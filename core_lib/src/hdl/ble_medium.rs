//! BLE receive medium (Linux-only, `experimental` feature).
//!
//! Advertises this machine as a Nearby / Quick Share endpoint over BLE and, for
//! every accepted L2CAP CoC connection, bridges the Nearby data tier into
//! rquickshare's real [`InboundRequest`](crate::hdl::InboundRequest) state
//! machine over an in-memory [`tokio::io::duplex`].

use std::collections::BTreeMap;
use std::time::Duration;

use bluer::adv::{Advertisement, Type};
use bluer::gatt::local::{
    Application, Characteristic, CharacteristicRead, CharacteristicReadRequest, Service,
};
use bluer::l2cap::{
    SocketAddr as L2capSocketAddr, Stream as L2capStream, StreamListener, PSM_LE_DYN_START,
    PSM_LE_MAX,
};
use bluer::{Address, AddressType, UuidExt};
use futures::FutureExt;
use rand::Rng;
use sha2::{Digest, Sha256};
use tokio::io::{AsyncReadExt, AsyncWrite, AsyncWriteExt};
use tokio::sync::broadcast;
use tokio::sync::mpsc::UnboundedSender;
use tokio_util::sync::CancellationToken;
use uuid::Uuid;

use crate::channel::{ChannelDirection, ChannelMessage};
use crate::errors::AppError;
use crate::hdl::{InboundRequest, State};

const INNER_NAME: &str = "BleServer";

/// Nearby Connections service id string, hashed to get the 3-byte service id
/// hash embedded in both inner and outer (regular-mode) advertisements.
const SERVICE_ID_STR: &str = "NearbySharing";

/// `kMaxFastEndpointInfoLength` from Nearby Connections client_proxy.cc.
const FAST_MAX_ENDPOINT_INFO_LEN: usize = 17;

/// `kMaxFastAdvertisementLength` from Nearby Connections ble_advertisement.cc
/// (1 byte0 + 1 data_size + 23-byte inner + 2-byte token, for the worked
/// fast-mode example).
const FAST_MAX_ADVERTISEMENT_LEN: usize = 27;

/// Legacy 0xFE2C "attention beacon" service data (mirrors `blea.rs::SERVICE_DATA`,
/// which is not `pub`). Included in case Android's scanner wants to see it before
/// it will surface a Nearby-style device in the picker.
const LEGACY_FE2C_SERVICE_DATA: [u8; 24] = [
    252, 18, 142, 1, 66, 0, 0, 0, 0, 0, 0, 0, 0, 0, 191, 45, 91, 160, 225, 216, 117, 36, 202, 0,
];

/// DeviceType packing matches `crate::utils::gen_mdns_endpoint_info`
/// (Laptop = 3, packed as `device_type << 1`).
const DEVICE_TYPE_LAPTOP: u8 = 3;
const DEVICE_NAME: &str = "RQS-Linux";

/// `BleAdvertisementHeader` size: 1 byte0 + 10-byte bloom filter + 4-byte
/// advertisement hash + 2-byte PSM.
const BLE_ADVERTISEMENT_HEADER_LEN: usize = 17;

/// header byte0 = `(VERSION<<5)&0xE0 | (EXT_ADV<<4)&0x10 | (NUM_SLOTS)&0x0F`.
/// VERSION=2 (kV2, required), EXT_ADV=0, NUM_SLOTS=1 (one GATT slot) => 0x41.
const HEADER_BYTE0: u8 = 0x41;

/// LE L2CAP dynamic PSM fallback scan range (used only if kernel-assigned
/// PSM 0 doesn't work).
const L2CAP_PSM_FALLBACK_RANGE: std::ops::RangeInclusive<u16> = PSM_LE_DYN_START..=PSM_LE_MAX;

/// Sanity cap on the 4-byte BE length prefix of every L2CAP frame, so a framing
/// desync can't make us `read_exact` gigabytes of garbage.
const MAX_FRAME_LEN: u32 = 512 * 1024;

/// `SocketControlFrame.type` values (proto2 enum `ControlFrameType`).
const CONTROL_TYPE_INTRODUCTION: u64 = 1;
const CONTROL_TYPE_DISCONNECTION: u64 = 2;
const CONTROL_TYPE_PACKET_ACKNOWLEDGEMENT: u64 = 3;

/// `BleL2capPacket` opcodes (command tier).
const OPCODE_REQUEST_ADVERTISEMENT: u8 = 0x01;
const OPCODE_REQUEST_ADVERTISEMENT_FINISH: u8 = 0x02;
const OPCODE_REQUEST_DATA_CONNECTION: u8 = 0x03;
const OPCODE_RESPONSE_ADVERTISEMENT: u8 = 0x15;
const OPCODE_RESPONSE_SERVICE_ID_NOT_FOUND: u8 = 0x16;
const OPCODE_RESPONSE_DATA_CONNECTION_READY: u8 = 0x17;
const OPCODE_RESPONSE_DATA_CONNECTION_FAILURE: u8 = 0x18;

/// `service_id_hash` = SHA-256("NearbySharing")[0:3]. Must equal `FC 9F 5E`.
fn service_id_hash() -> [u8; 3] {
    let digest = Sha256::digest(SERVICE_ID_STR.as_bytes());
    [digest[0], digest[1], digest[2]]
}

/// Inner "endpoint" BleAdvertisement
/// (connections/implementation/ble_advertisement.cc).
///
/// Fast:    `[byte0][ENDPOINT_ID 4B][INFO_LEN 1B][ENDPOINT_INFO N]`
/// Regular: `[byte0][SERVICE_ID_HASH 3B][ENDPOINT_ID 4B][INFO_LEN 1B]`
///          `[ENDPOINT_INFO N][BLUETOOTH_MAC 6B][UWB_LEN 1B][EXTRA 1B]`
fn inner_advertisement(endpoint_id: [u8; 4], endpoint_info: &[u8], fast: bool) -> Vec<u8> {
    // byte0 = (VERSION<<5)&0xE0 | (PCP&0x1F). VERSION=1, PCP=3 (P2P_POINT_TO_POINT) => 0x23.
    let byte0: u8 = ((1u8 << 5) & 0xE0) | (3u8 & 0x1F);

    let mut out = Vec::with_capacity(1 + 3 + 4 + 1 + endpoint_info.len() + 6 + 1 + 1);
    out.push(byte0);

    if !fast {
        out.extend_from_slice(&service_id_hash());
    }

    out.extend_from_slice(&endpoint_id);
    out.push(endpoint_info.len() as u8);
    out.extend_from_slice(endpoint_info);

    if !fast {
        out.extend_from_slice(&[0u8; 6]); // bluetooth_mac (unset => zeros)
        out.push(0u8); // uwb length (none)
        out.push(0u8); // extra: bit0 = webrtc, unset
    }

    out
}

/// Outer "medium" BleAdvertisement
/// (connections/implementation/mediums/ble/ble_advertisement.cc).
///
/// Fast:    `[byte0][DATA_SIZE 1B][DATA][DEVICE_TOKEN 2B]`
/// Regular: `[byte0][SERVICE_ID_HASH 3B][DATA_SIZE 4B BE][DATA][DEVICE_TOKEN 2B]`
fn outer_advertisement(inner: &[u8], fast: bool, device_token: [u8; 2]) -> Vec<u8> {
    // byte0 = (VER<<5)&0xE0 | (SOCKET_VER<<2)&0x1C | (FAST<<1)&0x02 | second&0x01.
    // Production VER=2, SOCKET_VER=2, second=0 => fast=0x4A, regular=0x48.
    let fast_bit: u8 = if fast { 1 } else { 0 };
    let byte0: u8 = ((2u8 << 5) & 0xE0) | ((2u8 << 2) & 0x1C) | ((fast_bit << 1) & 0x02);

    let mut out = Vec::with_capacity(1 + 3 + 4 + inner.len() + 2);
    out.push(byte0);

    if fast {
        out.push(inner.len() as u8);
    } else {
        out.extend_from_slice(&service_id_hash());
        out.extend_from_slice(&(inner.len() as u32).to_be_bytes());
    }

    out.extend_from_slice(inner);
    out.extend_from_slice(&device_token);

    out
}

/// `DEVICE_TOKEN` = SHA-256(decimal-ASCII of a random u32)[0:2].
fn gen_device_token() -> [u8; 2] {
    let n: u32 = rand::rng().random();
    let digest = Sha256::digest(n.to_string().as_bytes());
    [digest[0], digest[1]]
}

/// 4 ASCII chars from the endpoint id charset used by client_proxy.cc
/// (uppercase letters + digits). Kept as a helper for callers that want the
/// `BleServer` to self-generate an endpoint id; `BleServer::new` currently takes
/// the id from the shared RQS endpoint id instead.
#[allow(dead_code)]
fn gen_endpoint_id() -> [u8; 4] {
    const CHARSET: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
    let mut rng = rand::rng();
    let mut id = [0u8; 4];
    for slot in id.iter_mut() {
        *slot = CHARSET[rng.random_range(0..CHARSET.len())];
    }
    id
}

/// endpoint_info payload: same packing as `crate::utils::gen_mdns_endpoint_info`
/// (`[deviceType<<1][16 random salt bytes][name_len][name]`), returned as raw
/// bytes (BLE, not base64/mDNS-TXT).
fn build_endpoint_info(device_type: u8, name: &str) -> Vec<u8> {
    let mut info = Vec::new();
    info.push(device_type << 1);

    let salt: [u8; 16] = rand::rng().random();
    info.extend_from_slice(&salt);

    let name_bytes = name.as_bytes();
    info.push(name_bytes.len() as u8);
    info.extend_from_slice(name_bytes);

    info
}

/// `advertisement_hash` (4B) of the `BleAdvertisementHeader`. Production is a
/// rolling SHA-256 chain truncated to 4 bytes; we take SHA-256(full outer
/// advertisement bytes)[0..4] — fine since this field is only used for
/// change-detection, not gating.
fn advertisement_hash(full_advert_bytes: &[u8]) -> [u8; 4] {
    let digest = Sha256::digest(full_advert_bytes);
    [digest[0], digest[1], digest[2], digest[3]]
}

/// `BleAdvertisementHeader`, goes in the 0xFEF3 service data.
///
/// `[byte0][bloom_filter 10B][advertisement_hash 4B][psm 2B BE]` (17 bytes).
/// bloom_filter is a SHORTCUT: proper encoding is a MurmurHash3_x64_128 5-hash
/// bloom filter over the service id; we use 10 bytes of 0xFF (all bits set) so
/// `PossiblyContains` is always true and the phone never skips us on
/// bloom-filter grounds. False positives are harmless here.
fn ble_advertisement_header(
    advertisement_hash: [u8; 4],
    psm: u16,
) -> [u8; BLE_ADVERTISEMENT_HEADER_LEN] {
    let mut out = [0u8; BLE_ADVERTISEMENT_HEADER_LEN];
    out[0] = HEADER_BYTE0;
    out[1..11].copy_from_slice(&[0xFFu8; 10]); // bloom filter (shortcut)
    out[11..15].copy_from_slice(&advertisement_hash);
    out[15..17].copy_from_slice(&psm.to_be_bytes());
    out
}

/// Prepends the uniform `[4-byte BIG-ENDIAN length][payload]` framing used on
/// every read/write on the L2CAP CoC.
fn frame(payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(4 + payload.len());
    out.extend_from_slice(&(payload.len() as u32).to_be_bytes());
    out.extend_from_slice(payload);
    out
}

/// Parsed `BleL2capPacket` command-tier message (opcode = `payload[0]`).
/// `Unknown` covers any opcode we don't otherwise recognize — logged and
/// skipped rather than treated as an error.
#[derive(Debug, Clone, PartialEq, Eq)]
enum L2capCommand {
    RequestAdvertisement { hash: [u8; 3] },
    RequestAdvertisementFinish,
    RequestDataConnection,
    ResponseAdvertisement { advertisement: Vec<u8> },
    ResponseServiceIdNotFound,
    ResponseDataConnectionReady,
    ResponseDataConnectionFailure,
    Unknown { opcode: u8 },
}

/// Parses a `BleL2capPacket` command payload (i.e. the payload of a
/// `[4B len][payload]` frame that is neither a `000000`-prefixed BlePacket
/// control frame nor an `fc9f5e`-prefixed BlePacket data frame).
fn parse_l2cap_command(payload: &[u8]) -> Option<L2capCommand> {
    let opcode = *payload.first()?;
    match opcode {
        OPCODE_REQUEST_ADVERTISEMENT => {
            // `01 [len 2B BE][service_id_hash 3B]`.
            if payload.len() < 6 {
                return None;
            }
            let hash = [payload[3], payload[4], payload[5]];
            Some(L2capCommand::RequestAdvertisement { hash })
        }
        OPCODE_REQUEST_ADVERTISEMENT_FINISH => Some(L2capCommand::RequestAdvertisementFinish),
        OPCODE_REQUEST_DATA_CONNECTION => Some(L2capCommand::RequestDataConnection),
        OPCODE_RESPONSE_ADVERTISEMENT => {
            // `15 [len 2B BE][advertisement bytes]`.
            if payload.len() < 3 {
                return None;
            }
            let len = u16::from_be_bytes([payload[1], payload[2]]) as usize;
            let advertisement = payload.get(3..3 + len)?.to_vec();
            Some(L2capCommand::ResponseAdvertisement { advertisement })
        }
        OPCODE_RESPONSE_SERVICE_ID_NOT_FOUND => Some(L2capCommand::ResponseServiceIdNotFound),
        OPCODE_RESPONSE_DATA_CONNECTION_READY => Some(L2capCommand::ResponseDataConnectionReady),
        OPCODE_RESPONSE_DATA_CONNECTION_FAILURE => Some(L2capCommand::ResponseDataConnectionFailure),
        opcode => Some(L2capCommand::Unknown { opcode }),
    }
}

/// Encodes a protobuf varint (LEB128, 7 bits/byte + continuation bit).
fn encode_varint(mut value: u64, out: &mut Vec<u8>) {
    loop {
        let byte = (value & 0x7F) as u8;
        value >>= 7;
        if value != 0 {
            out.push(byte | 0x80);
        } else {
            out.push(byte);
            break;
        }
    }
}

/// Decodes a protobuf varint starting at `*pos`, advancing `*pos` past it.
fn decode_varint(data: &[u8], pos: &mut usize) -> Option<u64> {
    let mut result: u64 = 0;
    let mut shift = 0u32;
    loop {
        let byte = *data.get(*pos)?;
        *pos += 1;
        result |= ((byte & 0x7F) as u64) << shift;
        if byte & 0x80 == 0 {
            return Some(result);
        }
        shift += 7;
        if shift >= 64 {
            return None; // malformed / absurdly long varint
        }
    }
}

fn encode_tag(field_number: u32, wire_type: u8, out: &mut Vec<u8>) {
    encode_varint(((field_number as u64) << 3) | (wire_type as u64), out);
}

fn encode_bytes_field(field_number: u32, data: &[u8], out: &mut Vec<u8>) {
    encode_tag(field_number, 2, out);
    encode_varint(data.len() as u64, out);
    out.extend_from_slice(data);
}

fn encode_varint_field(field_number: u32, value: u64, out: &mut Vec<u8>) {
    encode_tag(field_number, 0, out);
    encode_varint(value, out);
}

/// Hand-encodes a `SocketControlFrame{ type = PACKET_ACKNOWLEDGEMENT,
/// packet_acknowledgement { service_id_hash, received_size } }`, wrapped in the
/// `000000` BlePacket-control prefix (but NOT the outer `[4B len]` framing —
/// callers pass the result through `frame()` before writing it).
/// Wire shape: `[00 00 00] 08 03 22 <L> 0A 03 <hash> 10 <received_size varint>`.
fn build_packet_ack(service_id_hash: [u8; 3], received_size: i32) -> Vec<u8> {
    let mut inner = Vec::new();
    encode_bytes_field(1, &service_id_hash, &mut inner); // PacketAcknowledgementFrame.service_id_hash
    encode_varint_field(2, received_size as u64, &mut inner); // PacketAcknowledgementFrame.received_size

    let mut scf = Vec::new();
    encode_varint_field(1, CONTROL_TYPE_PACKET_ACKNOWLEDGEMENT, &mut scf); // SocketControlFrame.type
    encode_bytes_field(4, &inner, &mut scf); // SocketControlFrame.packet_acknowledgement

    let mut out = Vec::with_capacity(3 + scf.len());
    out.extend_from_slice(&[0x00, 0x00, 0x00]);
    out.extend_from_slice(&scf);
    out
}

/// Minimal parse of a `SocketControlFrame` (the payload after the `000000`
/// BlePacket-control prefix has been stripped). Extracts `type` (field 1), plus
/// best-effort `service_id_hash` and either `socket_version` (INTRODUCTION) or
/// `received_size` (PACKET_ACKNOWLEDGEMENT).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ParsedSocketControlFrame {
    frame_type: Option<u64>,
    service_id_hash: Option<Vec<u8>>,
    socket_version: Option<u64>,
    received_size: Option<u64>,
}

/// Shared shape of `IntroductionFrame` / `PacketAcknowledgementFrame` (both
/// `{ optional bytes service_id_hash = 1; optional <varint> = 2; }`).
fn parse_hash_and_optional_varint(sub: &[u8]) -> (Option<Vec<u8>>, Option<u64>) {
    let mut hash = None;
    let mut second = None;
    let mut pos = 0usize;
    while pos < sub.len() {
        let Some(tag) = decode_varint(sub, &mut pos) else {
            break;
        };
        let field_number = tag >> 3;
        let wire_type = tag & 0x7;
        match wire_type {
            0 => {
                let Some(value) = decode_varint(sub, &mut pos) else {
                    break;
                };
                if field_number == 2 {
                    second = Some(value);
                }
            }
            2 => {
                let Some(len) = decode_varint(sub, &mut pos) else {
                    break;
                };
                let len = len as usize;
                // `len` is a peer-controlled varint — guard against usize overflow.
                if len > sub.len().saturating_sub(pos) {
                    break;
                }
                let data = &sub[pos..pos + len];
                pos += len;
                if field_number == 1 {
                    hash = Some(data.to_vec());
                }
            }
            _ => break, // 64-bit/32-bit wire types unused by these messages
        }
    }
    (hash, second)
}

fn parse_socket_control_frame(bytes: &[u8]) -> ParsedSocketControlFrame {
    let mut out = ParsedSocketControlFrame::default();
    let mut pos = 0usize;
    while pos < bytes.len() {
        let Some(tag) = decode_varint(bytes, &mut pos) else {
            break;
        };
        let field_number = tag >> 3;
        let wire_type = tag & 0x7;
        match wire_type {
            0 => {
                let Some(value) = decode_varint(bytes, &mut pos) else {
                    break;
                };
                if field_number == 1 {
                    out.frame_type = Some(value);
                }
            }
            2 => {
                let Some(len) = decode_varint(bytes, &mut pos) else {
                    break;
                };
                let len = len as usize;
                // `len` is a peer-controlled varint — guard against usize overflow.
                if len > bytes.len().saturating_sub(pos) {
                    break;
                }
                let sub = &bytes[pos..pos + len];
                pos += len;

                match field_number {
                    2 => {
                        // IntroductionFrame { service_id_hash=1, socket_version=2 }
                        let (hash, version) = parse_hash_and_optional_varint(sub);
                        out.service_id_hash = hash;
                        out.socket_version = version;
                    }
                    3 => {
                        // DisconnectionFrame — shape unconfirmed; best-effort hash only.
                        let (hash, _) = parse_hash_and_optional_varint(sub);
                        out.service_id_hash = hash;
                    }
                    4 => {
                        // PacketAcknowledgementFrame { service_id_hash=1, received_size=2 }
                        let (hash, size) = parse_hash_and_optional_varint(sub);
                        out.service_id_hash = hash;
                        out.received_size = size;
                    }
                    _ => {} // unknown nested field: ignore contents, keep scanning siblings
                }
            }
            _ => break, // 64-bit/32-bit wire types unused by SocketControlFrame
        }
    }
    out
}

fn control_frame_type_name(frame_type: Option<u64>) -> &'static str {
    match frame_type {
        Some(CONTROL_TYPE_INTRODUCTION) => "INTRODUCTION",
        Some(CONTROL_TYPE_DISCONNECTION) => "DISCONNECTION",
        Some(CONTROL_TYPE_PACKET_ACKNOWLEDGEMENT) => "PACKET_ACKNOWLEDGEMENT",
        Some(_) => "UNKNOWN",
        None => "MISSING",
    }
}

/// Opens an LE L2CAP CoC listener for the given adapter address/address type.
/// Tries PSM 0 first so the kernel assigns a dynamic PSM; if that fails (or
/// reports back PSM 0), falls back to explicitly trying PSMs in the LE dynamic
/// range (`0x0080..=0x00FF`) until one binds.
///
/// Returns the bound listener and the PSM it ended up on (to be embedded,
/// big-endian, in the advertised `BleAdvertisementHeader`).
async fn open_l2cap_listener(
    adapter_addr: Address,
    addr_type: AddressType,
) -> anyhow::Result<(StreamListener, u16)> {
    let auto_sa = L2capSocketAddr::new(adapter_addr, addr_type, 0);
    match StreamListener::bind(auto_sa).await {
        Ok(listener) => {
            let psm = listener.as_ref().local_addr()?.psm;
            if psm != 0 {
                info!("{INNER_NAME}: kernel-assigned dynamic PSM=0x{psm:04X} ({psm})");
                return Ok((listener, psm));
            }
            warn!(
                "{INNER_NAME}: bind(psm=0) succeeded but local_addr().psm reported back as 0; \
                 falling back to explicit PSM scan over {L2CAP_PSM_FALLBACK_RANGE:?}"
            );
        }
        Err(e) => {
            warn!(
                "{INNER_NAME}: bind(psm=0) failed ({e}); falling back to explicit PSM scan over \
                 {L2CAP_PSM_FALLBACK_RANGE:?}"
            );
        }
    }

    for psm in L2CAP_PSM_FALLBACK_RANGE {
        let sa = L2capSocketAddr::new(adapter_addr, addr_type, psm);
        match StreamListener::bind(sa).await {
            Ok(listener) => {
                info!("{INNER_NAME}: bound explicit dynamic PSM=0x{psm:04X}");
                return Ok((listener, psm));
            }
            Err(e) => {
                trace!("{INNER_NAME}: PSM=0x{psm:04X} bind failed: {e}");
            }
        }
    }

    anyhow::bail!(
        "{INNER_NAME}: exhausted PSM range {L2CAP_PSM_FALLBACK_RANGE:?} without a successful bind \
         (kernel-assigned PSM 0 also failed) — cannot open the L2CAP CoC listener"
    );
}

/// Wraps an `InboundRequest`-produced `[4B BE len][OfflineFrame]` frame (exactly
/// the bytes `send_frame` writes) as an outbound BlePacket data frame ready for
/// the L2CAP CoC: `frame( [fc9f5e] ++ [4B len][OfflineFrame] )`.
fn wrap_inbound_frame_as_ble_data(our_service_id_hash: [u8; 3], inbound_framed: &[u8]) -> Vec<u8> {
    let mut payload = Vec::with_capacity(3 + inbound_framed.len());
    payload.extend_from_slice(&our_service_id_hash);
    payload.extend_from_slice(inbound_framed);
    frame(&payload)
}

/// Inverse of the inbound direction: given a BlePacket DATA payload
/// `[fc9f5e][4B len][OfflineFrame]` (after the outer length has been stripped),
/// returns the inner `[4B len][OfflineFrame]` slice iff it carries our
/// service-id hash — exactly what `InboundRequest` expects to read off its socket.
fn unwrap_ble_data_payload(payload: &[u8], our_service_id_hash: [u8; 3]) -> Option<&[u8]> {
    if payload.len() >= 3 && payload[0..3] == our_service_id_hash {
        Some(&payload[3..])
    } else {
        None
    }
}

/// Handles a `000000`-prefixed BlePacket control frame: parses it as a
/// `SocketControlFrame` and logs type + embedded service_id_hash +
/// socket_version. We never reply to a control frame (Nearby's INTRODUCTION is
/// implicit for the acceptor). Returns `true` when the peer asked to close
/// (DISCONNECTION), so the caller tears the bridge down.
fn handle_control_frame(control_bytes: &[u8], peer: &L2capSocketAddr) -> bool {
    let parsed = parse_socket_control_frame(control_bytes);
    let type_name = control_frame_type_name(parsed.frame_type);

    debug!(
        "{INNER_NAME}: peer={peer:?} CONTROL type={type_name} (raw={:?}) service_id_hash={} \
         socket_version={:?} received_size={:?}",
        parsed.frame_type,
        parsed
            .service_id_hash
            .as_deref()
            .map(hex::encode)
            .unwrap_or_else(|| "<none>".to_string()),
        parsed.socket_version,
        parsed.received_size,
    );

    if parsed.frame_type == Some(CONTROL_TYPE_DISCONNECTION) {
        info!("{INNER_NAME}: peer={peer:?} DISCONNECTION control frame — closing bridge");
        return true;
    }
    false
}

/// Bridges an `fc9f5e`-prefixed BlePacket data frame INTO `InboundRequest`.
/// `bytes_after_hash` is `[4B BE inner_len][OfflineFrame]` — i.e. exactly the
/// `[4B len][frame]` framing `InboundRequest` reads off a TCP socket — so we
/// write it verbatim into the duplex and let the state machine parse it. Then
/// queue a PACKET_ACKNOWLEDGEMENT (received_size = inner_len) back onto the CoC.
async fn forward_data_frame_to_inbound<W>(
    ble_write: &mut W,
    l2c_tx: &UnboundedSender<Vec<u8>>,
    bytes_after_hash: &[u8],
    our_service_id_hash: [u8; 3],
    peer: &L2capSocketAddr,
) -> std::io::Result<()>
where
    W: AsyncWrite + Unpin,
{
    if bytes_after_hash.len() < 4 {
        warn!(
            "{INNER_NAME}: peer={peer:?} BlePacket DATA frame too short for inner-length prefix: {}",
            hex::encode(bytes_after_hash)
        );
        return Ok(());
    }

    let inner_len = u32::from_be_bytes([
        bytes_after_hash[0],
        bytes_after_hash[1],
        bytes_after_hash[2],
        bytes_after_hash[3],
    ]);

    // Feed [4B inner_len][OfflineFrame] straight into the duplex; InboundRequest
    // reads it byte-for-byte the way it reads a TCP frame.
    ble_write.write_all(bytes_after_hash).await?;
    ble_write.flush().await?;
    debug!(
        "{INNER_NAME}: peer={peer:?} forwarded {inner_len}-byte OfflineFrame into InboundRequest \
         ({} bytes on the duplex); queueing PACKET_ACKNOWLEDGEMENT",
        bytes_after_hash.len()
    );

    let ack_framed = frame(&build_packet_ack(our_service_id_hash, inner_len as i32));
    if l2c_tx.send(ack_framed).is_err() {
        warn!("{INNER_NAME}: peer={peer:?} failed queueing PACKET_ACKNOWLEDGEMENT (writer task gone)");
    }

    Ok(())
}

/// Handles a `BleL2capPacket` command-tier frame (opcode = `payload[0]`), the
/// pre-data-connection tier. Answers RequestAdvertisement / RequestDataConnection
/// by queueing the framed reply on the single-writer channel (`l2c_tx`).
/// `our_advertisement` is the same outer BleAdvertisement bytes served on the
/// GATT slot-0 characteristic, reused verbatim for ResponseAdvertisement.
fn handle_command_frame(
    l2c_tx: &UnboundedSender<Vec<u8>>,
    payload: &[u8],
    our_advertisement: &[u8],
    peer: &L2capSocketAddr,
) {
    match parse_l2cap_command(payload) {
        Some(L2capCommand::RequestAdvertisement { hash }) => {
            info!(
                "{INNER_NAME}: peer={peer:?} RequestAdvertisement requested_hash={} (ours={}) — \
                 replying ResponseAdvertisement with our {}-byte endpoint advertisement",
                hex::encode(hash),
                hex::encode(service_id_hash()),
                our_advertisement.len()
            );

            let mut resp_payload = Vec::with_capacity(3 + our_advertisement.len());
            resp_payload.push(OPCODE_RESPONSE_ADVERTISEMENT);
            resp_payload.extend_from_slice(&(our_advertisement.len() as u16).to_be_bytes());
            resp_payload.extend_from_slice(our_advertisement);

            if l2c_tx.send(frame(&resp_payload)).is_err() {
                warn!("{INNER_NAME}: peer={peer:?} failed queueing ResponseAdvertisement (writer task gone)");
            }
        }
        Some(L2capCommand::RequestAdvertisementFinish) => {
            debug!("{INNER_NAME}: peer={peer:?} RequestAdvertisementFinish (opcode 0x02) — logging only");
        }
        Some(L2capCommand::RequestDataConnection) => {
            info!("{INNER_NAME}: peer={peer:?} RequestDataConnection — replying ResponseDataConnectionReady (0x17)");

            if l2c_tx.send(frame(&[OPCODE_RESPONSE_DATA_CONNECTION_READY])).is_err() {
                warn!("{INNER_NAME}: peer={peer:?} failed queueing ResponseDataConnectionReady (writer task gone)");
            }
        }
        Some(other) => {
            debug!("{INNER_NAME}: peer={peer:?} received response/other-tier command {other:?} — logging only");
        }
        None => {
            warn!(
                "{INNER_NAME}: peer={peer:?} unrecognized or too-short BleL2capPacket command payload={}",
                hex::encode(payload)
            );
        }
    }
}

/// Handles one accepted L2CAP CoC connection by BRIDGING its BlePacket data tier
/// into a real [`InboundRequest`](crate::hdl::InboundRequest). The L2CAP stream
/// is split so the two directions never contend, and every write back onto the
/// CoC is serialised through one mpsc-fed writer task. Four `'static` tasks:
///
/// * **writer** owns the CoC write half, draining `l2c_tx`.
/// * **L2CAP -> inbound** reads `[4B len][payload]` frames and dispatches:
///   `000000` control (log; close on DISCONNECTION), `fc9f5e` data (feed the
///   inner `[4B len][OfflineFrame]` into the duplex for `InboundRequest`, then
///   queue a PACKET_ACKNOWLEDGEMENT), else BleL2capPacket command (answer
///   RequestAdvertisement / RequestDataConnection).
/// * **inbound -> L2CAP** reads each `[4B len][OfflineFrame]` `InboundRequest`
///   emits on the duplex and queues it wrapped as an `fc9f5e` data frame.
/// * **InboundRequest driver** runs the `handle()` loop (mirrors `manager.rs`,
///   feeding the SHARED RQS `sender` so the app shows consent UI — NO auto-accept).
///
/// The handler returns when the L2CAP reader ends (EOF / DISCONNECTION / error)
/// or when `ctk` is cancelled, tearing the remaining tasks down.
async fn handle_l2cap_connection(
    stream: L2capStream,
    peer: L2capSocketAddr,
    our_advertisement: Vec<u8>,
    sender: broadcast::Sender<ChannelMessage>,
    ctk: CancellationToken,
) {
    info!("{INNER_NAME}: accepted connection, peer={peer:?}");

    if let Ok(mtu) = stream.as_ref().recv_mtu() {
        debug!("{INNER_NAME}: peer={peer:?} recv_mtu={mtu}");
    }

    let our_service_id_hash = service_id_hash();
    // Stable unique id; InboundRequest routes consent Accept/Reject back by it.
    let peer_id = peer.addr.to_string();

    // Split the CoC into independent read/write halves so each bridge direction
    // can block on its own read_exact without select-cancellation hazards.
    let (mut l2cap_read, mut l2cap_write) = tokio::io::split(stream);

    // Single-writer channel: command responses, PACKET_ACKs and wrapped inbound
    // OfflineFrames are all serialised through this so writes never interleave.
    let (l2c_tx, mut l2c_rx) = tokio::sync::mpsc::unbounded_channel::<Vec<u8>>();

    // Duplex bridging the L2CAP data tier to InboundRequest: bytes written into
    // `ble_write` are read by InboundRequest (like inbound TCP bytes), and what
    // InboundRequest writes comes back out of `ble_read`.
    let (ble_end, inbound_end) = tokio::io::duplex(64 * 1024);
    let (mut ble_read, mut ble_write) = tokio::io::split(ble_end);

    let writer_task = tokio::spawn(async move {
        while let Some(bytes) = l2c_rx.recv().await {
            trace!("{INNER_NAME} TX peer={peer:?} {} bytes: {}", bytes.len(), hex::encode(&bytes));
            if let Err(e) = l2cap_write.write_all(&bytes).await {
                warn!("{INNER_NAME}: peer={peer:?} write error: {e}");
                break;
            }
            if let Err(e) = l2cap_write.flush().await {
                warn!("{INNER_NAME}: peer={peer:?} flush error: {e}");
                break;
            }
        }
        debug!("{INNER_NAME}: peer={peer:?} writer task exiting");
    });

    let inbound_to_l2cap = {
        let l2c_tx = l2c_tx.clone();
        tokio::spawn(async move {
            loop {
                let mut len_buf = [0u8; 4];
                if let Err(e) = ble_read.read_exact(&mut len_buf).await {
                    debug!("{INNER_NAME} inbound->L2CAP: peer={peer:?} duplex closed/EOF reading length: {e}");
                    break;
                }
                let m = u32::from_be_bytes(len_buf);
                if m > MAX_FRAME_LEN {
                    warn!("{INNER_NAME} inbound->L2CAP: peer={peer:?} frame len {m} exceeds cap {MAX_FRAME_LEN}; closing");
                    break;
                }

                // Reassemble the exact [4B len][OfflineFrame] InboundRequest wrote.
                let mut inbound_framed = Vec::with_capacity(4 + m as usize);
                inbound_framed.extend_from_slice(&len_buf);
                let mut frame_body = vec![0u8; m as usize];
                if let Err(e) = ble_read.read_exact(&mut frame_body).await {
                    debug!("{INNER_NAME} inbound->L2CAP: peer={peer:?} EOF reading {m}-byte OfflineFrame: {e}");
                    break;
                }
                inbound_framed.extend_from_slice(&frame_body);

                let wire = wrap_inbound_frame_as_ble_data(our_service_id_hash, &inbound_framed);
                trace!(
                    "{INNER_NAME} inbound->L2CAP: peer={peer:?} wrapping {m}-byte OfflineFrame -> {} wire bytes",
                    wire.len(),
                );
                if l2c_tx.send(wire).is_err() {
                    debug!("{INNER_NAME} inbound->L2CAP: peer={peer:?} writer task gone, exiting");
                    break;
                }
            }
            debug!("{INNER_NAME} inbound->L2CAP task exiting (peer={peer:?})");
        })
    };

    let mut l2cap_to_inbound = {
        let l2c_tx = l2c_tx.clone();
        let our_advertisement = our_advertisement.clone();
        tokio::spawn(async move {
            loop {
                let mut len_buf = [0u8; 4];
                match l2cap_read.read_exact(&mut len_buf).await {
                    Ok(_) => {}
                    Err(e) if e.kind() == std::io::ErrorKind::UnexpectedEof => {
                        info!("{INNER_NAME}: peer={peer:?} connection ended (EOF reading length prefix)");
                        break;
                    }
                    Err(e) => {
                        info!("{INNER_NAME}: peer={peer:?} read error on length prefix: {e}");
                        break;
                    }
                }
                let n = u32::from_be_bytes(len_buf);

                if n > MAX_FRAME_LEN {
                    warn!(
                        "{INNER_NAME}: peer={peer:?} frame length N={n} exceeds sanity cap \
                         {MAX_FRAME_LEN}; len_bytes_hex={} — bailing this connection (framing desync?)",
                        hex::encode(len_buf)
                    );
                    break;
                }

                let mut payload = vec![0u8; n as usize];
                if let Err(e) = l2cap_read.read_exact(&mut payload).await {
                    info!("{INNER_NAME}: peer={peer:?} read error/EOF reading {n}-byte payload: {e}");
                    break;
                }

                trace!("{INNER_NAME} RX peer={peer:?} n={n} payload={}", hex::encode(&payload));

                if payload.len() >= 3 && payload[0..3] == [0x00, 0x00, 0x00] {
                    if handle_control_frame(&payload[3..], &peer) {
                        break;
                    }
                } else if let Some(after) = unwrap_ble_data_payload(&payload, our_service_id_hash) {
                    if let Err(e) = forward_data_frame_to_inbound(
                        &mut ble_write,
                        &l2c_tx,
                        after,
                        our_service_id_hash,
                        &peer,
                    )
                    .await
                    {
                        warn!("{INNER_NAME}: peer={peer:?} error forwarding BlePacket DATA into InboundRequest: {e}");
                        break;
                    }
                } else {
                    handle_command_frame(&l2c_tx, &payload, &our_advertisement, &peer);
                }
            }
            debug!("{INNER_NAME} L2CAP->inbound task exiting (peer={peer:?})");
        })
    };

    let mut ir_task = {
        let ir_id = peer_id.clone();
        let ir_sender = sender.clone();
        let esender = sender.clone();
        tokio::spawn(async move {
            let mut ir = InboundRequest::new(Box::new(inbound_end), ir_id.clone(), ir_sender);
            debug!("{INNER_NAME}: InboundRequest[{ir_id}] driver starting");
            loop {
                match ir.handle().await {
                    Ok(_) => {}
                    Err(e) => match e.downcast_ref() {
                        Some(AppError::NotAnError) => break,
                        None => {
                            if ir.state.state == State::Initial {
                                break;
                            }

                            if ir.state.state != State::Finished {
                                let _ = esender.send(ChannelMessage {
                                    id: ir_id.clone(),
                                    direction: ChannelDirection::LibToFront,
                                    state: Some(State::Disconnected),
                                    ..Default::default()
                                });
                            }
                            error!("{INNER_NAME}: error while handling client: {e} ({:?})", ir.state.state);
                            break;
                        }
                    },
                }
            }
            debug!("{INNER_NAME}: InboundRequest[{ir_id}] driver exiting");
        })
    };

    // The L2CAP reader is the connection lifecycle: when it ends (EOF /
    // DISCONNECTION / error) — or when the server is cancelled — tear down the
    // rest of the bridge.
    tokio::select! {
        _ = ctk.cancelled() => {
            info!("{INNER_NAME}: peer={peer:?} cancellation requested; tearing down bridge tasks");
        }
        _ = &mut l2cap_to_inbound => {
            info!("{INNER_NAME}: peer={peer:?} reader ended; tearing down bridge tasks");
        }
        _ = &mut ir_task => {
            info!("{INNER_NAME}: peer={peer:?} InboundRequest finished; tearing down bridge tasks");
        }
    }

    drop(l2c_tx); // let the writer observe channel-close as well
    writer_task.abort();
    inbound_to_l2cap.abort();
    l2cap_to_inbound.abort();
    ir_task.abort();
    info!("{INNER_NAME}: peer={peer:?} connection handler exiting");
}

/// A BLE receive medium: advertises this machine as a Nearby / Quick Share
/// endpoint and, for every accepted L2CAP connection, runs rquickshare's real
/// `InboundRequest` over the CoC — feeding the SHARED RQS message channel so the
/// app's existing consent flow (Accept/Reject) applies, exactly like `TcpServer`.
pub struct BleServer {
    endpoint_id: [u8; 4],
    sender: broadcast::Sender<ChannelMessage>,
}

impl BleServer {
    /// Cheap to construct; the bluer adapter is brought up in [`BleServer::run`].
    pub async fn new(
        endpoint_id: [u8; 4],
        sender: broadcast::Sender<ChannelMessage>,
    ) -> Result<Self, anyhow::Error> {
        Ok(Self { endpoint_id, sender })
    }

    /// Brings up the adapter, registers the GATT server (slot-0 char = outer
    /// endpoint advertisement), advertises the 0xFEF3 `BleAdvertisementHeader`
    /// (with the real PSM) + the 0xFE2C beacon, opens the L2CAP CoC listener, and
    /// runs the accept loop until `ctk` is cancelled.
    pub async fn run(self, ctk: CancellationToken) -> Result<(), anyhow::Error> {
        // ---- build the advertisement -------------------------------------
        let endpoint_info = build_endpoint_info(DEVICE_TYPE_LAPTOP, DEVICE_NAME);
        let fast = endpoint_info.len() <= FAST_MAX_ENDPOINT_INFO_LEN;

        let inner = inner_advertisement(self.endpoint_id, &endpoint_info, fast);
        let device_token = gen_device_token();
        let outer = outer_advertisement(&inner, fast, device_token);

        info!(
            "{INNER_NAME}: endpoint_id={:?} mode={} inner={}B outer={}B",
            std::str::from_utf8(&self.endpoint_id).unwrap_or("<non-ascii>"),
            if fast { "FAST" } else { "REGULAR" },
            inner.len(),
            outer.len(),
        );

        if outer.len() > FAST_MAX_ADVERTISEMENT_LEN {
            debug!(
                "{INNER_NAME}: outer advertisement is {} bytes, over the {}-byte fast budget; the \
                 legacy service-data copy is best-effort — the GATT slot-0 read serves the full bytes",
                outer.len(),
                FAST_MAX_ADVERTISEMENT_LEN
            );
        }

        // ---- bring up the adapter ----------------------------------------
        let session = bluer::Session::new().await?;
        let adapter = session.default_adapter().await?;
        adapter.set_powered(true).await?;

        let adapter_addr = adapter.address().await?;
        let adapter_addr_type = adapter.address_type().await?;
        info!(
            "{INNER_NAME}: adapter name={} address={} address_type={:?}",
            adapter.name(),
            adapter_addr,
            adapter_addr_type
        );

        // ---- open the LE L2CAP CoC listener (need the PSM before we can
        // ---- build the BleAdvertisementHeader below) ---------------------
        let (l2cap_listener, l2cap_psm) =
            open_l2cap_listener(adapter_addr, adapter_addr_type).await?;
        info!("{INNER_NAME}: L2CAP CoC listener bound, PSM=0x{l2cap_psm:04X} ({l2cap_psm})");

        // ---- build the BleAdvertisementHeader ----------------------------
        let adv_hash = advertisement_hash(&outer);
        let header = ble_advertisement_header(adv_hash, l2cap_psm);

        // ---- GATT server (register BEFORE advertising) -------------------
        let slot0_uuid = Uuid::parse_str("00000000-0000-3000-8000-000000000000")?;
        let outer_for_read = outer.clone();

        let service = Service {
            uuid: Uuid::from_u16(0xFEF3),
            primary: true,
            characteristics: vec![Characteristic {
                uuid: slot0_uuid,
                read: Some(CharacteristicRead {
                    read: true,
                    fun: Box::new(move |req: CharacteristicReadRequest| {
                        let value = outer_for_read.clone();
                        async move {
                            debug!(
                                "{INNER_NAME}: GATT READ slot0 device={} offset={} mtu={} -> {} bytes",
                                req.device_address,
                                req.offset,
                                req.mtu,
                                value.len()
                            );
                            Ok(value)
                        }
                        .boxed()
                    }),
                    ..Default::default()
                }),
                ..Default::default()
            }],
            ..Default::default()
        };

        let app = Application {
            services: vec![service],
            ..Default::default()
        };

        let app_handle = adapter.serve_gatt_application(app).await?;
        info!("{INNER_NAME}: GATT application registered (service 0xFEF3, slot0={slot0_uuid})");

        // ---- advertise ---------------------------------------------------
        let mut service_data: BTreeMap<Uuid, Vec<u8>> = BTreeMap::new();
        service_data.insert(Uuid::from_u16(0xFEF3), header.to_vec());
        service_data.insert(Uuid::from_u16(0xFE2C), LEGACY_FE2C_SERVICE_DATA.to_vec());

        let advertisement = Advertisement {
            advertisement_type: Type::Peripheral,
            discoverable: Some(true),
            local_name: Some("rqs".into()),
            service_uuids: [Uuid::from_u16(0xFEF3)].into(),
            service_data,
            ..Default::default()
        };

        let adv_handle = adapter.advertise(advertisement).await?;
        info!(
            "{INNER_NAME}: advertising STARTED (Peripheral, connectable) with PSM=0x{l2cap_psm:04X}; \
             waiting for connections"
        );

        // ---- accept loop -------------------------------------------------
        loop {
            tokio::select! {
                _ = ctk.cancelled() => {
                    info!("{INNER_NAME}: tracker cancelled, breaking accept loop");
                    break;
                }
                r = l2cap_listener.accept() => {
                    match r {
                        Ok((stream, peer)) => {
                            info!("{INNER_NAME}: accept() -> new connection from peer={peer:?}");
                            let sender = self.sender.clone();
                            let adv = outer.clone();
                            let cctk = ctk.clone();
                            tokio::spawn(handle_l2cap_connection(stream, peer, adv, sender, cctk));
                        }
                        Err(e) => {
                            error!("{INNER_NAME}: accept() failed: {e}; retrying in 500ms");
                            tokio::time::sleep(Duration::from_millis(500)).await;
                        }
                    }
                }
            }
        }

        // ---- teardown ----------------------------------------------------
        drop(adv_handle);
        drop(app_handle);
        drop(l2cap_listener);
        info!("{INNER_NAME}: advertisement + GATT app dropped, L2CAP listener closed, exiting");

        Ok(())
    }
}

// ===========================================================================
// Tests: byte-layout asserts against the worked examples in
// nearby-ble-encoding-ref.md / nearby-ble-gate2b-ref.md. Encoders are pure
// functions above; the test module re-derives the same worked vectors.
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn service_id_hash_matches_reference() {
        assert_eq!(service_id_hash(), [0xFC, 0x9F, 0x5E]);
    }

    #[test]
    fn inner_fast_matches_worked_example() {
        // id="ABCD", 17-byte info -> `23 41 42 43 44 11 <17 info bytes>` (23 bytes).
        let endpoint_id = *b"ABCD";
        let info: Vec<u8> = (0..17).collect();

        let inner = inner_advertisement(endpoint_id, &info, true);

        assert_eq!(inner.len(), 23);
        assert_eq!(&inner[0..6], &[0x23, 0x41, 0x42, 0x43, 0x44, 0x11]);
        assert_eq!(&inner[6..23], info.as_slice());
    }

    #[test]
    fn outer_fast_matches_worked_example() {
        // Wrapping the 23B fast inner from the example above:
        // `4A 17 <23 inner bytes> <2 token bytes>` (27 bytes = kMaxFastAdvertisementLength).
        let endpoint_id = *b"ABCD";
        let info: Vec<u8> = (0..17).collect();
        let inner = inner_advertisement(endpoint_id, &info, true);
        assert_eq!(inner.len(), 23);

        let token = [0xAA, 0xBB];
        let outer = outer_advertisement(&inner, true, token);

        assert_eq!(outer.len(), 27);
        assert_eq!(outer.len(), FAST_MAX_ADVERTISEMENT_LEN);
        assert_eq!(&outer[0..2], &[0x4A, 0x17]);
        assert_eq!(&outer[2..25], inner.as_slice());
        assert_eq!(&outer[25..27], &token);
    }

    #[test]
    fn inner_regular_adds_hash_mac_uwb_extra() {
        let endpoint_id = *b"WXYZ";
        let info = vec![0u8; 27];

        let inner = inner_advertisement(endpoint_id, &info, false);

        // byte0(1) + hash(3) + id(4) + len(1) + info(27) + mac(6) + uwb(1) + extra(1) = 44
        assert_eq!(inner.len(), 44);
        assert_eq!(inner[0], 0x23);
        assert_eq!(&inner[1..4], &[0xFC, 0x9F, 0x5E]);
        assert_eq!(&inner[4..8], b"WXYZ");
        assert_eq!(inner[8], 27);
        assert_eq!(&inner[9..36], info.as_slice());
        assert_eq!(&inner[36..42], &[0u8; 6]); // bluetooth_mac
        assert_eq!(inner[42], 0); // uwb len
        assert_eq!(inner[43], 0); // extra
    }

    #[test]
    fn outer_regular_byte0_and_size_field() {
        let inner = vec![0u8; 44];
        let token = [0x01, 0x02];

        let outer = outer_advertisement(&inner, false, token);

        // byte0(1) + hash(3) + size(4 BE) + inner(44) + token(2) = 54
        assert_eq!(outer.len(), 54);
        assert_eq!(outer[0], 0x48);
        assert_eq!(&outer[1..4], &[0xFC, 0x9F, 0x5E]);
        assert_eq!(&outer[4..8], &44u32.to_be_bytes());
        assert_eq!(&outer[8..52], inner.as_slice());
        assert_eq!(&outer[52..54], &token);
    }

    #[test]
    fn ble_advertisement_header_is_17_bytes_with_version_byte() {
        let hash = advertisement_hash(b"some full outer advertisement bytes");
        let psm: u16 = 0x0085;

        let header = ble_advertisement_header(hash, psm);

        assert_eq!(header.len(), 17);
        assert_eq!(header[0], 0x41);
        assert_eq!(&header[1..11], &[0xFFu8; 10]);
        assert_eq!(&header[11..15], &hash);
        assert_eq!(&header[15..17], &psm.to_be_bytes());
    }

    #[test]
    fn real_endpoint_info_forces_regular_mode() {
        // With a real, visible device name the endpoint_info is always well over
        // the 17-byte fast cap (16 random salt + 1 header + 1 len byte already
        // exceeds it before any name bytes at all).
        let info = build_endpoint_info(DEVICE_TYPE_LAPTOP, DEVICE_NAME);
        assert!(info.len() > FAST_MAX_ENDPOINT_INFO_LEN);
    }

    #[test]
    fn gen_endpoint_id_is_ascii_alnum() {
        let id = gen_endpoint_id();
        assert!(id.iter().all(|b| b.is_ascii_alphanumeric()));
    }

    // -----------------------------------------------------------------
    // Framed L2CAP protocol tests, against captured/worked vectors.
    // -----------------------------------------------------------------

    #[test]
    fn frame_prepends_4byte_be_length() {
        assert_eq!(frame(&[0x17]), vec![0, 0, 0, 1, 0x17]);
        assert_eq!(frame(&[]), vec![0, 0, 0, 0]);
    }

    #[test]
    fn parse_l2cap_command_captured_request_advertisement() {
        // Captured vector: `01 00 03 16 d9 ae` -> RequestAdvertisement(hash=16d9ae).
        let payload = [0x01, 0x00, 0x03, 0x16, 0xd9, 0xae];
        assert_eq!(
            parse_l2cap_command(&payload),
            Some(L2capCommand::RequestAdvertisement {
                hash: [0x16, 0xd9, 0xae]
            })
        );
    }

    #[test]
    fn parse_l2cap_command_captured_request_data_connection() {
        // Captured vector: `03` -> RequestDataConnection.
        let payload = [0x03];
        assert_eq!(
            parse_l2cap_command(&payload),
            Some(L2capCommand::RequestDataConnection)
        );
    }

    #[test]
    fn parse_l2cap_command_response_advertisement_roundtrip() {
        let advertisement = vec![0xAA, 0xBB, 0xCC, 0xDD];
        let mut payload = vec![OPCODE_RESPONSE_ADVERTISEMENT];
        payload.extend_from_slice(&(advertisement.len() as u16).to_be_bytes());
        payload.extend_from_slice(&advertisement);

        assert_eq!(
            parse_l2cap_command(&payload),
            Some(L2capCommand::ResponseAdvertisement { advertisement })
        );
    }

    #[test]
    fn parse_l2cap_command_unknown_opcode_is_logged_not_errored() {
        assert_eq!(
            parse_l2cap_command(&[0x7F]),
            Some(L2capCommand::Unknown { opcode: 0x7F })
        );
    }

    #[test]
    fn parse_l2cap_command_empty_payload_is_none() {
        assert_eq!(parse_l2cap_command(&[]), None);
    }

    #[test]
    fn varint_roundtrips_small_and_multibyte_values() {
        for value in [0u64, 1, 127, 128, 300, 16384, u32::MAX as u64] {
            let mut buf = Vec::new();
            encode_varint(value, &mut buf);
            let mut pos = 0usize;
            assert_eq!(decode_varint(&buf, &mut pos), Some(value));
            assert_eq!(pos, buf.len());
        }
    }

    #[test]
    fn parse_socket_control_frame_introduction_worked_example() {
        // `08 01 12 07 0A 03 fc 9f 5e 10 02`: type=1 (INTRODUCTION),
        // introduction{ service_id_hash=fc9f5e, socket_version=2 (V2) }.
        let bytes = [0x08, 0x01, 0x12, 0x07, 0x0A, 0x03, 0xfc, 0x9f, 0x5e, 0x10, 0x02];

        let parsed = parse_socket_control_frame(&bytes);

        assert_eq!(parsed.frame_type, Some(1));
        assert_eq!(
            parsed.service_id_hash.as_deref(),
            Some([0xfc, 0x9f, 0x5e].as_slice())
        );
        assert_eq!(parsed.socket_version, Some(2));
        assert_eq!(control_frame_type_name(parsed.frame_type), "INTRODUCTION");
    }

    #[test]
    fn build_packet_ack_encodes_expected_prefix_and_roundtrips_size() {
        let hash = [0xfc, 0x9f, 0x5e];
        let received_size = 42i32;

        let ack = build_packet_ack(hash, received_size);

        // `[00 00 00]` BlePacket-control prefix, then `08 03 22 <L> ...`.
        assert_eq!(&ack[0..3], &[0x00, 0x00, 0x00]);
        assert_eq!(&ack[3..6], &[0x08, 0x03, 0x22]);

        let parsed = parse_socket_control_frame(&ack[3..]);
        assert_eq!(parsed.frame_type, Some(CONTROL_TYPE_PACKET_ACKNOWLEDGEMENT));
        assert_eq!(parsed.service_id_hash.as_deref(), Some(hash.as_slice()));
        assert_eq!(parsed.received_size, Some(received_size as u64));
    }

    #[test]
    fn build_packet_ack_roundtrips_large_received_size() {
        let hash = [0x01, 0x02, 0x03];
        let received_size = 987_654i32;

        let ack = build_packet_ack(hash, received_size);
        let parsed = parse_socket_control_frame(&ack[3..]);

        assert_eq!(parsed.received_size, Some(received_size as u64));
    }

    // -----------------------------------------------------------------
    // Bridge framing (inbound <-> L2CAP data tier) round-trips.
    // -----------------------------------------------------------------

    #[test]
    fn wrap_inbound_frame_prepends_hash_and_outer_length() {
        // What InboundRequest.send_frame writes: [4B len=3][frame aa bb cc].
        let inbound_framed = [0x00, 0x00, 0x00, 0x03, 0xAA, 0xBB, 0xCC];

        let wire = wrap_inbound_frame_as_ble_data([0xfc, 0x9f, 0x5e], &inbound_framed);

        assert_eq!(
            wire,
            vec![
                0x00, 0x00, 0x00, 0x0A, // outer BE length = 10
                0xfc, 0x9f, 0x5e, // service_id_hash
                0x00, 0x00, 0x00, 0x03, // inner BE length = 3
                0xAA, 0xBB, 0xCC, // OfflineFrame bytes
            ]
        );
    }

    #[test]
    fn unwrap_ble_data_payload_strips_hash() {
        let payload = [0xfc, 0x9f, 0x5e, 0x00, 0x00, 0x00, 0x03, 0xAA, 0xBB, 0xCC];

        let inner = unwrap_ble_data_payload(&payload, [0xfc, 0x9f, 0x5e]);

        assert_eq!(
            inner,
            Some([0x00, 0x00, 0x00, 0x03, 0xAA, 0xBB, 0xCC].as_slice())
        );
    }

    #[test]
    fn unwrap_ble_data_payload_rejects_foreign_hash() {
        let payload = [0x01, 0x00, 0x03, 0x16, 0xd9, 0xae];
        assert_eq!(unwrap_ble_data_payload(&payload, [0xfc, 0x9f, 0x5e]), None);
        assert_eq!(unwrap_ble_data_payload(&[0x01], [0xfc, 0x9f, 0x5e]), None);
    }

    #[test]
    fn wrap_then_unwrap_round_trips_the_inbound_frame() {
        let inbound_framed = [0x00, 0x00, 0x00, 0x02, 0x12, 0x34];
        let hash = [0xfc, 0x9f, 0x5e];

        let wire = wrap_inbound_frame_as_ble_data(hash, &inbound_framed);
        let payload = &wire[4..];
        let unwrapped = unwrap_ble_data_payload(payload, hash).unwrap();

        assert_eq!(unwrapped, &inbound_framed);
    }
}
