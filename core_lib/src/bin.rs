#[macro_use]
extern crate log;

use mqs_lib::MQS;
use tokio::sync::broadcast;

#[tokio::main]
async fn main() -> Result<(), anyhow::Error> {
    // Define log level
    if std::env::var("RUST_LOG").is_err() {
        std::env::set_var(
            "RUST_LOG",
            "TRACE,mdns_sd=ERROR,polling=ERROR,neli=ERROR,bluez_async=ERROR",
        );
    }

    // Init logger/tracing
    tracing_subscriber::fmt::init();

    // Start the MQuickShare service
    let mut mqs = MQS::default();
    mqs.run().await?;

    let discovery_channel = broadcast::channel(10);
    mqs.discovery(discovery_channel.0)?;

    // Wait for CTRL+C and then stop MQS
    let _ = tokio::signal::ctrl_c().await;
    info!("Stopping service.");
    mqs.stop().await;

    Ok(())
}
