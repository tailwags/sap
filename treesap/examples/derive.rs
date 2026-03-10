//! Demonstrates `#[derive(Parser)]` with treesap.
//!
//! Each `bool` field becomes a long flag matching the field name. Pass the
//! flag on the command line to set it to `true`; omit it to leave it `false`.
//!
//! Run with:
//!
//! ```text
//! cargo run --example derive
//! cargo run --example derive -- --verbose
//! cargo run --example derive -- --verbose --dry-run
//! ```

use treesap::Parser;

/// Arguments accepted by this program.
#[derive(Debug, Parser)]
struct Args {
    /// Enable verbose output.
    verbose: bool,

    /// Perform a dry run without making any changes.
    dry_run: bool,
}

fn main() -> sap::Result<()> {
    let args = Args::parse()?;

    if args.verbose {
        println!("verbose mode enabled");
    }

    if args.dry_run {
        println!("dry-run: no changes will be made");
    }

    if !args.verbose && !args.dry_run {
        println!("no flags set — try --verbose or --dry-run");
    }

    Ok(())
}
