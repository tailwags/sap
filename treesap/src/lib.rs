#![deny(missing_docs)]
//! # treesap
//!
//! A `#[derive(Parser)]` interface for [`sap`].
//!
//! treesap lets you declare your CLI arguments as a plain Rust struct and
//! generates a `parse()` method that calls into `sap` under the hood.
//!
//! > **Work in progress.** Only `bool` fields mapped to long flags are
//! > currently functional. See the
//! > [README](https://github.com/tailwags/sap/blob/main/treesap/README.md)
//! > for a full breakdown of implemented versus planned features.
//!
//! ## Usage
//!
//! ```rust,no_run
//! use treesap::Parser;
//!
//! #[derive(Debug, Parser)]
//! struct Args {
//!     verbose: bool,
//!     dry_run: bool,
//! }
//!
//! fn main() -> sap::Result<()> {
//!     let args = Args::parse()?;
//!
//!     if args.verbose {
//!         println!("verbose mode enabled");
//!     }
//!
//!     if args.dry_run {
//!         println!("dry-run: no changes will be made");
//!     }
//!
//!     Ok(())
//! }
//! ```

/// The `Parser` derive macro.
///
/// Generates a `parse() -> sap::Result<Self>` associated function on the
/// annotated struct. Each `bool` field becomes a long flag matching the field
/// name literally (e.g. a field named `dry_run` maps to `--dry_run`, not
/// `--dry-run`; hyphen conversion is not yet implemented).
///
/// `#[arg(…)]` and `#[command(…)]` attributes are accepted by the macro but
/// are not yet acted upon.
///
/// See the [crate-level documentation](crate) and the
/// [README](https://github.com/tailwags/sap/blob/main/treesap/README.md) for
/// current limitations and the planned feature roadmap.
pub use treesap_macros::Parser;
