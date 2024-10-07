use anyhow::Result;
use sap::Parser;
use std::ffi::OsString;

#[derive(Debug, Parser)]
#[allow(unused)]
struct Args {
    normal: OsString,
    utf8: String,
    flag: bool,
    optional: Option<OsString>,
    multiple: Vec<OsString>,
}

fn main() -> Result<()> {
    let args = Args::try_parse(std::env::args_os().skip(1))?;

    dbg!(args);

    Ok(())
}
