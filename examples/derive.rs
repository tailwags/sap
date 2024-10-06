use std::{
    ffi::OsString,
    io::{stdout, Write},
    os::unix::prelude::OsStrExt,
};

use sap::Error;
use sap_macros::Parser;

#[derive(Debug, Parser)]
#[allow(unused)]
struct Args {
    normal: OsString,
    utf8: String,
    flag: bool,
    optional: Option<OsString>,
    multiple: Vec<OsString>,
}

fn main() -> Result<(), Error> {
    let args = Args::parse(std::env::args_os().skip(1))?;

    dbg!(args);

    Ok(())
}
