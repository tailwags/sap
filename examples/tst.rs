use std::{
    ffi::OsString,
    io::{stdout, Write},
    os::unix::prelude::OsStrExt,
    path::PathBuf,
};

use sap::{Arg, Error, Parser};

#[derive(Debug)]
#[allow(unused)]
struct Args {
    normal: OsString,
    utf8: String,
    path: PathBuf,
    flag: bool,
    optional: Option<OsString>,
    multiple: Vec<OsString>,
}

impl Parser for Args {
    const HELP: &'static str = "help\n";
    const VERSION: &'static str = env!("CARGO_PKG_VERSION");

    fn try_parse<I>(args: I) -> Result<Self, Error>
    where
        I: IntoIterator<Item = OsString>,
    {
        let mut args = args.into_iter().peekable();

        let mut normal = None;
        let mut utf8 = None;
        let mut path = None;
        let mut flag = false;
        let mut optional = None;
        let mut multiple = None;

        while let Some(arg) = args.next() {
            match arg.as_bytes() {
                b"--help" | b"-h" => {
                    let _ = stdout().write_all(Self::HELP.as_bytes());
                    ::std::process::exit(0);
                }
                b"--version" | b"-V" => {
                    let _ = stdout().write_all(Self::VERSION.as_bytes());
                    ::std::process::exit(0);
                }
                b"--normal" => normal = sap::get_value(args.next(), "--normal")?,
                b"--optional" => optional = sap::get_value(args.next(), "--optional")?,
                b"--utf8" => match args.next() {
                    Some(arg) if arg.is_value() => utf8 = Some(arg.to_string_lossy().into_owned()),
                    _ => return Err(Error::MissingValue("--utf8")),
                },
                b"--path" => path = sap::get_value(args.next(), "--path")?,
                b"--flag" => flag = true,
                b"--multiple" => {
                    let mut container = Vec::new();

                    while let Some(arg) = args.next_if(|arg| arg.is_value()) {
                        container.push(arg)
                    }

                    multiple = Some(container)
                }
                _ => return Err(Error::UnexpectedArgument(arg)),
            }
        }

        Ok(Self {
            normal: normal.ok_or(Error::MissingArgument("--normal"))?,
            utf8: utf8.ok_or(Error::MissingArgument("--utf8"))?,
            path: path.ok_or(Error::MissingArgument("--path"))?,
            flag,
            optional,
            multiple: multiple.ok_or(Error::MissingArgument("--multiple"))?,
        })
    }
}

fn main() -> Result<(), Error> {
    let args = Args::try_parse(std::env::args_os().skip(1))?;

    dbg!(args);

    Ok(())
}
