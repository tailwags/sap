use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(Parser, attributes(arg))]
pub fn parser(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let help = generate_help(&input);
    let version = format!("{}\n", std::env::var("CARGO_PKG_VERSION").unwrap());
    let name = input.ident;

    quote! {
        impl #name {
            const HELP: &'static str = #help;
            const VERSION: &'static str = #version;
        
            fn parse<I>(args: I) -> ::std::result::Result<Self, Error>
            where
                I: IntoIterator<Item = ::std::ffi::OsString>,
            {
                use sap::Arg;

                let mut args = args.into_iter().peekable();
        
                let mut normal = None;
                let mut utf8 = None;
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
                        b"--normal" => match args.next() {
                            Some(arg) if arg.is_value() => normal = Some(arg),
                            _ => return Err(Error::MissingValue("--normal")),
                        },
                        b"--optional" => match args.next() {
                            Some(arg) if arg.is_value() => optional = Some(arg),
                            _ => return Err(Error::MissingValue("--optional")),
                        },
                        b"--utf8" => match args.next() {
                            Some(arg) if arg.is_value() => utf8 = Some(arg.to_string_lossy().into_owned()),
                            _ => return Err(Error::MissingValue("--utf8")),
                        },
                        b"--flag" => flag = true,
                        b"--multiple" => {
                            let mut container = Vec::new();
        
                            while let Some(arg) = args.next_if(|arg| arg.is_value()) {
                                container.push(arg)
                            }
        
                            multiple = Some(container)
                        }
                        _ => return Err(Error::UnexpectedArgument(arg.to_os_string())),
                    }
                }
        
                Ok(Self {
                    normal: normal.ok_or(Error::MissingArgument("--normal"))?,
                    utf8: utf8.ok_or(Error::MissingArgument("--utf8"))?,
                    flag,
                    optional,
                    multiple: multiple.ok_or(Error::MissingArgument("--multiple"))?,
                })
            }
        }
    }
    .into()
}

fn generate_help(_input: &DeriveInput) -> String {
    "This is a sample generated help message\n".to_string()
}
