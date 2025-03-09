use proc_macro::TokenStream;
use quote::quote;
use syn::{DeriveInput, parse_macro_input};

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

            fn try_parse<I>(args: I) -> ::std::result::Result<Self, sap::Error>
            where
                I: IntoIterator<Item = ::std::ffi::OsString>,
            {
                use sap::Arg;

                let mut args = args.into_iter().peekable();

                todo!()
            }
        }
    }
    .into()
}

fn generate_help(_input: &DeriveInput) -> String {
    "This is a sample generated help message\n".to_string()
}
