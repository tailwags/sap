use proc_macro::TokenStream;
use quote::quote;
use syn::{Data, DataStruct, DeriveInput, parse_macro_input};

#[proc_macro_derive(Parser, attributes(arg, command))]
pub fn derive_parser(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let ident = input.ident;

    match input.data {
        Data::Struct(DataStruct { fields, .. }) => {
            let mut field_declarations = Vec::new();
            let mut field_setters = Vec::new();
            let mut field_getters = Vec::new();

            for field in fields {
                let ident = field.ident.unwrap();
                let ty = field.ty;
                let option = ident.to_string();

                field_declarations.push(quote! {
                    let mut #ident: Option<#ty> = None;
                });

                field_setters.push(quote! {
                    sap::Argument::Long(#option) => { #ident = Some(true) }
                });

                field_getters.push(quote! {
                    #ident: #ident.unwrap()
                });
            }

            quote! {
                impl #ident {
                    const HELP: &str = "";

                    pub fn parse() -> ::sap::Result<Self> {
                        use std::io::Write as _;

                        let mut arg_parser = sap::Parser::from_env()?;

                        #(#field_declarations)*

                        while let Some(arg) = arg_parser.forward()? {

                            match arg {
                                // Long("version") => {
                                //     stdout
                                //         .write_all(
                                //             "wc (puppyutils) 0.0.1\nLicensed under the European Union Public Licence (EUPL) <https://eupl.eu/>\n"
                                //                 .as_bytes(),
                                //         )?;
                                //     stdout.flush()?;
                                //     std::process::exit(0);
                                // }
                                // Long("help") => {
                                //     stdout
                                //         .write_all(
                                //             "Usage: wc [OPTION]... [FILE]...\nPrint newline, word, and byte counts for each FILE.  A word is a nonempty \nsequence of non white space delimited by white space characters or by start \nor end of input.\n\n  -c, --bytes    print the byte counts\n  -m, --chars    print the character counts\n  -l, --lines    print the newline counts\n  -w, --words    print the word counts\n      --help     display this help and exit\n      --version  output version information and exit\n\nWith no FILE, or when FILE is -, read standard input.\n"
                                //                 .as_bytes(),
                                //         )?;
                                //     stdout.flush()?;
                                //     std::process::exit(0);
                                // }
                                #(#field_setters),*
                                arg => return Err(arg.into_error(None)),
                            }
                        }

                        Ok(Self { #(#field_getters),* })
                    }
                }

            }
            .into()
        }
        Data::Enum(_data_enum) => todo!(),
        Data::Union(_data_union) => todo!(),
    }
}
