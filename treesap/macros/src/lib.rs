//! Internal proc-macro crate powering [`treesap`]'s `#[derive(Parser)]`.
//!
//! Do not depend on this crate directly; use `treesap` instead.

use proc_macro::TokenStream;
use quote::quote;
use syn::{Data, DataStruct, DeriveInput, parse_macro_input};

/// Derives a `parse() -> sap::Result<Self>` implementation for a struct.
///
/// Each named field in the struct becomes a long flag that matches the field
/// name exactly. Currently only `bool` fields are supported; all matched flags
/// are unconditionally set to `true`.
///
/// `#[arg(…)]` and `#[command(…)]` attributes are accepted but not yet acted
/// upon.
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
                        let mut arg_parser = sap::Parser::from_env()?;

                        #(#field_declarations)*

                        while let Some(arg) = arg_parser.forward()? {
                            match arg {
                                #(#field_setters),*
                                arg => return Err(arg.unexpected()),
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
