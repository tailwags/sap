use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, LitStr};

#[proc_macro]
pub fn utf16_string(tokens: TokenStream) -> TokenStream {
    let literal = parse_macro_input!(tokens as LitStr).value();

    let utf16_encoded: Vec<u16> = literal.encode_utf16().collect();

    quote! {
        {
            [#(#utf16_encoded),*]
        }
    }
    .into()
}
