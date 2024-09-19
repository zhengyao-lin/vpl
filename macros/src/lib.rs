use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Data, Fields};

/// Given a struct like struct NewType<A1, ..., An>(B1, ..., Bn)
/// where each Bi either implements View, or is a type parameter,
///
/// generate a View impl for NewType that looks like the following
/// impl<A1: View, ..., An: View> View for NewType
/// {
///     type V = NewType<A1::V, ..., An::V>;
///     open spec fn view(&self) -> Self::V {
///         NewType(self.0@, ..., self.n@)
///     }
/// }
///
/// Supports unit and named structs too
#[proc_macro_derive(View)]
pub fn derive_view(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident; // The name of the struct/enum

    // Get type parameters A1, A2, ..., An
    // TODO: collect trait bounds here?
    let generic_idents: Vec<_> = input.generics.params.iter().map(|g| match g {
        syn::GenericParam::Type(ty) => &ty.ident,
        _ => panic!("derive(View) only supports type parameters"),
    }).collect();

    // Generate A1::V, ..., An::V
    let generic_view_types = generic_idents.iter().map(|ident| {
        quote! { <#ident as View>::V }
    });

    // Map to A1: View, ... An: View
    let view_generic_idents: Vec<_> = generic_idents.iter().map(|ident| {
        quote! { #ident: View }
    }).collect();

    // Generate `impl View` body
    let view_body = match input.data {
        Data::Struct(ref data) => {
            match &data.fields {
                Fields::Unnamed(fields) => {
                    // Generate self.0@, ..., self.n@
                    let field_view = (0..fields.unnamed.len()).map(|i| {
                        let i = syn::Index::from(i);
                        quote! { self.#i@ }
                    });

                    // Generate the implementation
                    quote! {
                        ::builtin_macros::verus! {
                            impl<#(#view_generic_idents),*> View for #name<#(#generic_idents),*> {
                                type V = #name<#(#generic_view_types),*>;

                                open spec fn view(&self) -> Self::V {
                                    #name(#(#field_view),*)
                                }
                            }
                        }
                    }
                },
                Fields::Named(fields) => {
                    // Handle named structs
                    let field_view = fields.named.iter().map(|f| {
                        let name = &f.ident;
                        quote! { #name: self.#name@ }
                    });

                    // Generate the implementation for named struct
                    quote! {
                        ::builtin_macros::verus! {
                            impl<#(#view_generic_idents),*> View for #name<#(#generic_idents),*> {
                                type V = #name<#(#generic_view_types),*>;

                                open spec fn view(&self) -> Self::V {
                                    #name {
                                        #(#field_view),*
                                    }
                                }
                            }
                        }
                    }
                },
                Fields::Unit => {
                    quote! {
                        ::builtin_macros::verus! {
                            impl<#(#view_generic_idents),*> View for #name<#(#generic_idents),*> {
                                type V = #name<#(#generic_view_types),*>;

                                open spec fn view(&self) -> Self::V {
                                    #name
                                }
                            }
                        }
                    }
                }
            }
        },
        _ => panic!("derive(View) only supports structs"),
    };

    // eprintln!("Generated code:\n{}", view_body.to_string());

    // Convert the output into a TokenStream
    TokenStream::from(view_body)
}

// #[proc_macro_derive(ASN1Tagged)]
// pub fn derive_asn1_tagged(input: TokenStream) -> TokenStream {
//     let name = parse_macro_input!(input as DeriveInput).ident;

//     TokenStream::from(quote! {
//         ::builtin_macros::verus! {
//             impl ViewWithASN1Tagged for #name {
//                 proof fn lemma_view_preserves_tag(&self) {}
//             }
//         }
//     })
// }

#[proc_macro_derive(ViewWithASN1Tagged)]
pub fn derive_view_with_asn1_tagged(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    // Get type parameters A1, A2, ..., An
    let generic_idents: Vec<_> = input.generics.params.iter().map(|g| match g {
        syn::GenericParam::Type(ty) => &ty.ident,
        _ => panic!("derive(View) only supports type parameters"),
    }).collect();

    // Map to A1: View, ... An: View
    let view_generic_idents: Vec<_> = generic_idents.iter().map(|ident| {
        quote! { #ident: View }
    }).collect();

    TokenStream::from(quote! {
        ::builtin_macros::verus! {
            impl<#(#view_generic_idents),*> ViewWithASN1Tagged for #name<#(#generic_idents),*> {
                proof fn lemma_view_preserves_tag(&self) {}
            }
        }
    })
}
