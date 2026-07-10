use proc_macro::TokenStream;

use quote::quote;
use syn::{
    Data, DeriveInput, Error, Fields, ImplGenerics, Index, Result, Type, TypeGenerics, WhereClause,
    WherePredicate, parse_macro_input,
};

#[proc_macro_derive(LatticeOrd)]
pub fn derive_lattice_ord(input: TokenStream) -> TokenStream {
    match derive_impl(
        parse_macro_input!(input as DeriveInput),
        |name| {
            quote! {
                self.#name.leq(&other.#name)
            }
        },
        |leqs| {
            quote! {
                #(#leqs)&&*
            }
        },
        |index| {
            quote! {
                self.#index.leq(&other.#index)
            }
        },
        |leqs| {
            quote! {
                #(#leqs)&&*
            }
        },
        |ty| syn::parse_quote!(#ty: LatticeOrd),
        |impl_generics, ty_generics, name, where_clause, body| {
            quote! {
                impl #impl_generics LatticeOrd for #name #ty_generics #where_clause {
                    fn leq(&self, other: &Self) -> bool {
                        #body
                    }
                }
            }
        },
        "LatticeOrd can only be derived for structs",
    ) {
        Ok(tokens) => tokens.into(),
        Err(error) => error.to_compile_error().into(),
    }
}

#[proc_macro_derive(Join)]
pub fn derive_join(input: TokenStream) -> TokenStream {
    match derive_impl(
        parse_macro_input!(input as DeriveInput),
        |name| {
            quote! {
                #name: self.#name.join(&other.#name)
            }
        },
        |joins| {
            quote! {
                Self {
                    #(#joins),*
                }
            }
        },
        |index| {
            quote! {
                self.#index.join(&other.#index)
            }
        },
        |joins| {
            quote! {
                Self(
                    #(#joins),*
                )
            }
        },
        |ty| syn::parse_quote!(#ty: Join),
        |impl_generics, ty_generics, name, where_clause, body| {
            quote! {
                impl #impl_generics Join for #name #ty_generics #where_clause {
                    fn join(&self, other: &Self) -> Self {
                        #body
                    }
                }
            }
        },
        "Join can only be derived for structs",
    ) {
        Ok(tokens) => tokens.into(),
        Err(error) => error.to_compile_error().into(),
    }
}

#[proc_macro_derive(Meet)]
pub fn derive_meet(input: TokenStream) -> TokenStream {
    match derive_impl(
        parse_macro_input!(input as DeriveInput),
        |name| {
            quote! {
                #name: self.#name.meet(&other.#name)
            }
        },
        |meets| {
            quote! {
                Self {
                    #(#meets),*
                }
            }
        },
        |meets| {
            quote! {
                self.#meets.meet(&other.#meets)
            }
        },
        |meets| {
            quote! {
                Self(
                    #(#meets),*
                )
            }
        },
        |ty| syn::parse_quote!(#ty: Meet),
        |impl_generics, ty_generics, name, where_clause, body| {
            quote! {
                impl #impl_generics Meet for #name #ty_generics #where_clause {
                    fn meet(&self, other: &Self) -> Self {
                        #body
                    }
                }
            }
        },
        "Meet can only be derived for structs",
    ) {
        Ok(tokens) => tokens.into(),
        Err(error) => error.to_compile_error().into(),
    }
}

fn derive_impl(
    input: DeriveInput,
    named_field_derive: impl Fn(&proc_macro2::Ident) -> proc_macro2::TokenStream,
    named_fields_derive: impl Fn(Vec<proc_macro2::TokenStream>) -> proc_macro2::TokenStream,
    unnamed_field_derive: impl Fn(&Index) -> proc_macro2::TokenStream,
    unnamed_fields_derive: impl Fn(Vec<proc_macro2::TokenStream>) -> proc_macro2::TokenStream,
    generic_derive: impl Fn(&Type) -> WherePredicate,
    impl_derive: impl Fn(
        ImplGenerics,
        TypeGenerics,
        &proc_macro2::Ident,
        Option<&WhereClause>,
        proc_macro2::TokenStream,
    ) -> proc_macro2::TokenStream,
    impl_error: &str,
) -> Result<proc_macro2::TokenStream> {
    let name = &input.ident;

    let (body, field_types) = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => {
                let derives = fields
                    .named
                    .iter()
                    .map(|field| {
                        let name = field
                            .ident
                            .as_ref()
                            .expect("named fields should have a name");
                        named_field_derive(&name)
                    })
                    .collect();

                let types = fields.named.iter().map(|field| &field.ty);

                (named_fields_derive(derives), types.collect::<Vec<_>>())
            }

            Fields::Unnamed(fields) => {
                let derives = fields
                    .unnamed
                    .iter()
                    .enumerate()
                    .map(|(i, _)| unnamed_field_derive(&syn::Index::from(i)))
                    .collect();

                let types = fields.unnamed.iter().map(|field| &field.ty);

                (unnamed_fields_derive(derives), types.collect::<Vec<_>>())
            }

            Fields::Unit => (
                quote! {
                    Self
                },
                Vec::new(),
            ),
        },

        _ => {
            return Err(Error::new(proc_macro2::Span::call_site(), impl_error));
        }
    };

    let mut generics = input.generics.clone();

    for ty in field_types {
        generics
            .make_where_clause()
            .predicates
            .push(generic_derive(ty));
    }

    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    Ok(impl_derive(
        impl_generics,
        ty_generics,
        name,
        where_clause,
        body,
    ))
}
