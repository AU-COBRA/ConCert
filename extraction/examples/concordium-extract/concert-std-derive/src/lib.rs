extern crate proc_macro;
extern crate syn;
#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::ToTokens;
use syn::{GenericParam, Ident, Meta, parse_macro_input, parse_quote, spanned::Spanned};

// Taken from Concordium
fn unwrap_or_report(v: syn::Result<TokenStream>) -> TokenStream {
    match v {
        Ok(ts) => ts,
        Err(e) => e.to_compile_error().into(),
    }
}

fn contains_attribute<'a, I: IntoIterator<Item = &'a Meta>>(iter: I, name: &str) -> bool {
    iter.into_iter().any(|attr| attr.path().is_ident(name))
}

#[proc_macro_derive(ConCertSerial)]
pub fn concert_serial_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input);
    unwrap_or_report(impl_concert_serial(&ast))
}

fn impl_concert_serial_field(
    field: &syn::Field,
    ident: &proc_macro2::TokenStream,
    out: &syn::Ident,
) -> syn::Result<proc_macro2::TokenStream> {
    if let Some(l) = find_length_attribute(&field.attrs, "size_length")? {
        let id = format_ident!("u{}", 8 * l);
        Ok(quote! {
            let len: #id = #ident.len() as #id;
            len.concert_serial(#out)?;
            serial_vector_no_length(&#ident, #out)?;
        })
    } else if let Some(l) = find_length_attribute(&field.attrs, "map_size_length")? {
        let id = format_ident!("u{}", 8 * l);
        Ok(quote! {
            let len: #id = #ident.len() as #id;
            len.concert_serial(#out)?;
            serial_map_no_length(&#ident, #out)?;
        })
    } else if let Some(l) = find_length_attribute(&field.attrs, "set_size_length")? {
        let id = format_ident!("u{}", 8 * l);
        Ok(quote! {
            let len: #id = #ident.len() as #id;
            len.concert_serial(#out)?;
            serial_set_no_length(&#ident, #out)?;
        })
    } else if let Some(l) = find_length_attribute(&field.attrs, "string_size_length")? {
        let id = format_ident!("u{}", 8 * l);
        Ok(quote! {
            let len: #id = #ident.len() as #id;
            len.concert_serial(#out)?;
            serial_string(#ident.as_str(), #out)?;
        })
    } else {
        Ok(quote! {
            #ident.concert_serial(#out)?;
        })
    }
}

fn impl_concert_serial(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let data_name = &ast.ident;

    let span = ast.span();

    let write_ident = format_ident!("W", span = span);

    // Require that each type param can be serialized as well
    let mut generics = ast.generics.clone();
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(ConCertSerial))
        }
    }

    let (impl_generics, ty_generics, where_clauses) = generics.split_for_impl();

    let out_ident = format_ident!("out");

    let body = match ast.data {
        syn::Data::Struct(ref data) => {
            let fields_tokens = match data.fields {
                syn::Fields::Named(_) => {
                    data.fields
                        .iter()
                        .map(|field| {
                            let field_ident = field.ident.clone().unwrap(); // safe since named fields.
                            let field_ident = quote!(self.#field_ident);
                            impl_concert_serial_field(field, &field_ident, &out_ident)
                        })
                        .collect::<syn::Result<_>>()?
                }
                syn::Fields::Unnamed(_) => data
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, field)| {
                        let i = syn::LitInt::new(i.to_string().as_str(), Span::call_site());
                        let field_ident = quote!(self.#i);
                        impl_concert_serial_field(field, &field_ident, &out_ident)
                    })
                    .collect::<syn::Result<_>>()?,
                syn::Fields::Unit => proc_macro2::TokenStream::new(),
            };
            quote! {
                #fields_tokens
                Ok(())
            }
        }
        syn::Data::Enum(ref data) => {
            let mut matches_tokens = proc_macro2::TokenStream::new();

            let size = if data.variants.len() <= 256 {
                format_ident!("u8")
            } else if data.variants.len() <= 256 * 256 {
                format_ident!("u16")
            } else {
                unimplemented!(
                    "[derive(ConCertSerial)]: Enums with more than 65536 variants are not supported."
                );
            };

            for (i, variant) in data.variants.iter().enumerate() {
                let (field_names, pattern) = match variant.fields {
                    syn::Fields::Named(_) => {
                        let field_names: Vec<_> = variant
                            .fields
                            .iter()
                            .map(|field| field.ident.clone().unwrap())
                            .collect();
                        (field_names.clone(), quote! { {#(#field_names),*} })
                    }
                    syn::Fields::Unnamed(_) => {
                        let field_names: Vec<_> = variant
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, _)| format_ident!("x_{}", i))
                            .collect();
                        (field_names.clone(), quote! { (#(#field_names),*) })
                    }
                    syn::Fields::Unit => (Vec::new(), proc_macro2::TokenStream::new()),
                };
                let field_tokens: proc_macro2::TokenStream = field_names
                    .iter()
                    .zip(variant.fields.iter())
                    .map(|(name, field)| impl_concert_serial_field(field, &quote!(#name), &out_ident))
                    .collect::<syn::Result<_>>()?;

                let variant_ident = &variant.ident;

                let mut body_tokens = proc_macro2::TokenStream::new();
                if data.variants.len() > 1 {
                    let idx_lit =
                        syn::LitInt::new(format!("{}{}", i, size).as_str(), Span::call_site());

                    body_tokens.extend(quote! { #idx_lit.concert_serial(#out_ident)?; })
                }

                body_tokens.extend(field_tokens);

                matches_tokens.extend(quote! {
                    #data_name::#variant_ident#pattern => {
                        #body_tokens
                    },
                })
            }
            quote! {
                match self {
                    #matches_tokens
                }
                Ok(())
            }
        }
        _ => unimplemented!("#[derive(ConCertSerial)] is not implemented for union."),
    };

    let gen = quote! {
        #[automatically_derived]
        impl #impl_generics ConCertSerial for #data_name #ty_generics #where_clauses {
            fn concert_serial<#write_ident: concordium_std::Write>(&self, #out_ident: &mut #write_ident) -> Result<(), #write_ident::Err> {
                #body
            }
        }
    };
    Ok(gen.into())
}

#[proc_macro_derive(ConCertDeserial)]
pub fn concert_deserial_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input);
    unwrap_or_report(impl_concert_deserial(&ast))
}

/// The prefix used in field attributes: `#[concordium(attr = "something")]`
const CONCORDIUM_FIELD_ATTRIBUTE: &str = "concordium";

/// A list of valid concordium field attributes
const VALID_CONCORDIUM_FIELD_ATTRIBUTES: [&str; 5] =
    ["size_length", "set_size_length", "map_size_length", "string_size_length", "ensure_ordered"];

fn get_concordium_field_attributes(attributes: &[syn::Attribute]) -> syn::Result<Vec<syn::Meta>> {
    attributes
        .iter()
        // Keep only concordium attributes
        .flat_map(|attr| match attr.parse_meta() {
            Ok(syn::Meta::List(list)) if list.path.is_ident(CONCORDIUM_FIELD_ATTRIBUTE) => {
                list.nested
            }
            _ => syn::punctuated::Punctuated::new(),
        })
        // Ensure only valid attributes and unwrap NestedMeta
        .map(|nested| match nested {
            syn::NestedMeta::Meta(meta) => {
                let path = meta.path();
                if VALID_CONCORDIUM_FIELD_ATTRIBUTES.iter().any(|&attr| path.is_ident(attr)) {
                    Ok(meta)
                } else {
                    Err(syn::Error::new(meta.span(),
                        format!("The attribute '{}' is not supported as a concordium field attribute.",
                        path.to_token_stream())
                    ))
                }
            }
            lit => Err(syn::Error::new(lit.span(), "Literals are not supported in a concordium field attribute.")),
        })
        .collect()
}

fn find_field_attribute_value(
    attributes: &[syn::Attribute],
    target_attr: &str,
) -> syn::Result<Option<syn::Lit>> {
    let target_attr = format_ident!("{}", target_attr);
    let attr_values: Vec<_> = get_concordium_field_attributes(attributes)?
        .into_iter()
        .filter_map(|nested_meta| match nested_meta {
            syn::Meta::NameValue(value) if value.path.is_ident(&target_attr) => Some(value.lit),
            _ => None,
        })
        .collect();
    if attr_values.is_empty() {
        return Ok(None);
    }
    if attr_values.len() > 1 {
        let mut init_error = syn::Error::new(
            attr_values[1].span(),
            format!("Attribute '{}' should only be specified once.", target_attr),
        );
        for other in attr_values.iter().skip(2) {
            init_error.combine(syn::Error::new(
                other.span(),
                format!("Attribute '{}' should only be specified once.", target_attr),
            ))
        }
        Err(init_error)
    } else {
        Ok(Some(attr_values[0].clone()))
    }
}

fn find_length_attribute(
    attributes: &[syn::Attribute],
    target_attr: &str,
) -> syn::Result<Option<u32>> {
    let value = match find_field_attribute_value(attributes, target_attr)? {
        Some(v) => v,
        None => return Ok(None),
    };

    let value = match value {
        syn::Lit::Int(int) => int,
        _ => {
            return Err(syn::Error::new(value.span(), "Length attribute value must be an integer."))
        }
    };
    let value = match value.base10_parse() {
        Ok(v) => v,
        _ => {
            return Err(syn::Error::new(
                value.span(),
                "Length attribute value must be a base 10 integer.",
            ))
        }
    };
    match value {
        1 | 2 | 4 | 8 => Ok(Some(value)),
        _ => Err(syn::Error::new(value.span(), "Length info must be either 1, 2, 4, or 8.")),
    }
}

fn impl_concert_deserial_field(
    f: &syn::Field,
    ident: &syn::Ident,
    source: &syn::Ident,
    arena: &syn::Ident,
) -> syn::Result<proc_macro2::TokenStream> {
    let concordium_attributes = get_concordium_field_attributes(&f.attrs)?;
    if let Some(l) = find_length_attribute(&f.attrs, "size_length")? {
        let size = format_ident!("u{}", 8 * l);
        Ok(quote! {
            let #ident = {
                let len = #size::concert_deserial(#source, #arena)?;
                deserial_vector_no_length(#source, len as usize)?
            };
        })
    } else if let Some(l) = find_length_attribute(&f.attrs, "map_size_length")? {
        let size = format_ident!("u{}", 8 * l);
        if contains_attribute(&concordium_attributes, "ensure_ordered") {
            Ok(quote! {
                let #ident = {
                    let len = #size::concert_deserial(#source, #arena)?;
                    deserial_map_no_length(#source, len as usize)?
                };
            })
        } else {
            Ok(quote! {
                let #ident = {
                    let len = #size::concert_deserial(#source, #arena)?;
                    deserial_map_no_length_no_order_check(#source, len as usize)?
                };
            })
        }
    } else if let Some(l) = find_length_attribute(&f.attrs, "set_size_length")? {
        let size = format_ident!("u{}", 8 * l);
        if contains_attribute(&concordium_attributes, "ensure_ordered") {
            Ok(quote! {
                let #ident = {
                    let len = #size::concert_deserial(#source, #arena)?;
                    deserial_set_no_length(#source, len as usize)?
                };
            })
        } else {
            Ok(quote! {
                let #ident = {
                    let len = #size::concert_deserial(#source, #arena)?;
                    deserial_set_no_length_no_order_check(#source, len as usize)?
                };
            })
        }
    } else if let Some(l) = find_length_attribute(&f.attrs, "string_size_length")? {
        let size = format_ident!("u{}", 8 * l);
        Ok(quote! {
            let #ident = {
                let len = #size::concert_deserial(#source, #arena)?;
                deserial_string(#source, len as usize)?
            };
        })
    } else {
        let ty = &f.ty;
        Ok(quote! {
            let #ident = <#ty as ConCertDeserial>::concert_deserial(#source, #arena)?;
        })
    }
}

fn single<It: IntoIterator>(vals: It) -> Option<It::Item> {
    let mut it = vals.into_iter();
    let first = it.next()?;
    if let Some(_) = it.next() {
        None
    } else {
        Some(first)
    }
}

fn impl_concert_deserial(ast: &syn::DeriveInput) -> syn::Result<TokenStream> {
    let data_name = &ast.ident;

    let span = ast.span();

    let read_ident = format_ident!("R", span = span);

    let lifetime =
        if let Some(lt) = single(ast.generics.lifetimes()) {
            lt
        } else {
            return Err(syn::Error::new(
                ast.span(),
                "Expected exactly one lifetime in type"
            ))
        };

    // Require that each type param can be deserialized as well
    let mut generics = ast.generics.clone();
    for param in &mut generics.params {
        if let GenericParam::Type(ref mut type_param) = *param {
            type_param.bounds.push(parse_quote!(ConCertDeserial<#lifetime>))
        }
    }

    //let mut generics = ast.generics.clone();
    //generics.params.push(parse_quote!('_a));
    //let (impl_generics, _, _) = generics.split_for_impl();
    let (impl_generics, ty_generics, where_clauses) = generics.split_for_impl();

    let source_ident = Ident::new("source", Span::call_site());

    let arena_ident = format_ident!("arena", span = span);

    let body_tokens = match ast.data {
        syn::Data::Struct(ref data) => {
            let mut names = proc_macro2::TokenStream::new();
            let mut field_tokens = proc_macro2::TokenStream::new();
            let return_tokens = match data.fields {
                syn::Fields::Named(_) => {
                    for field in data.fields.iter() {
                        let field_ident = field.ident.clone().unwrap(); // safe since named fields.
                        field_tokens.extend(impl_concert_deserial_field(
                            field,
                            &field_ident,
                            &source_ident,
                            &arena_ident,
                        ));
                        names.extend(quote!(#field_ident,))
                    }
                    quote!(Ok(#data_name{#names}))
                }
                syn::Fields::Unnamed(_) => {
                    for (i, f) in data.fields.iter().enumerate() {
                        let field_ident = format_ident!("x_{}", i);
                        field_tokens.extend(impl_concert_deserial_field(f, &field_ident, &source_ident, &arena_ident));
                        names.extend(quote!(#field_ident,))
                    }
                    quote!(Ok(#data_name(#names)))
                }
                _ => quote!(Ok(#data_name{})),
            };
            quote! {
                #field_tokens
                #return_tokens
            }
        }
        syn::Data::Enum(ref data) => {
            let mut matches_tokens = proc_macro2::TokenStream::new();
            let source = Ident::new("source", Span::call_site());
            for (i, variant) in data.variants.iter().enumerate() {
                let (field_names, pattern) = match variant.fields {
                    syn::Fields::Named(_) => {
                        let field_names: Vec<_> = variant
                            .fields
                            .iter()
                            .map(|field| field.ident.clone().unwrap())
                            .collect();
                        (field_names.clone(), quote! { {#(#field_names),*} })
                    }
                    syn::Fields::Unnamed(_) => {
                        let field_names: Vec<_> = variant
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, _)| format_ident!("x_{}", i))
                            .collect();
                        (field_names.clone(), quote! { ( #(#field_names),* ) })
                    }
                    syn::Fields::Unit => (Vec::new(), proc_macro2::TokenStream::new()),
                };

                let field_tokens: proc_macro2::TokenStream = field_names
                    .iter()
                    .zip(variant.fields.iter())
                    .map(|(name, field)| impl_concert_deserial_field(field, name, &source, &arena_ident))
                    .collect::<syn::Result<proc_macro2::TokenStream>>()?;
                let idx_lit = syn::LitInt::new(i.to_string().as_str(), Span::call_site());
                let variant_ident = &variant.ident;
                matches_tokens.extend(quote! {
                    #idx_lit => {
                        #field_tokens
                        Ok(#data_name::#variant_ident#pattern)
                    },
                })
            }
            let mut idx_tokens = proc_macro2::TokenStream::new();
            if data.variants.len() > 1 {
                let size = if data.variants.len() <= 256 {
                    format_ident!("u8")
                } else if data.variants.len() <= 256 * 256 {
                    format_ident!("u16")
                } else {
                    return Err(syn::Error::new(
                        ast.span(),
                        "[derive(ConCertDeserial)]: Too many variants. Maximum 65536 are supported.",
                    ));
                };

                idx_tokens.extend(quote! { #size::concert_deserial(#source, #arena_ident)? });
            } else {
                idx_tokens.extend(quote! { 0 })
            }
            
            quote! {
                let idx = #idx_tokens;
                match idx {
                    #matches_tokens
                    _ => Err(Default::default())
                }
            }
        }
        _ => unimplemented!("#[derive(ConCertDeserial)] is not implemented for union."),
    };
    let gen = quote! {
        #[automatically_derived]
        impl #impl_generics ConCertDeserial<#lifetime> for #data_name #ty_generics #where_clauses {
            fn concert_deserial<#read_ident: concordium_std::Read>(#source_ident: &mut #read_ident, #arena_ident: &#lifetime bumpalo::Bump) -> concordium_std::ParseResult<Self> {
                #body_tokens
            }
        }
    };
    Ok(gen.into())
}
