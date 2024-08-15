#![feature(if_let_guard)]
#![feature(let_chains)]

use std::collections::HashMap;

use proc_macro::TokenStream;
use proc_macro2::{Ident, Span};
use quote::quote;
use syn::{
    parse_macro_input, spanned::Spanned, Data, DataStruct, DeriveInput, Error, Expr, ExprPath, Field, Meta, PredicateType, ReturnType, Type, TypeArray, TypeBareFn, TypeGroup, TypeParen, TypePath, TypePtr, TypeReference, TypeSlice, TypeTuple, WherePredicate
};

#[proc_macro_derive(TypedBuilder, attributes(typed_builder))]
pub fn typed_builder(token: TokenStream) -> TokenStream {
    let DeriveInput {
        attrs,
        vis,
        ident,
        generics,
        data,
    } = parse_macro_input!(token as DeriveInput);

    let generics_predicates = generics
        .where_clause
        .into_iter()
        .flat_map(|p| p.predicates.into_iter())
        .filter_map(|p| match p {
            WherePredicate::Type(ty) => match ty.bounded_ty {
                Type::Path(ref path) => match path.path.require_ident() {
                    Ok(ok) => Some(Ok((ok.clone(), ty))),
                    Err(err) => Some(Err(err)),
                },
                _ => None,
            },
            _ => None,
        })
        .collect::<Result<HashMap<Ident, PredicateType>, _>>();
    // map all predicates so that if generics are used, it is properly constrained on with_ooo function
    let generics_predicates = match generics_predicates {
        Ok(ok) => ok,
        Err(err) => return err.into_compile_error().into(),
    };

    // default name
    let builder = if let Some(kv) = attrs.into_iter().find_map(|p| match p.meta {
        Meta::NameValue(kv) if kv.path.is_ident("name") => Some(kv),
        _ => None,
    }) {
        match &kv.value {
            Expr::Path(ExprPath { path, .. }) => match path.require_ident() {
                Ok(ok) => ok.clone(),
                Err(err) => return err.into_compile_error().into(),
            },
            x => {
                return Error::new(x.span(), "Only supports valid ident as value")
                    .to_compile_error()
                    .into()
            }
        }
    } else {
        Ident::new(&format!("{}Builder", ident), Span::call_site())
    };

    let generics_mapping = match data {
        Data::Struct(DataStruct { fields, .. }) => fields.into_iter(),
        Data::Enum(e) => {
            return Error::new(e.enum_token.span(), "Not supported")
                .to_compile_error()
                .into()
        }
        Data::Union(u) => {
            return Error::new(u.union_token.span(), "Not supported")
                .to_compile_error()
                .into()
        }
    }
    .enumerate()
    .map(|(i, p)| {
        (
            p.ident.clone().expect("Struct always exists"),
            (Ident::new(&format!("T{i}"), Span::call_site()), p),
        )
    })
    .collect::<HashMap<Ident, (Ident, Field)>>();

    let generics = generics_mapping.values().map(|p| &p.0).collect::<Vec<_>>();
    let fields = generics_mapping
        .iter()
        .map(|(name, (gen, _field))| quote! { #name: #gen });
    let basic_impls =
        generics_mapping
            .iter()
            .enumerate()
            .filter_map(|(i, (name, (_gen, field)))| {
                if field
                    .attrs
                    .iter()
                    .all(|p| matches!(&p.meta, Meta::Path(kv) if !kv.is_ident("skip")))
                {
                    let builder = builder.clone();
                    let (omitted_before, omitted_after) = generics.split_at(i);
                    let func_name = Ident::new(&format!("with_{}", name), Span::call_site());
                    let omitted_fields = generics_mapping
                        .keys()
                        .filter(|p| *p != name)
                        .collect::<Vec<_>>();
                    let mut where_clauses = Vec::new();
                    let mut lifetimes = Vec::new();
                    let mut remaining_types = vec![&field.ty];
                    let ty = &field.ty;
                    while let Some(ty) = remaining_types.pop() {
                        match ty {
                            // bare functions can use generics on input/output types
                            Type::BareFn(TypeBareFn { inputs, output, ..}) => {
                                remaining_types.extend(inputs.iter().map(|p| &p.ty));

                                if let ReturnType::Type(_, ty) = output {
                                    remaining_types.push(ty);
                                }
                            },
                            // Form of type superset like array, recursively check types
                            Type::Array(TypeArray { elem, .. })
                             | Type::Group(TypeGroup { elem, .. })
                             | Type::Paren(TypeParen { elem, .. })
                             | Type::Ptr(TypePtr { elem, .. })
                             | Type::Slice(TypeSlice { elem, .. }) => remaining_types.push(elem.as_ref()),
                            Type::Reference(TypeReference { lifetime, elem, .. }) => {
                                if let Some(life) = lifetime && !lifetimes.contains(&life) {
                                    lifetimes.push(life);
                                }
                                remaining_types.push(elem.as_ref());
                            },
                            Type::Tuple(TypeTuple { elems, .. }) => remaining_types.extend(elems.iter()),
                            // actual generic value
                            Type::Path(TypePath { path, .. }) if let Some(ident) = path.get_ident() => {
                                if let Some(definition) = generics_predicates.get(ident) {
                                    where_clauses.push(definition);
                                }
                            },
                            // Never and Trait Object is essentially a regular type, not generic, leave alone
                            Type::Never(_) 
                             | Type::TraitObject(_) => {},
                            // Error cases
                            Type::Macro(m) => return Error::new(m.span(), "Macro as type not supported").into_compile_error().into(),
                            x => return Error::new(x.span(), "Stream did not fit in any of the types").into_compile_error().into(),
                        }
                    }

                    let wh = (!where_clauses.is_empty() || !lifetimes.is_empty()).then_some(quote! { where });
                    let lt = (!lifetimes.is_empty()).then_some(quote! { <'a> });

                    quote! {
                        impl<#(#omitted_before,)* #(#omitted_after,)*> #builder<#(#omitted_before,)* (), #(#omitted_after,)*> {
                            pub fn #func_name #lt(self, #name) -> #builder<#(#omitted_before,)* #ty, #(#omitted_after,)*>
                            #wh #(#where_clauses,)* #('a: #lifetimes)+*  {
                                let #builder {
                                    #(#omitted_fields,)*
                                    ..
                                } = self;

                                Self {
                                    #(#omitted_fields,)*
                                    #name
                                }
                            }
                        }
                    }
                    .into()
                } else {
                    None
                }
            });

    quote! {
        // Generated by TypedBuilder
        #vis struct #builder<#(#generics),*> {
            #(#fields),*
        }

        #(#basic_impls)*
    }
    .into()
}
