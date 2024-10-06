//! This crate defines the surface language for the Pion programming language.
//! See `lexical-syntax.md` and `context-free-syntax.md` in the specification.

#![feature(allocator_api, str_from_raw_parts)]

pub mod lex;
pub mod parse;
pub mod print;
pub mod syntax;
