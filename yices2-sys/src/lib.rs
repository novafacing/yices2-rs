//! yices2-sys low-level bindings

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(clippy::useless_transmute)]
// NOTE: Only allows Block to be used -- no other problems needing this allow
#![allow(improper_ctypes)]
// NOTE: Allows the use of the ::block crate
#![allow(unused_imports)]

#[cfg(feature = "use-generated")]
include!(concat!(env!("OUT_DIR"), "/bindings.rs"));

#[cfg(not(feature = "use-generated"))]
include!("bindings.rs");
