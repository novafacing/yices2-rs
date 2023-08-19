//! High-level Yices2 bindings

// Allow unused unsafe because the yices! macro is sometimes not unsafe but having two
// versions of it would be silly
#![allow(unused_unsafe)]

use crate::error::Error;
use crate::sys::{yices_exit, yices_init, yices_reset};
type Result<T> = std::result::Result<T, Error>;

#[cfg(feature = "ctor")]
pub mod init;

pub mod context;
pub mod error;
pub mod gc;
pub mod model;
pub mod sys;
pub mod term;
pub mod typ;
pub mod value;

#[cfg(not(feature = "ctor"))]
pub struct Yices {}

#[cfg(not(feature = "ctor"))]
impl Yices {
    pub fn new() {
        init();
    }

    pub fn reset(&self) {
        reset();
    }
}

#[cfg(not(feature = "ctor"))]
impl Drop for Yices {
    fn drop(&mut self) {
        exit();
    }
}

#[cfg(not(feature = "ctor"))]
pub fn init() {
    unsafe { yices_init() };
}

#[cfg(not(feature = "ctor"))]
pub fn exit() {
    unsafe { yices_exit() };
}

pub fn reset() {
    unsafe { yices_reset() };
}

#[cfg(all(test, feature = "ctor"))]
mod ctor_test {
    use crate::{
        context::Context,
        term::{NamedTerm, Term, Uninterpreted},
        typ::Real,
    };
    use anyhow::Result;

    #[test]
    fn test_mcsat() -> Result<()> {
        let x = Uninterpreted::new(Real::new()?.into())?;
        x.set_name("x")?;
        let p: Term = "(= (* x x) 2)".parse()?;
        let ctx = Context::new()?;
        ctx.assert([p])?;
        let status = ctx.check()?;
        Ok(())
    }
}
