//! # Yices2
//!
//! High level bindings to the Yices2 SMT solver.
//!
//! ## Examples
//!
//! Some examples to demonstrate usage of this library.
//!
//! ### Linear Real Arithmetic
//!
//! ```rust,no_run
//! use yices2::prelude::*;
//!
//! fn main() -> Result<(), Error> {
//!   let config = Config::with_defaults_for_logics([Logic::QF_LRA])?;
//!   let ctx = Context::with_config(&config)?;
//!   let x = Uninterpreted::with_name(RealType::new()?, "x")?;
//!   let y = Uninterpreted::with_name(RealType::new()?, "y")?;
//!   let t1 = Add::new(x, y)?;
//!   let t2: Term = ArithmeticGreaterThanAtom::new(t1, ArithmeticConstant::zero()?)?.into();
//!   let t3: Term = Or::new([
//!       ArithmeticLessThanAtom::new(x, ArithmeticConstant::zero()?)?,
//!       ArithmeticLessThanAtom::new(y, ArithmeticConstant::zero()?)?,
//!   ])?.into();
//!   ctx.assert([t2, t3])?;
//!   let status = ctx.check()?;
//!   assert_eq!(status, Status::STATUS_SAT);
//!   let xv = ctx.model()?.get_double(x)?;
//!   let yv = ctx.model()?.get_double(y)?;
//!   assert_eq!(xv, 2.0);
//!   assert_eq!(yv, -1.0);
//!
//!   Ok(())
//! }
//! ```
//!
//! ### BitVectors
//!
//! ```rust,no_run
//! use yices2::prelude::*;
//!
//! fn main() -> Result<(), Error> {
//!   let config = Config::with_defaults_for_logics([Logic::QF_BV])?;
//!   let ctx = Context::with_config(&config)?;
//!   let bv = BitVectorType::new(32)?;
//!   let bvc = BitVectorConstant::from_hex_with_name("00000000", "c")?;
//!   let x = Uninterpreted::with_name(bv, "x")?;
//!   let y = Uninterpreted::with_name(bv, "y")?;
//!   let a1: Term = BitVectorSignedGreaterThanAtom::new(x, bvc)?.into();
//!   let a2: Term = BitVectorSignedGreaterThanAtom::new(y, bvc)?.into();
//!   let a3: Term = BitVectorSignedLessThanAtom::new(
//!       BitVectorAdd::new(x, y)?,
//!       x,
//!   )?.into();
//!   ctx.assert([a1, a2, a3])?;
//!
//!   assert_eq!(ctx.check()?, Status::STATUS_SAT);
//!
//!   Ok(())
//! }
//! ```
//!
//! ## Usage
//!
//! You can add this crate to your project by running:
//!
//! ```sh
//! cargo add yices2
//! ```
//!
//! Or by adding this line to your `Cargo.toml`:
//!
//! ```toml
//! yices2 = { version = "2.6.4-patch.1" }
//! ```
//!
//! ## Features
//!
//! By default, `yices2` enables the `ctor` feature, which calls `yices_init` at program
//! initialization and `yices_exit` at program exit. If you'd like to disable this behavior,
//! you can use the `default-features = false` flag in your `Cargo.toml`.
//!
//! ```toml
//! yices2 = { version = "2.6.4-patch.1", default-features = false }
//! ```
//!
//! ## Notes
//!
//! This library is not thread safe, because the underlying `Yices2` library is not thread
//! safe. Do not use this library in multithreaded code. To use in multi-threaded code,
//! create a separate process and submit requests to the solver running in that process or
//! disable the `ctor` feature and manage state yourself.

// Allow unused unsafe because the yices! macro is sometimes not unsafe but having two
// versions of it would be silly
#![allow(unused_unsafe)]
#![deny(clippy::unwrap_used)]

use crate::error::Error;
use crate::sys::yices_reset;

#[cfg(not(feature = "ctor"))]
use crate::sys::{yices_exit, yices_init};

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

// TODO: How do we manage this? We don't know drop order, but we need to have one.
// We'll just use the compiler approach for now and not free yices memory.
//
// #[cfg(all(feature = "ctor", not(test)))]
// impl Drop for Yices {
//     fn drop(&mut self) {
//         exit();
//     }
// }

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

#[cfg(feature = "prelude")]
/// Use all items at the top level of this module, makes importing
/// easier by just writing `use yices2::prelude::*;`
pub mod prelude {
    pub use super::*;
    pub use crate::context::*;
    pub use crate::error::*;
    pub use crate::gc::*;
    pub use crate::init::*;
    pub use crate::model::*;
    pub use crate::sys;
    pub use crate::term::*;
    pub use crate::typ::*;
    pub use crate::value::*;
}

#[cfg(all(test, feature = "ctor"))]
mod ctor_test {
    use crate::{
        context::{Config, Context, Logic, Status},
        reset,
        term::{
            AbsoluteValue, Add, ArithmeticConstant, ArithmeticEqualAtom, ArithmeticGreaterThanAtom,
            ArithmeticGreaterThanEqualAtom, ArithmeticLessThanAtom, ArithmeticLessThanEqualAtom,
            BitVectorAdd, BitVectorConstant, BitVectorSignedGreaterThanAtom,
            BitVectorSignedLessThanAtom, Equal, GcTerm, IfThenElse, IntegerDivision, Mul,
            NamedTerm, Or, Power, Square, Sub, Term, Uninterpreted,
        },
        typ::{BitVectorType, BoolType, IntegerType, RealType},
    };
    use anyhow::Result;

    #[test]
    /// mcsat_example.c test case
    fn test_example_mcsat() -> Result<()> {
        let x = Uninterpreted::new(RealType::new()?)?;
        x.set_name("x")?;
        let p: Term = "(= (* x x) 2)".parse()?;
        let config = Config::with_defaults_for_logics([Logic::QF_NRA])?;
        let ctx = Context::with_config(&config)?;
        ctx.assert([p])?;
        let status = ctx.check()?;
        assert_eq!(status, Status::STATUS_SAT);
        let model = ctx.model()?;
        let dv = model.get_double(x)?;
        // I mean yeah...float stuff
        assert_eq!(dv * dv, 1.9999999999999996);
        Ok(())
    }

    #[test]
    /// uf_plugin.c test case
    fn test_uf_plugin() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_NIA])?;
        let ctx = Context::with_config(&config)?;

        let x = Uninterpreted::new(IntegerType::new()?)?;
        x.set_name("x")?;

        let t1 = IfThenElse::new(
            Equal::new(x, ArithmeticConstant::zero()?)?,
            ArithmeticConstant::zero()?,
            ArithmeticConstant::from_i32(-1)?,
        )?;
        let t2 = Sub::new(x, t1)?;
        let t3 = Add::new(x, t1)?;
        let arbitrary = Mul::new(Square::new(t2)?, t3)?;

        let zero = ArithmeticConstant::zero()?;
        let alternate_zero = IfThenElse::new(
            Equal::new(arbitrary, zero)?,
            zero,
            IntegerDivision::new(zero, arbitrary)?,
        )?;
        let alternate_one = IfThenElse::new(
            Equal::new(arbitrary, zero)?,
            arbitrary,
            IntegerDivision::new(arbitrary, arbitrary)?,
        )?;
        let one = IfThenElse::new(
            Equal::new(alternate_zero, arbitrary)?,
            ArithmeticConstant::from_i32(1)?,
            alternate_one,
        )?;
        let one_eq_zero = ArithmeticEqualAtom::new(ArithmeticConstant::zero()?, one)?;

        ctx.assert([one_eq_zero])?;

        let status = ctx.check()?;

        assert_eq!(status, Status::STATUS_UNSAT);

        Ok(())
    }

    #[test]
    fn test_term_utils() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_NIA])?;
        let ctx = Context::with_config(&config)?;

        let x = Uninterpreted::new(IntegerType::new()?)?;
        x.set_name("x")?;

        let one = ArithmeticConstant::from_i32(1)?;
        let ite_term = IfThenElse::new(
            ArithmeticGreaterThanEqualAtom::new(one, x)?,
            ArithmeticConstant::from_i32(-1)?,
            one,
        )?;
        let abs_term = AbsoluteValue::new(ite_term)?;

        ctx.assert([Equal::new(abs_term, one)?])?;

        let status = ctx.check()?;

        assert_eq!(status, Status::STATUS_SAT);

        Ok(())
    }

    #[test]
    fn refcount_issue() -> Result<()> {
        reset();

        let bool_type = BoolType::new()?;

        for _ in 0..255 {
            let t = Uninterpreted::new(bool_type)?;
            t.incref()?;
        }

        Ok(())
    }

    #[test]
    fn rba_buffer_terms() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_NIA])?;
        let ctx = Context::with_config(&config)?;
        let x = Uninterpreted::new(IntegerType::new()?)?;
        x.set_name("x")?;

        let power_term = Power::new(Square::new(x)?, 2)?;
        let leq_term = ArithmeticLessThanEqualAtom::new(power_term, x)?;
        ctx.assert([leq_term])?;
        assert_eq!(ctx.check()?, Status::STATUS_SAT);

        Ok(())
    }

    #[test]
    fn rationals() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_NIA])?;
        let ctx = Context::with_config(&config)?;
        let val = ArithmeticConstant::from_i64(-8)?;
        let val_sqrt = IntegerDivision::new(val, val)?;
        let eq_one = ArithmeticEqualAtom::new(val_sqrt, ArithmeticConstant::from_i64(1)?)?;
        ctx.assert([eq_one])?;
        assert_eq!(ctx.check()?, Status::STATUS_SAT);

        Ok(())
    }

    #[test]
    fn model_eval() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_LIA])?;
        let ctx = Context::with_config(&config)?;
        let x = Uninterpreted::new(IntegerType::new()?)?;
        x.set_name("x")?;
        let r_1 = IntegerDivision::new(x, ArithmeticConstant::from_i32(2)?)?;
        let check_zero_t1 = ArithmeticEqualAtom::new(ArithmeticConstant::zero()?, r_1)?;
        ctx.assert([check_zero_t1])?;
        assert_eq!(ctx.check()?, Status::STATUS_SAT);
        let mdl = ctx.model_with_eliminated()?;
        let check_mdl = mdl.get_bool(check_zero_t1)?;
        assert!(check_mdl);

        Ok(())
    }

    #[test]
    /// The example from the Yices2 readme for LRA
    fn readme_lra() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_LRA])?;
        let ctx = Context::with_config(&config)?;
        let x = Uninterpreted::with_name(RealType::new()?, "x")?;
        let y = Uninterpreted::with_name(RealType::new()?, "y")?;
        let t1 = Add::new(x, y)?;
        let t2: Term = ArithmeticGreaterThanAtom::new(t1, ArithmeticConstant::zero()?)?.into();
        let t3: Term = Or::new([
            ArithmeticLessThanAtom::new(x, ArithmeticConstant::zero()?)?,
            ArithmeticLessThanAtom::new(y, ArithmeticConstant::zero()?)?,
        ])?
        .into();
        ctx.assert([t2, t3])?;
        let status = ctx.check()?;
        assert_eq!(status, Status::STATUS_SAT);
        let xv = ctx.model()?.get_double(x)?;
        let yv = ctx.model()?.get_double(y)?;
        assert_eq!(xv, 2.0);
        assert_eq!(yv, -1.0);
        Ok(())
    }

    #[test]
    fn readme_bv() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_BV])?;
        let ctx = Context::with_config(&config)?;
        let bv = BitVectorType::new(32)?;
        let bvc = BitVectorConstant::from_hex_with_name("00000000", "c")?;
        let x = Uninterpreted::with_name(bv, "x")?;
        let y = Uninterpreted::with_name(bv, "y")?;
        let a1: Term = BitVectorSignedGreaterThanAtom::new(x, bvc)?.into();
        let a2: Term = BitVectorSignedGreaterThanAtom::new(y, bvc)?.into();
        let a3: Term = BitVectorSignedLessThanAtom::new(BitVectorAdd::new(x, y)?, x)?.into();
        ctx.assert([a1, a2, a3])?;

        assert_eq!(ctx.check()?, Status::STATUS_SAT);
        Ok(())
    }
}
