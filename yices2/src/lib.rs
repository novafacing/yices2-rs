//! High-level Yices2 bindings
//!
//! For general Yices2 usage and API knowledge, consult the [Yices2
//! Docs](https://yices.csl.sri.com/doc/index.html). This crate is a high-level wrapper
//! around the Yices2 C API, and as such, the documentation here will be sparse,
//! describing only the Rust-specific interface.

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

#[cfg(all(test, feature = "ctor"))]
mod ctor_test {
    use crate::{
        context::{Config, Context, Logic, Status},
        reset,
        term::{
            AbsoluteValue, Add, ArithmeticConstant, ArithmeticEqualAtom, ArithmeticGreaterThanAtom,
            ArithmeticGreaterThanEqualAtom, ArithmeticLessThanAtom, ArithmeticLessThanEqualAtom,
            BitVectorAdd, BitVectorConstant, BitVectorSignedGreaterThanAtom,
            BitVectorSignedLessThanAtom, Equal, Gc, IfThenElse, IntegerDivision, Mul, NamedTerm,
            Or, Power, Square, Sub, Term, Uninterpreted,
        },
        typ::{BitVector, Bool, Integer, Real},
    };
    use anyhow::Result;

    #[test]
    /// mcsat_example.c test case
    fn test_example_mcsat() -> Result<()> {
        let x = Uninterpreted::new(Real::new()?.into())?;
        x.set_name("x")?;
        let p: Term = "(= (* x x) 2)".parse()?;
        let config = Config::with_defaults_for_logics([Logic::QF_NRA])?;
        let ctx = Context::with_config(&config)?;
        ctx.assert([p])?;
        let status = ctx.check()?;
        assert_eq!(status, Status::STATUS_SAT);
        let model = ctx.model()?;
        let dv = model.double(&x.into())?;
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

        let x = Uninterpreted::new(Integer::new()?.into())?;
        x.set_name("x")?;

        let t1 = IfThenElse::new(
            Equal::new(x.into(), ArithmeticConstant::zero()?.into())?.into(),
            ArithmeticConstant::zero()?.into(),
            ArithmeticConstant::from_i32(-1)?.into(),
        )?;
        let t2 = Sub::new(x.into(), t1.into())?;
        let t3 = Add::new(x.into(), t1.into())?;
        let arbitrary = Mul::new(Square::new(t2.into())?.into(), t3.into())?;

        let zero = ArithmeticConstant::zero()?;
        let alternate_zero = IfThenElse::new(
            Equal::new(arbitrary.into(), zero.into())?.into(),
            zero.into(),
            IntegerDivision::new(zero.into(), arbitrary.into())?.into(),
        )?;
        let alternate_one = IfThenElse::new(
            Equal::new(arbitrary.into(), zero.into())?.into(),
            arbitrary.into(),
            IntegerDivision::new(arbitrary.into(), arbitrary.into())?.into(),
        )?;
        let one = IfThenElse::new(
            Equal::new(alternate_zero.into(), arbitrary.into())?.into(),
            ArithmeticConstant::from_i32(1)?.into(),
            alternate_one.into(),
        )?;
        let one_eq_zero = ArithmeticEqualAtom::new(ArithmeticConstant::zero()?.into(), one.into())?;

        ctx.assert([one_eq_zero.into()])?;

        let status = ctx.check()?;

        assert_eq!(status, Status::STATUS_UNSAT);

        Ok(())
    }

    #[test]
    fn test_term_utils() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_NIA])?;
        let ctx = Context::with_config(&config)?;

        let x = Uninterpreted::new(Integer::new()?.into())?;
        x.set_name("x")?;

        let one = ArithmeticConstant::from_i32(1)?;
        let ite_term = IfThenElse::new(
            ArithmeticGreaterThanEqualAtom::new(one.into(), x.into())?.into(),
            ArithmeticConstant::from_i32(-1)?.into(),
            one.into(),
        )?;
        let abs_term = AbsoluteValue::new(ite_term.into())?;

        ctx.assert([Equal::new(abs_term.into(), one.into())?.into()])?;

        let status = ctx.check()?;

        assert_eq!(status, Status::STATUS_SAT);

        Ok(())
    }

    #[test]
    fn refcount_issue() -> Result<()> {
        reset();

        let bool_type = Bool::new()?;

        for _ in 0..255 {
            let t = Uninterpreted::new(bool_type.into())?;
            t.incref()?;
        }

        Ok(())
    }

    #[test]
    fn rba_buffer_terms() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_NIA])?;
        let ctx = Context::with_config(&config)?;
        let x = Uninterpreted::new(Integer::new()?.into())?;
        x.set_name("x")?;

        let power_term = Power::new(Square::new(x.into())?.into(), 2)?;
        let leq_term = ArithmeticLessThanEqualAtom::new(power_term.into(), x.into())?;
        ctx.assert([leq_term.into()])?;
        assert_eq!(ctx.check()?, Status::STATUS_SAT);

        Ok(())
    }

    #[test]
    fn rationals() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_NIA])?;
        let ctx = Context::with_config(&config)?;
        let val = ArithmeticConstant::from_i64(-8)?;
        let val_sqrt = IntegerDivision::new(val.into(), val.into())?;
        let eq_one =
            ArithmeticEqualAtom::new(val_sqrt.into(), ArithmeticConstant::from_i64(1)?.into())?;
        ctx.assert([eq_one.into()])?;
        assert_eq!(ctx.check()?, Status::STATUS_SAT);

        Ok(())
    }

    #[test]
    fn model_eval() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_LIA])?;
        let ctx = Context::with_config(&config)?;
        let x = Uninterpreted::new(Integer::new()?.into())?;
        x.set_name("x")?;
        let r_1 = IntegerDivision::new(x.into(), ArithmeticConstant::from_i32(2)?.into())?;
        let check_zero_t1 =
            ArithmeticEqualAtom::new(ArithmeticConstant::zero()?.into(), r_1.into())?;
        ctx.assert([check_zero_t1.into()])?;
        assert_eq!(ctx.check()?, Status::STATUS_SAT);
        let mdl = ctx.model_with_eliminated()?;
        let check_mdl = mdl.bool(&check_zero_t1.into())?;
        assert!(check_mdl);

        Ok(())
    }

    #[test]
    /// The example from the Yices2 readme for LRA
    fn readme_lra() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_LRA])?;
        let ctx = Context::with_config(&config)?;
        let x = Uninterpreted::with_name(Real::new()?.into(), "x")?;
        let y = Uninterpreted::with_name(Real::new()?.into(), "y")?;
        let t1 = Add::new(x.into(), y.into())?;
        let t2 = ArithmeticGreaterThanAtom::new(t1.into(), ArithmeticConstant::zero()?.into())?;
        let t3 = Or::new([
            ArithmeticLessThanAtom::new(x.into(), ArithmeticConstant::zero()?.into())?.into(),
            ArithmeticLessThanAtom::new(y.into(), ArithmeticConstant::zero()?.into())?.into(),
        ])?;
        ctx.assert([t2.into(), t3.into()])?;
        let status = ctx.check()?;
        assert_eq!(status, Status::STATUS_SAT);
        let xv = ctx.model()?.double(&x.into())?;
        let yv = ctx.model()?.double(&y.into())?;
        assert_eq!(xv, 2.0);
        assert_eq!(yv, -1.0);
        Ok(())
    }

    #[test]
    fn readme_bv() -> Result<()> {
        reset();

        let config = Config::with_defaults_for_logics([Logic::QF_BV])?;
        let ctx = Context::with_config(&config)?;
        let bv = BitVector::new(32)?;
        let bvc = BitVectorConstant::from_hex_with_name("00000000", "c")?;
        let x = Uninterpreted::with_name(bv.into(), "x")?;
        let y = Uninterpreted::with_name(bv.into(), "y")?;
        let a1 = BitVectorSignedGreaterThanAtom::new(x.into(), bvc.into())?;
        let a2 = BitVectorSignedGreaterThanAtom::new(y.into(), bvc.into())?;
        let a3 = BitVectorSignedLessThanAtom::new(
            BitVectorAdd::new(x.into(), y.into())?.into(),
            x.into(),
        )?;
        ctx.assert([a1.into(), a2.into(), a3.into()])?;

        assert_eq!(ctx.check()?, Status::STATUS_SAT);
        Ok(())
    }
}
