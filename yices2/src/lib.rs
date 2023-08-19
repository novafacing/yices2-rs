//! High-level Yices2 bindings

// Allow unused unsafe because the yices! macro is sometimes not unsafe but having two
// versions of it would be silly
#![allow(unused_unsafe)]

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
        context::{Config, Context, Status},
        reset,
        term::{
            AbsoluteValue, Add, ArithmeticConstant, ArithmeticEqualAtom,
            ArithmeticGreaterThanEqualAtom, ArithmeticLessThanEqualAtom, Equal, Gc, IfThenElse,
            IntegerDivision, Mul, NamedTerm, Power, Square, Sub, Term, Uninterpreted,
        },
        typ::{Bool, Integer, Real},
    };
    use anyhow::Result;

    #[test]
    /// mcsat_example.c test case
    fn test_example_mcsat() -> Result<()> {
        let x = Uninterpreted::new(Real::new()?.into())?;
        x.set_name("x")?;
        let p: Term = "(= (* x x) 2)".parse()?;
        let config = Config::new()?;
        config.default_for_logic("QF_NRA")?;
        config.set("mode", "one-shot")?;
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

        let config = Config::new()?;
        config.default_for_logic("QF_NIA")?;
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

        let config = Config::new()?;
        config.default_for_logic("QF_NIA")?;
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

        let config = Config::new()?;
        config.default_for_logic("QF_NIA")?;
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

        let config = Config::new()?;
        config.default_for_logic("QF_NIA")?;
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

        let config = Config::new()?;
        config.default_for_logic("QF_LIA")?;
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
}
