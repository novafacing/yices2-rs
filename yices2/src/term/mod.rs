use std::{
    ffi::{CStr, CString},
    fmt::Display,
    str::FromStr,
};

use crate::{
    error::Error,
    sys::{
        term_t, type_t, yices_abs, yices_add, yices_and, yices_application, yices_arith_eq0_atom,
        yices_arith_eq_atom, yices_arith_geq0_atom, yices_arith_geq_atom, yices_arith_gt0_atom,
        yices_arith_gt_atom, yices_arith_leq0_atom, yices_arith_leq_atom, yices_arith_lt0_atom,
        yices_arith_lt_atom, yices_arith_neq0_atom, yices_arith_neq_atom, yices_ashift_right,
        yices_bitextract, yices_bvadd, yices_bvand, yices_bvarray, yices_bvashr, yices_bvconcat,
        yices_bvconst_from_array, yices_bvconst_int32, yices_bvconst_int64,
        yices_bvconst_minus_one, yices_bvconst_one, yices_bvconst_uint32, yices_bvconst_uint64,
        yices_bvconst_zero, yices_bvdiv, yices_bveq_atom, yices_bvextract, yices_bvge_atom,
        yices_bvgt_atom, yices_bvle_atom, yices_bvlshr, yices_bvlt_atom, yices_bvmul, yices_bvnand,
        yices_bvneg, yices_bvneq_atom, yices_bvnor, yices_bvnot, yices_bvor, yices_bvpower,
        yices_bvproduct, yices_bvrem, yices_bvrepeat, yices_bvsdiv, yices_bvsge_atom,
        yices_bvsgt_atom, yices_bvshl, yices_bvsle_atom, yices_bvslt_atom, yices_bvsmod,
        yices_bvsquare, yices_bvsrem, yices_bvsub, yices_bvsum, yices_bvxnor, yices_bvxor,
        yices_ceil, yices_clear_term_name, yices_constant, yices_decref_term, yices_distinct,
        yices_divides_atom, yices_division, yices_eq, yices_exists, yices_false, yices_floor,
        yices_forall, yices_free_string, yices_get_term_by_name, yices_get_term_name, yices_idiv,
        yices_iff, yices_imod, yices_implies, yices_incref_term, yices_int32, yices_int64,
        yices_is_int_atom, yices_ite, yices_lambda, yices_mul, yices_neg, yices_neq,
        yices_new_uninterpreted_term, yices_new_variable, yices_not, yices_or, yices_parse_bvbin,
        yices_parse_bvhex, yices_parse_float, yices_parse_rational, yices_parse_term,
        yices_poly_int32, yices_poly_int64, yices_poly_rational32, yices_poly_rational64,
        yices_power, yices_product, yices_rational32, yices_rational64, yices_redand,
        yices_redcomp, yices_redor, yices_remove_term_name, yices_rotate_left, yices_rotate_right,
        yices_select, yices_set_term_name, yices_shift_left0, yices_shift_left1,
        yices_shift_right0, yices_shift_right1, yices_sign_extend, yices_square, yices_sub,
        yices_subst_term, yices_sum, yices_term_bitsize, yices_term_is_arithmetic,
        yices_term_is_bitvector, yices_term_is_bool, yices_term_is_function, yices_term_is_ground,
        yices_term_is_int, yices_term_is_real, yices_term_is_scalar, yices_term_is_tuple,
        yices_term_to_string, yices_true, yices_tuple, yices_tuple_update, yices_type_of_term,
        yices_update, yices_xor, yices_zero, yices_zero_extend, NULL_TERM,
    },
    typ::Type,
    yices, yices_try, Result,
};
use itertools::multiunzip;
use paste::paste;

pub trait InnerTerm {
    fn inner_term(&self) -> term_t;
}

pub trait TryInnerType {
    fn try_inner_type(&self) -> Result<type_t>;
}

pub trait NamedTerm: InnerTerm {
    fn name(&self) -> Result<Option<String>>
    where
        Self: Sized,
    {
        let name = yices! { yices_get_term_name(self.inner_term()) };

        if name.is_null() {
            Ok(None)
        } else {
            Ok(Some(
                unsafe { std::ffi::CStr::from_ptr(name) }
                    .to_str()
                    .map_err(|e| Error::External(e.into()))?
                    .to_owned(),
            ))
        }
    }

    fn set_name(&self, name: &str) -> Result<()>
    where
        Self: Sized,
    {
        let c_str = CString::new(name).map_err(|e| Error::External(e.into()))?;
        let ok = yices! { yices_set_term_name(self.inner_term(), c_str.as_ptr() as *const i8) };

        if ok < 0 {
            Err(Error::TermSetName {
                name: name.to_string(),
            })
        } else {
            Ok(())
        }
    }

    fn clear_name(&self) -> Result<()>
    where
        Self: Sized,
    {
        let ok = yices! { yices_clear_term_name(self.inner_term()) };

        if ok < 0 {
            Err(Error::TermClearName)
        } else {
            Ok(())
        }
    }
}

pub trait GcTerm: InnerTerm {
    fn incref(&self) -> Result<()> {
        yices_try! { yices_incref_term(self.inner_term()) }.and_then(|r| {
            if r < 0 {
                Err(Error::TermIncRef)
            } else {
                Ok(())
            }
        })
    }

    fn decref(&self) -> Result<()> {
        yices_try! { yices_decref_term(self.inner_term()) }.and_then(|r| {
            if r < 0 {
                Err(Error::TermDecRef)
            } else {
                Ok(())
            }
        })
    }
}

macro_rules! impl_term {
    ($id:ident) => {
        paste! {
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub struct $id {
                term: term_t,
            }

            impl $id {
                pub fn typ(&self) -> Result<Type> {
                    let typ = self.try_inner_type()?;
                    typ.try_into()
                }
            }

            impl InnerTerm for $id {
                fn inner_term(&self) -> term_t {
                    self.term
                }
            }

            impl TryInnerType for $id {
                fn try_inner_type(&self) -> Result<type_t> {
                    Ok(yices! { yices_type_of_term(self.inner_term()) })
                }
            }

            impl NamedTerm for $id {}
            impl GcTerm for $id {}

            impl From<term_t> for $id {
                fn from(term: term_t) -> Self {
                    Self { term }
                }
            }

            impl From<&term_t> for $id {
                fn from(term: &term_t) -> Self {
                    Self { term: *term }
                }
            }

            impl From<$id> for term_t {
                fn from(term: $id) -> Self {
                    term.inner_term()
                }
            }

            impl From<&$id> for term_t {
                fn from(term: &$id) -> Self {
                    term.inner_term()
                }
            }

            impl From<$id> for Term {
                fn from(term: $id) -> Self {
                    Self::$id(term)
                }
            }

            impl From<&$id> for Term {
                fn from(term: &$id) -> Self {
                    Self::$id(*term)
                }
            }

            impl TryFrom<Term> for $id {
                type Error = Error;

                fn try_from(term: Term) -> Result<Self> {
                    match term {
                        Term::$id(term) => Ok(term),
                        _ => Err(Error::TermFromTerm),
                    }
                }
            }

            impl TryFrom<&Term> for $id {
                type Error = Error;

                fn try_from(term: &Term) -> Result<Self> {
                    match term {
                        Term::$id(term) => Ok(*term),
                        _ => Err(Error::TermFromTerm),
                    }
                }
            }

            impl std::fmt::Display for $id {
                fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                    let c_str = yices_try! { $crate::sys::yices_term_to_string(self.into(), u32::MAX, 1, 0) }
                        .map_err(|_| std::fmt::Error)?;

                    if c_str.is_null() {
                        Err(std::fmt::Error)
                    } else {
                        let s = unsafe { CStr::from_ptr(c_str) };
                        let s = s.to_str().map_err(|_| std::fmt::Error)?;
                        write!(f, "{}", s)?;
                        yices_try! { $crate::sys::yices_free_string(c_str) }.map_err(|_| std::fmt::Error)
                    }
                }
            }

        }
    };
}

// Any is a special term that can be used to represent any term. This is useful because we
// can get a term by name, but the is_ quanitifiers aren't specific enough to return a
// specific Term specialization.
impl_term! { Any }

impl_term! { Uninterpreted }

impl Uninterpreted {
    pub fn new(typ: Type) -> Result<Self> {
        let ok = yices! { yices_new_uninterpreted_term(typ.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn with_name(typ: Type, name: &str) -> Result<Self> {
        let s = Self::new(typ)?;
        s.set_name(name)?;
        Ok(s)
    }
}

impl_term! { Variable }

impl Variable {
    pub fn new(typ: Type) -> Result<Self> {
        let ok = yices! { yices_new_variable(typ.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn with_name(typ: Type, name: &str) -> Result<Self> {
        let s = Self::new(typ)?;
        s.set_name(name)?;
        Ok(s)
    }
}

impl_term! { Constant }

impl Constant {
    /// typ must either be scalar or uninterpreted
    pub fn new(typ: Type, index: i32) -> Result<Self> {
        let ok = yices! { yices_constant(typ.into(), index) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn with_name(typ: Type, index: i32, name: &str) -> Result<Self> {
        let s = Self::new(typ, index)?;
        s.set_name(name)?;
        Ok(s)
    }
}

impl_term! { IfThenElse }

impl IfThenElse {
    pub fn new(cond: Term, then: Term, els: Term) -> Result<Self> {
        let ok = yices! { yices_ite(cond.into(), then.into(), els.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Equal }

impl Equal {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_eq(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { NotEqual }

impl NotEqual {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_neq(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Distinct }

impl Distinct {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        // terms may be modified by this call
        let mut terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_distinct(terms.len() as u32, terms.as_mut_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Application }

impl Application {
    pub fn new<I>(fun: Term, args: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms: Vec<_> = args.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_application(fun.into(), terms.len() as u32, terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Tuple }

impl Tuple {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_tuple(terms.len() as u32, terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Select }

impl Select {
    pub fn new(tuple: Term, index: u32) -> Result<Self> {
        let ok = yices! { yices_select(index, tuple.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { TupleUpdate }

impl TupleUpdate {
    pub fn new(tuple: Term, index: u32, value: Term) -> Result<Self> {
        let ok = yices! { yices_tuple_update(tuple.into(), index, value.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { FunctionUpdate }

impl FunctionUpdate {
    pub fn new<I>(fun: Term, args: I, value: Term) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms = args.into_iter().map(|t| t.into()).collect::<Vec<_>>();

        let ok =
            yices! { yices_update(fun.into(), terms.len() as u32, terms.as_ptr(), value.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ForAll }

impl ForAll {
    pub fn new<I>(vars: I, body: Term) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let mut terms = vars.into_iter().map(|t| t.into()).collect::<Vec<_>>();

        let ok = yices! { yices_forall(terms.len() as u32, terms.as_mut_ptr(), body.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Exists }

impl Exists {
    pub fn new<I>(vars: I, body: Term) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let mut terms = vars.into_iter().map(|t| t.into()).collect::<Vec<_>>();

        let ok = yices! { yices_exists(terms.len() as u32, terms.as_mut_ptr(), body.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Lambda }

impl Lambda {
    pub fn new<I>(vars: I, body: Term) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms = vars.into_iter().map(|t| t.into()).collect::<Vec<_>>();

        let ok = yices! { yices_lambda(terms.len() as u32, terms.as_ptr(), body.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BooleanConstant }

impl BooleanConstant {
    pub fn from_bool(value: bool) -> Result<Self> {
        let ok = yices! { if value { yices_true() } else { yices_false() } };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_bool_with_name(value: bool, name: &str) -> Result<Self> {
        let s = Self::from_bool(value)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn bitsize(&self) -> Result<u32> {
        Ok(yices! { yices_term_bitsize(self.inner_term()) })
    }
}

impl_term! { Not }

impl Not {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_not(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { And }

impl And {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let mut terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_and(terms.len() as u32, terms.as_mut_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Or }

impl Or {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let mut terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_or(terms.len() as u32, terms.as_mut_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Xor }

impl Xor {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let mut terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_xor(terms.len() as u32, terms.as_mut_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Iff }

impl Iff {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_iff(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Implies }

impl Implies {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_implies(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticConstant }

impl ArithmeticConstant {
    pub fn zero() -> Result<Self> {
        let ok = yices! { yices_zero() };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn zero_with_name(name: &str) -> Result<Self> {
        let s = Self::zero()?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_i32(value: i32) -> Result<Self> {
        let ok = yices! { yices_int32(value) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_i32_with_name(value: i32, name: &str) -> Result<Self> {
        let s = Self::from_i32(value)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_i64(value: i64) -> Result<Self> {
        let ok = yices! { yices_int64(value) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_i64_with_name(value: i64, name: &str) -> Result<Self> {
        let s = Self::from_i64(value)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_rational32(num: i32, den: u32) -> Result<Self> {
        let ok = yices! { yices_rational32(num, den) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_rational32_with_name(num: i32, den: u32, name: &str) -> Result<Self> {
        let s = Self::from_rational32(num, den)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_rational64(num: i64, den: u64) -> Result<Self> {
        let ok = yices! { yices_rational64(num, den) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_rational64_with_name(num: i64, den: u64, name: &str) -> Result<Self> {
        let s = Self::from_rational64(num, den)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_i32_terms<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = (Term, i32)>,
    {
        let (terms, coefficients): (Vec<term_t>, Vec<i32>) = terms
            .into_iter()
            .map(|(term, coefficient)| {
                let term: term_t = term.into();
                (term, coefficient)
            })
            .unzip();

        let ok =
            yices! { yices_poly_int32(terms.len() as u32, coefficients.as_ptr(), terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_i32_terms_with_name<I>(terms: I, name: &str) -> Result<Self>
    where
        I: IntoIterator<Item = (Term, i32)>,
    {
        let s = Self::from_i32_terms(terms)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_i64_terms<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = (Term, i64)>,
    {
        let (terms, coefficients): (Vec<term_t>, Vec<i64>) = terms
            .into_iter()
            .map(|(term, coefficient)| {
                let term: term_t = term.into();
                (term, coefficient)
            })
            .unzip();

        let ok =
            yices! { yices_poly_int64(terms.len() as u32, coefficients.as_ptr(), terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_i64_terms_with_name<I>(terms: I, name: &str) -> Result<Self>
    where
        I: IntoIterator<Item = (Term, i64)>,
    {
        let s = Self::from_i64_terms(terms)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_rational32_terms<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = (Term, i32, u32)>,
    {
        let (terms, numerators, denominators): (Vec<term_t>, Vec<i32>, Vec<u32>) =
            multiunzip(terms.into_iter().map(|(term, numerator, denominator)| {
                let term: term_t = term.into();
                (term, numerator, denominator)
            }));

        let ok = yices! { yices_poly_rational32(terms.len() as u32, numerators.as_ptr(), denominators.as_ptr(), terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_rational32_terms_with_name<I>(terms: I, name: &str) -> Result<Self>
    where
        I: IntoIterator<Item = (Term, i32, u32)>,
    {
        let s = Self::from_rational32_terms(terms)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_rational64_terms<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = (Term, i64, u64)>,
    {
        let (terms, numerators, denominators): (Vec<term_t>, Vec<i64>, Vec<u64>) =
            multiunzip(terms.into_iter().map(|(term, numerator, denominator)| {
                let term: term_t = term.into();
                (term, numerator, denominator)
            }));

        let ok = yices! { yices_poly_rational64(terms.len() as u32, numerators.as_ptr(), denominators.as_ptr(), terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_rational64_terms_with_name<I>(terms: I, name: &str) -> Result<Self>
    where
        I: IntoIterator<Item = (Term, i64, u64)>,
    {
        let s = Self::from_rational64_terms(terms)?;
        s.set_name(name)?;
        Ok(s)
    }
}

impl FromStr for ArithmeticConstant {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        if s.contains('e') || s.contains('.') {
            let cstring = CString::new(s).map_err(|e| Error::External(e.into()))?;

            let ok = yices! { yices_parse_float(cstring.as_ptr()) };

            if ok < 0 {
                Err(Error::NewTerm)
            } else {
                Ok(Self { term: ok })
            }
        } else {
            let cstring = CString::new(s).map_err(|e| Error::External(e.into()))?;

            let ok = yices! { yices_parse_rational(cstring.as_ptr()) };

            if ok < 0 {
                Err(Error::NewTerm)
            } else {
                Ok(Self { term: ok })
            }
        }
    }
}

impl_term! { Add }

impl Add {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_add(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Sub }

impl Sub {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_sub(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Neg }

impl Neg {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_neg(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Mul }

impl Mul {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_mul(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Square }

impl Square {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_square(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Power }

impl Power {
    pub fn new(base: Term, exponent: u32) -> Result<Self> {
        let ok = yices! { yices_power(base.into(), exponent) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Division }

impl Division {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_division(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Sum }

impl Sum {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_sum(terms.len() as u32, terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Product }

impl Product {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_product(terms.len() as u32, terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { AbsoluteValue }

impl AbsoluteValue {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_abs(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Floor }

impl Floor {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_floor(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { Ceiling }

impl Ceiling {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_ceil(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { IntegerDivision }

impl IntegerDivision {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_idiv(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { IntegerModulo }

impl IntegerModulo {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_imod(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticEqualAtom }

impl ArithmeticEqualAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_arith_eq_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticNotEqualAtom }

impl ArithmeticNotEqualAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_arith_neq_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticLessThanAtom }

impl ArithmeticLessThanAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_arith_lt_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticLessThanEqualAtom }

impl ArithmeticLessThanEqualAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_arith_leq_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticGreaterThanAtom }

impl ArithmeticGreaterThanAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_arith_gt_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticGreaterThanEqualAtom }

impl ArithmeticGreaterThanEqualAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_arith_geq_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticLessThanZeroAtom }

impl ArithmeticLessThanZeroAtom {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_arith_lt0_atom(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticLessThanEqualZeroAtom }

impl ArithmeticLessThanEqualZeroAtom {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_arith_leq0_atom(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticGreaterThanZeroAtom }

impl ArithmeticGreaterThanZeroAtom {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_arith_gt0_atom(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticGreaterThanEqualZeroAtom }

impl ArithmeticGreaterThanEqualZeroAtom {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_arith_geq0_atom(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticEqualZeroAtom }

impl ArithmeticEqualZeroAtom {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_arith_eq0_atom(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { ArithmeticNotEqualZeroAtom }

impl ArithmeticNotEqualZeroAtom {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_arith_neq0_atom(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { DividesAtom }

impl DividesAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_divides_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { IsIntegerAtom }

impl IsIntegerAtom {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_is_int_atom(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorConstant }

impl BitVectorConstant {
    pub fn from_i32(size: u32, value: i32) -> Result<Self> {
        let ok = yices! { yices_bvconst_int32(size, value) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_i32_with_name(size: u32, value: i32, name: &str) -> Result<Self> {
        let s = Self::from_i32(size, value)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_i64(size: u32, value: i64) -> Result<Self> {
        let ok = yices! { yices_bvconst_int64(size, value) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_i64_with_name(size: u32, value: i64, name: &str) -> Result<Self> {
        let s = Self::from_i64(size, value)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_u32(size: u32, value: u32) -> Result<Self> {
        let ok = yices! { yices_bvconst_uint32(size, value) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_u32_with_name(size: u32, value: u32, name: &str) -> Result<Self> {
        let s = Self::from_u32(size, value)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_u64(size: u32, value: u64) -> Result<Self> {
        let ok = yices! { yices_bvconst_uint64(size, value) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_u64_with_name(size: u32, value: u64, name: &str) -> Result<Self> {
        let s = Self::from_u64(size, value)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn zero(size: u32) -> Result<Self> {
        let ok = yices! { yices_bvconst_zero(size) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn zero_with_name(size: u32, name: &str) -> Result<Self> {
        let s = Self::zero(size)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn one(size: u32) -> Result<Self> {
        let ok = yices! { yices_bvconst_one(size) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn one_with_name(size: u32, name: &str) -> Result<Self> {
        let s = Self::one(size)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn minus_one(size: u32) -> Result<Self> {
        let ok = yices! { yices_bvconst_minus_one(size) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn minus_one_with_name(size: u32, name: &str) -> Result<Self> {
        let s = Self::minus_one(size)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_i32_terms<I>(values: I) -> Result<Self>
    where
        I: IntoIterator<Item = i32>,
    {
        let values: Vec<_> = values.into_iter().collect();

        let ok = yices! { yices_bvconst_from_array(values.len() as u32, values.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_i32_terms_with_name<I>(values: I, name: &str) -> Result<Self>
    where
        I: IntoIterator<Item = i32>,
    {
        let s = Self::from_i32_terms(values)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_hex<S>(hex: S) -> Result<Self>
    where
        S: AsRef<str>,
    {
        let hex = CString::new(hex.as_ref()).map_err(|e| Error::External(e.into()))?;

        let ok = yices! { yices_parse_bvhex(hex.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_hex_with_name<S>(hex: S, name: &str) -> Result<Self>
    where
        S: AsRef<str>,
    {
        let s = Self::from_hex(hex)?;
        s.set_name(name)?;
        Ok(s)
    }

    pub fn from_bin<S>(bin: S) -> Result<Self>
    where
        S: AsRef<str>,
    {
        let bin = CString::new(bin.as_ref()).map_err(|e| Error::External(e.into()))?;

        let ok = yices! { yices_parse_bvbin(bin.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }

    pub fn from_bin_with_name<S>(bin: S, name: &str) -> Result<Self>
    where
        S: AsRef<str>,
    {
        let s = Self::from_bin(bin)?;
        s.set_name(name)?;
        Ok(s)
    }
}

impl_term! { BitVectorAdd }

impl BitVectorAdd {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvadd(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorSub }

impl BitVectorSub {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvsub(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorNeg }

impl BitVectorNeg {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_bvneg(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorMul }

impl BitVectorMul {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvmul(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorSquare }

impl BitVectorSquare {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_bvsquare(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorPower }

impl BitVectorPower {
    pub fn new(base: Term, exponent: u32) -> Result<Self> {
        let ok = yices! { yices_bvpower(base.into(), exponent) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorSum }

impl BitVectorSum {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_bvsum(terms.len() as u32, terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorProduct }

impl BitVectorProduct {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_bvproduct(terms.len() as u32, terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorDivision }

impl BitVectorDivision {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvdiv(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorRemainder }

impl BitVectorRemainder {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvrem(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorSignedDivision }

impl BitVectorSignedDivision {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvsdiv(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorSignedRemainder }

impl BitVectorSignedRemainder {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvsrem(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorSignedModulo }

impl BitVectorSignedModulo {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvsmod(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorNot }

impl BitVectorNot {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_bvnot(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorAnd }

impl BitVectorAnd {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_bvand(terms.len() as u32, terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorOr }

impl BitVectorOr {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_bvor(terms.len() as u32, terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorXor }

impl BitVectorXor {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_bvxor(terms.len() as u32, terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorNAnd }

impl BitVectorNAnd {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvnand(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorNOr }

impl BitVectorNOr {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvnor(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorXNor }

impl BitVectorXNor {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvxnor(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorShiftLeftFill0 }

impl BitVectorShiftLeftFill0 {
    pub fn new(left: Term, n: u32) -> Result<Self> {
        let ok = yices! { yices_shift_left0(left.into(), n) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorShiftLeftFill1 }

impl BitVectorShiftLeftFill1 {
    pub fn new(left: Term, n: u32) -> Result<Self> {
        let ok = yices! { yices_shift_left1(left.into(), n) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorShiftRightFill0 }

impl BitVectorShiftRightFill0 {
    pub fn new(left: Term, n: u32) -> Result<Self> {
        let ok = yices! { yices_shift_right0(left.into(), n) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorShiftRightFill1 }

impl BitVectorShiftRightFill1 {
    pub fn new(left: Term, n: u32) -> Result<Self> {
        let ok = yices! { yices_shift_right1(left.into(), n) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorArithmeticShiftRightConstant }

impl BitVectorArithmeticShiftRightConstant {
    pub fn new(left: Term, n: u32) -> Result<Self> {
        let ok = yices! { yices_ashift_right(left.into(), n) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorRotateLeft }

impl BitVectorRotateLeft {
    pub fn new(left: Term, n: u32) -> Result<Self> {
        let ok = yices! { yices_rotate_left(left.into(), n) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorRotateRight }

impl BitVectorRotateRight {
    pub fn new(left: Term, n: u32) -> Result<Self> {
        let ok = yices! { yices_rotate_right(left.into(), n) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorShiftLeft }

impl BitVectorShiftLeft {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvshl(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorShiftRight }

impl BitVectorShiftRight {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvlshr(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorArithmeticShiftRight }

impl BitVectorArithmeticShiftRight {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvashr(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorExtract }

impl BitVectorExtract {
    pub fn new(term: Term, lower: u32, upper: u32) -> Result<Self> {
        let ok = yices! { yices_bvextract(term.into(), lower, upper) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorBitExtract }

impl BitVectorBitExtract {
    pub fn new(term: Term, bit: u32) -> Result<Self> {
        let ok = yices! { yices_bitextract(term.into(), bit) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorConcatenate }

impl BitVectorConcatenate {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_bvconcat(terms.len() as u32, terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorRepeat }

impl BitVectorRepeat {
    pub fn new(term: Term, n: u32) -> Result<Self> {
        let ok = yices! { yices_bvrepeat(term.into(), n) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorSignExtend }

impl BitVectorSignExtend {
    pub fn new(term: Term, n: u32) -> Result<Self> {
        let ok = yices! { yices_sign_extend(term.into(), n) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorZeroExtend }

impl BitVectorZeroExtend {
    pub fn new(term: Term, n: u32) -> Result<Self> {
        let ok = yices! { yices_zero_extend(term.into(), n) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorReduceAnd }

impl BitVectorReduceAnd {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_redand(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorReduceOr }

impl BitVectorReduceOr {
    pub fn new(term: Term) -> Result<Self> {
        let ok = yices! { yices_redor(term.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorReduceEqual }

impl BitVectorReduceEqual {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_redcomp(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorArray }

impl BitVectorArray {
    pub fn new<I>(terms: I) -> Result<Self>
    where
        I: IntoIterator<Item = Term>,
    {
        let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        let ok = yices! { yices_bvarray(terms.len() as u32, terms.as_ptr()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorEqualAtom }

impl BitVectorEqualAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bveq_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorNotEqualAtom }

impl BitVectorNotEqualAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvneq_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorLessThanAtom }

impl BitVectorLessThanAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvlt_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorLessThanEqualAtom }

impl BitVectorLessThanEqualAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvle_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorGreaterThanAtom }

impl BitVectorGreaterThanAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvgt_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorGreaterThanEqualAtom }

impl BitVectorGreaterThanEqualAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvge_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorSignedLessThanAtom }

impl BitVectorSignedLessThanAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvslt_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorSignedLessThanEqualAtom }

impl BitVectorSignedLessThanEqualAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvsle_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorSignedGreaterThanAtom }

impl BitVectorSignedGreaterThanAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvsgt_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

impl_term! { BitVectorSignedGreaterThanEqualAtom }

impl BitVectorSignedGreaterThanEqualAtom {
    pub fn new(left: Term, right: Term) -> Result<Self> {
        let ok = yices! { yices_bvsge_atom(left.into(), right.into()) };

        if ok < 0 {
            Err(Error::NewTerm)
        } else {
            Ok(Self { term: ok })
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Term {
    Uninterpreted(Uninterpreted),
    Variable(Variable),
    Constant(Constant),
    IfThenElse(IfThenElse),
    Equal(Equal),
    NotEqual(NotEqual),
    Distinct(Distinct),
    Application(Application),
    Tuple(Tuple),
    Select(Select),
    TupleUpdate(TupleUpdate),
    FunctionUpdate(FunctionUpdate),
    ForAll(ForAll),
    Exists(Exists),
    Lambda(Lambda),
    BooleanConstant(BooleanConstant),
    Not(Not),
    And(And),
    Or(Or),
    Xor(Xor),
    Iff(Iff),
    Implies(Implies),
    ArithmeticConstant(ArithmeticConstant),
    Add(Add),
    Sub(Sub),
    Neg(Neg),
    Mul(Mul),
    Square(Square),
    Power(Power),
    Division(Division),
    Sum(Sum),
    Product(Product),
    AbsoluteValue(AbsoluteValue),
    Floor(Floor),
    Ceiling(Ceiling),
    IntegerDivision(IntegerDivision),
    IntegerModulo(IntegerModulo),
    ArithmeticEqualAtom(ArithmeticEqualAtom),
    ArithmeticNotEqualAtom(ArithmeticNotEqualAtom),
    ArithmeticLessThanAtom(ArithmeticLessThanAtom),
    ArithmeticLessThanEqualAtom(ArithmeticLessThanEqualAtom),
    ArithmeticGreaterThanAtom(ArithmeticGreaterThanAtom),
    ArithmeticGreaterThanEqualAtom(ArithmeticGreaterThanEqualAtom),
    ArithmeticLessThanZeroAtom(ArithmeticLessThanZeroAtom),
    ArithmeticLessThanEqualZeroAtom(ArithmeticLessThanEqualZeroAtom),
    ArithmeticGreaterThanZeroAtom(ArithmeticGreaterThanZeroAtom),
    ArithmeticGreaterThanEqualZeroAtom(ArithmeticGreaterThanEqualZeroAtom),
    ArithmeticEqualZeroAtom(ArithmeticEqualZeroAtom),
    ArithmeticNotEqualZeroAtom(ArithmeticNotEqualZeroAtom),
    DividesAtom(DividesAtom),
    IsIntegerAtom(IsIntegerAtom),
    BitVectorConstant(BitVectorConstant),
    BitVectorAdd(BitVectorAdd),
    BitVectorSub(BitVectorSub),
    BitVectorNeg(BitVectorNeg),
    BitVectorMul(BitVectorMul),
    BitVectorSquare(BitVectorSquare),
    BitVectorPower(BitVectorPower),
    BitVectorSum(BitVectorSum),
    BitVectorProduct(BitVectorProduct),
    BitVectorDivision(BitVectorDivision),
    BitVectorRemainder(BitVectorRemainder),
    BitVectorSignedDivision(BitVectorSignedDivision),
    BitVectorSignedRemainder(BitVectorSignedRemainder),
    BitVectorSignedModulo(BitVectorSignedModulo),
    BitVectorNot(BitVectorNot),
    BitVectorAnd(BitVectorAnd),
    BitVectorOr(BitVectorOr),
    BitVectorXor(BitVectorXor),
    BitVectorNAnd(BitVectorNAnd),
    BitVectorNOr(BitVectorNOr),
    BitVectorXNor(BitVectorXNor),
    BitVectorShiftLeftFill0(BitVectorShiftLeftFill0),
    BitVectorShiftLeftFill1(BitVectorShiftLeftFill1),
    BitVectorShiftRightFill0(BitVectorShiftRightFill0),
    BitVectorShiftRightFill1(BitVectorShiftRightFill1),
    BitVectorArithmeticShiftRightConstant(BitVectorArithmeticShiftRightConstant),
    BitVectorRotateLeft(BitVectorRotateLeft),
    BitVectorRotateRight(BitVectorRotateRight),
    BitVectorShiftLeft(BitVectorShiftLeft),
    BitVectorShiftRight(BitVectorShiftRight),
    BitVectorArithmeticShiftRight(BitVectorArithmeticShiftRight),
    BitVectorExtract(BitVectorExtract),
    BitVectorBitExtract(BitVectorBitExtract),
    BitVectorConcatenate(BitVectorConcatenate),
    BitVectorRepeat(BitVectorRepeat),
    BitVectorSignExtend(BitVectorSignExtend),
    BitVectorZeroExtend(BitVectorZeroExtend),
    BitVectorReduceAnd(BitVectorReduceAnd),
    BitVectorReduceOr(BitVectorReduceOr),
    BitVectorReduceEqual(BitVectorReduceEqual),
    BitVectorArray(BitVectorArray),
    BitVectorEqualAtom(BitVectorEqualAtom),
    BitVectorNotEqualAtom(BitVectorNotEqualAtom),
    BitVectorLessThanAtom(BitVectorLessThanAtom),
    BitVectorLessThanEqualAtom(BitVectorLessThanEqualAtom),
    BitVectorGreaterThanAtom(BitVectorGreaterThanAtom),
    BitVectorGreaterThanEqualAtom(BitVectorGreaterThanEqualAtom),
    BitVectorSignedLessThanAtom(BitVectorSignedLessThanAtom),
    BitVectorSignedLessThanEqualAtom(BitVectorSignedLessThanEqualAtom),
    BitVectorSignedGreaterThanAtom(BitVectorSignedGreaterThanAtom),
    BitVectorSignedGreaterThanEqualAtom(BitVectorSignedGreaterThanEqualAtom),
    Any(Any),
}

impl From<Term> for term_t {
    fn from(value: Term) -> Self {
        match value {
            Term::Uninterpreted(term) => term.inner_term(),
            Term::Variable(term) => term.inner_term(),
            Term::Constant(term) => term.inner_term(),
            Term::IfThenElse(term) => term.inner_term(),
            Term::Equal(term) => term.inner_term(),
            Term::NotEqual(term) => term.inner_term(),
            Term::Distinct(term) => term.inner_term(),
            Term::Application(term) => term.inner_term(),
            Term::Tuple(term) => term.inner_term(),
            Term::Select(term) => term.inner_term(),
            Term::TupleUpdate(term) => term.inner_term(),
            Term::FunctionUpdate(term) => term.inner_term(),
            Term::ForAll(term) => term.inner_term(),
            Term::Exists(term) => term.inner_term(),
            Term::Lambda(term) => term.inner_term(),
            Term::BooleanConstant(term) => term.inner_term(),
            Term::Not(term) => term.inner_term(),
            Term::And(term) => term.inner_term(),
            Term::Or(term) => term.inner_term(),
            Term::Xor(term) => term.inner_term(),
            Term::Iff(term) => term.inner_term(),
            Term::Implies(term) => term.inner_term(),
            Term::ArithmeticConstant(term) => term.inner_term(),
            Term::Add(term) => term.inner_term(),
            Term::Sub(term) => term.inner_term(),
            Term::Neg(term) => term.inner_term(),
            Term::Mul(term) => term.inner_term(),
            Term::Square(term) => term.inner_term(),
            Term::Power(term) => term.inner_term(),
            Term::Division(term) => term.inner_term(),
            Term::Sum(term) => term.inner_term(),
            Term::Product(term) => term.inner_term(),
            Term::AbsoluteValue(term) => term.inner_term(),
            Term::Floor(term) => term.inner_term(),
            Term::Ceiling(term) => term.inner_term(),
            Term::IntegerDivision(term) => term.inner_term(),
            Term::IntegerModulo(term) => term.inner_term(),
            Term::ArithmeticEqualAtom(term) => term.inner_term(),
            Term::ArithmeticNotEqualAtom(term) => term.inner_term(),
            Term::ArithmeticLessThanAtom(term) => term.inner_term(),
            Term::ArithmeticLessThanEqualAtom(term) => term.inner_term(),
            Term::ArithmeticGreaterThanAtom(term) => term.inner_term(),
            Term::ArithmeticGreaterThanEqualAtom(term) => term.inner_term(),
            Term::ArithmeticLessThanZeroAtom(term) => term.inner_term(),
            Term::ArithmeticLessThanEqualZeroAtom(term) => term.inner_term(),
            Term::ArithmeticGreaterThanZeroAtom(term) => term.inner_term(),
            Term::ArithmeticGreaterThanEqualZeroAtom(term) => term.inner_term(),
            Term::ArithmeticEqualZeroAtom(term) => term.inner_term(),
            Term::ArithmeticNotEqualZeroAtom(term) => term.inner_term(),
            Term::DividesAtom(term) => term.inner_term(),
            Term::IsIntegerAtom(term) => term.inner_term(),
            Term::BitVectorConstant(term) => term.inner_term(),
            Term::BitVectorAdd(term) => term.inner_term(),
            Term::BitVectorSub(term) => term.inner_term(),
            Term::BitVectorNeg(term) => term.inner_term(),
            Term::BitVectorMul(term) => term.inner_term(),
            Term::BitVectorSquare(term) => term.inner_term(),
            Term::BitVectorPower(term) => term.inner_term(),
            Term::BitVectorSum(term) => term.inner_term(),
            Term::BitVectorProduct(term) => term.inner_term(),
            Term::BitVectorDivision(term) => term.inner_term(),
            Term::BitVectorRemainder(term) => term.inner_term(),
            Term::BitVectorSignedDivision(term) => term.inner_term(),
            Term::BitVectorSignedRemainder(term) => term.inner_term(),
            Term::BitVectorSignedModulo(term) => term.inner_term(),
            Term::BitVectorNot(term) => term.inner_term(),
            Term::BitVectorAnd(term) => term.inner_term(),
            Term::BitVectorOr(term) => term.inner_term(),
            Term::BitVectorXor(term) => term.inner_term(),
            Term::BitVectorNAnd(term) => term.inner_term(),
            Term::BitVectorNOr(term) => term.inner_term(),
            Term::BitVectorXNor(term) => term.inner_term(),
            Term::BitVectorShiftLeftFill0(term) => term.inner_term(),
            Term::BitVectorShiftLeftFill1(term) => term.inner_term(),
            Term::BitVectorShiftRightFill0(term) => term.inner_term(),
            Term::BitVectorShiftRightFill1(term) => term.inner_term(),
            Term::BitVectorArithmeticShiftRightConstant(term) => term.inner_term(),
            Term::BitVectorRotateLeft(term) => term.inner_term(),
            Term::BitVectorRotateRight(term) => term.inner_term(),
            Term::BitVectorShiftLeft(term) => term.inner_term(),
            Term::BitVectorShiftRight(term) => term.inner_term(),
            Term::BitVectorArithmeticShiftRight(term) => term.inner_term(),
            Term::BitVectorExtract(term) => term.inner_term(),
            Term::BitVectorBitExtract(term) => term.inner_term(),
            Term::BitVectorConcatenate(term) => term.inner_term(),
            Term::BitVectorRepeat(term) => term.inner_term(),
            Term::BitVectorSignExtend(term) => term.inner_term(),
            Term::BitVectorZeroExtend(term) => term.inner_term(),
            Term::BitVectorReduceAnd(term) => term.inner_term(),
            Term::BitVectorReduceOr(term) => term.inner_term(),
            Term::BitVectorReduceEqual(term) => term.inner_term(),
            Term::BitVectorArray(term) => term.inner_term(),
            Term::BitVectorEqualAtom(term) => term.inner_term(),
            Term::BitVectorNotEqualAtom(term) => term.inner_term(),
            Term::BitVectorLessThanAtom(term) => term.inner_term(),
            Term::BitVectorLessThanEqualAtom(term) => term.inner_term(),
            Term::BitVectorGreaterThanAtom(term) => term.inner_term(),
            Term::BitVectorGreaterThanEqualAtom(term) => term.inner_term(),
            Term::BitVectorSignedLessThanAtom(term) => term.inner_term(),
            Term::BitVectorSignedLessThanEqualAtom(term) => term.inner_term(),
            Term::BitVectorSignedGreaterThanAtom(term) => term.inner_term(),
            Term::BitVectorSignedGreaterThanEqualAtom(term) => term.inner_term(),
            Term::Any(term) => term.inner_term(),
        }
    }
}

impl From<&Term> for term_t {
    fn from(value: &Term) -> Self {
        (*value).into()
    }
}

impl From<term_t> for Term {
    fn from(value: term_t) -> Self {
        Term::Any(value.into())
    }
}

impl Term {
    pub fn is_arithmetic(&self) -> Result<bool> {
        let ok = yices! { yices_term_is_arithmetic(self.into()) };

        if ok < 0 {
            Err(Error::TermNotTypeOrTerm)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn is_bitvector(&self) -> Result<bool> {
        let ok = yices! { yices_term_is_bitvector(self.into()) };

        if ok < 0 {
            Err(Error::TermNotTypeOrTerm)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn is_boolean(&self) -> Result<bool> {
        let ok = yices! { yices_term_is_bool(self.into()) };

        if ok < 0 {
            Err(Error::TermNotTypeOrTerm)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn is_function(&self) -> Result<bool> {
        let ok = yices! { yices_term_is_function(self.into()) };

        if ok < 0 {
            Err(Error::TermNotTypeOrTerm)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn is_integer(&self) -> Result<bool> {
        let ok = yices! { yices_term_is_int(self.into()) };

        if ok < 0 {
            Err(Error::TermNotTypeOrTerm)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn is_real(&self) -> Result<bool> {
        let ok = yices! { yices_term_is_real(self.into()) };

        if ok < 0 {
            Err(Error::TermNotTypeOrTerm)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn is_scalar(&self) -> Result<bool> {
        let ok = yices! { yices_term_is_scalar(self.into()) };

        if ok < 0 {
            Err(Error::TermNotTypeOrTerm)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn is_tuple(&self) -> Result<bool> {
        let ok = yices! { yices_term_is_tuple(self.into()) };

        if ok < 0 {
            Err(Error::TermNotTypeOrTerm)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn is_ground(&self) -> Result<bool> {
        let ok = yices! { yices_term_is_ground(self.into()) };

        if ok < 0 {
            Err(Error::TermNotTypeOrTerm)
        } else {
            Ok(ok != 0)
        }
    }
}

impl Term {
    pub fn try_from_name(name: &str) -> Result<Term>
    where
        Self: Sized,
    {
        let c_str = CString::new(name).map_err(|e| Error::External(e.into()))?;
        let term = yices! { yices_get_term_by_name(c_str.as_ptr()) };

        if term == NULL_TERM {
            Err(Error::TermNotFound {
                name: name.to_string(),
            })
        } else {
            Ok(Term::Any(term.into()))
        }
    }
}

pub fn remove_term_name(name: &str) -> Result<()> {
    let c_str = CString::new(name).map_err(|e| Error::External(e.into()))?;
    yices! { yices_remove_term_name(c_str.as_ptr()) };

    Ok(())
}

impl FromStr for Term {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        let c_str = CString::new(s).map_err(|e| Error::External(e.into()))?;
        let term = yices! { yices_parse_term(c_str.as_ptr()) };

        if term == NULL_TERM {
            Err(Error::TermParse {
                term: s.to_string(),
            })
        } else {
            Ok(Term::Any(term.into()))
        }
    }
}

pub fn substitute<I>(vars: I, replacements: I, terms: I) -> Result<()>
where
    I: IntoIterator<Item = Term>,
{
    let vars: Vec<_> = vars.into_iter().map(|t| t.into()).collect();
    let replacements: Vec<_> = replacements.into_iter().map(|t| t.into()).collect();

    terms.into_iter().try_for_each(|term| {
            let ok = yices! { yices_subst_term(vars.len() as u32, vars.as_ptr(), replacements.as_ptr(), term.into()) };

            if ok < 0 {
                Err(Error::TermSubstitute)
            } else {
                Ok(())
            }
        })
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let c_str = yices_try! { yices_term_to_string(self.into(), u32::MAX, 1, 0) }
            .map_err(|_| std::fmt::Error)?;

        if c_str.is_null() {
            Err(std::fmt::Error)
        } else {
            let s = unsafe { CStr::from_ptr(c_str) };
            let s = s.to_str().map_err(|_| std::fmt::Error)?;
            write!(f, "{}", s)?;
            yices_try! { yices_free_string(c_str) }.map_err(|_| std::fmt::Error)
        }
    }
}
