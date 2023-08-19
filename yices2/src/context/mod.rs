use std::{
    ffi::CString,
    ptr::{null, null_mut},
};

use yices2_sys::term_vector_t;

use crate::{
    model::Model,
    sys::{
        context_t, ctx_config_t, param_t, smt_status_t, yices_assert_blocking_clause,
        yices_assert_formulas, yices_check_context, yices_check_context_with_assumptions,
        yices_context_disable_option, yices_context_enable_option, yices_context_status,
        yices_default_config_for_logic, yices_default_params_for_context, yices_delete_term_vector,
        yices_free_config, yices_free_context, yices_free_param_record, yices_get_model,
        yices_get_model_interpolant, yices_get_unsat_core, yices_init_term_vector,
        yices_new_config, yices_new_context, yices_new_param_record, yices_pop, yices_push,
        yices_reset_context, yices_set_config, yices_set_param, yices_stop_search, NULL_TERM,
    },
    term::Term,
    yices, yices_try, Error, Result,
};

pub type Status = smt_status_t;

pub struct Config {
    config: *mut ctx_config_t,
}

impl Config {
    pub fn new() -> Result<Self> {
        let config = yices! { yices_new_config() };

        if config.is_null() {
            Err(Error::CtxInvalidConfig)
        } else {
            Ok(Self { config })
        }
    }

    pub fn set<S>(&self, key: S, value: S) -> Result<()>
    where
        S: AsRef<str>,
    {
        let key = CString::new(key.as_ref()).unwrap();
        let value = CString::new(value.as_ref()).unwrap();

        if yices! { yices_set_config(self.config, key.as_ptr(), value.as_ptr()) } < 0 {
            Err(Error::CtxInvalidConfig)
        } else {
            Ok(())
        }
    }

    pub fn default_for_logic<S>(&self, logic: S) -> Result<()>
    where
        S: AsRef<str>,
    {
        let logic = CString::new(logic.as_ref()).unwrap();
        let ok = yices! { yices_default_config_for_logic(self.config, logic.as_ptr()) };

        if ok < 0 {
            Err(Error::CtxInvalidConfig)
        } else {
            Ok(())
        }
    }
}

impl Drop for Config {
    fn drop(&mut self) {
        if yices_try! { yices_free_config(self.config) }.is_err() {
            panic!("Failed to free Yices context config");
        }
    }
}

pub struct Param {
    param: *mut param_t,
}

impl Param {
    pub fn new() -> Result<Self> {
        let param = yices! { yices_new_param_record() };

        if param.is_null() {
            Err(Error::CtxInvalidConfig)
        } else {
            Ok(Self { param })
        }
    }

    pub fn set<S>(&self, key: S, value: S) -> Result<()>
    where
        S: AsRef<str>,
    {
        let key = CString::new(key.as_ref()).unwrap();
        let value = CString::new(value.as_ref()).unwrap();

        if yices! { yices_set_param(self.param, key.as_ptr(), value.as_ptr()) } != 0 {
            Err(Error::CtxInvalidConfig)
        } else {
            Ok(())
        }
    }

    pub fn default_for_context(&self, context: &Context) -> Result<()> {
        yices! { yices_default_params_for_context(context.context, self.param) };
        Ok(())
    }
}

impl Drop for Param {
    fn drop(&mut self) {
        if yices_try! { yices_free_param_record(self.param) }.is_err() {
            panic!("Failed to free Yices context param");
        }
    }
}

pub struct Context {
    context: *mut context_t,
}

impl Context {
    pub fn new() -> Result<Self> {
        let context = yices! { yices_new_context(null()) };

        if context.is_null() {
            Err(Error::CtxInvalidConfig)
        } else {
            Ok(Self { context })
        }
    }

    pub fn with_config(config: &Config) -> Result<Self> {
        let context = yices! { yices_new_context(config.config) };

        if context.is_null() {
            Err(Error::CtxInvalidConfig)
        } else {
            Ok(Self { context })
        }
    }

    pub fn enable_option<S>(&self, option: S) -> Result<()>
    where
        S: AsRef<str>,
    {
        let option = CString::new(option.as_ref()).unwrap();

        yices! { yices_context_enable_option(self.context, option.as_ptr()) };

        Ok(())
    }

    pub fn disable_option<S>(&self, option: S) -> Result<()>
    where
        S: AsRef<str>,
    {
        let option = CString::new(option.as_ref()).unwrap();

        yices! { yices_context_disable_option(self.context, option.as_ptr()) };

        Ok(())
    }

    pub fn status(&self) -> Result<Status> {
        Ok(yices! { yices_context_status(self.context) })
    }

    pub fn assert<I>(&self, formulas: I) -> Result<()>
    where
        I: IntoIterator<Item = Term>,
    {
        let formulas: Vec<_> = formulas.into_iter().map(|t| t.into()).collect();

        yices! { yices_assert_formulas(self.context, formulas.len() as u32, formulas.as_ptr()) };

        Ok(())
    }

    pub fn check(&self) -> Result<Status> {
        self.check_with_params(None)
    }

    pub fn check_with_params(&self, params: Option<&Param>) -> Result<Status> {
        let params = params.map_or(null(), |p| p.param);

        Ok(yices! { yices_check_context(self.context, params) })
    }

    pub fn stop_search(&self) -> Result<()> {
        yices! { yices_stop_search(self.context) };

        Ok(())
    }

    pub fn reset(&self) -> Result<()> {
        yices! { yices_reset_context(self.context) };

        Ok(())
    }

    pub fn assert_blocking(&self) -> Result<()> {
        let ok = yices! { yices_assert_blocking_clause(self.context) };

        if ok != 0 {
            Err(Error::CtxInvalidConfig)
        } else {
            Ok(())
        }
    }

    pub fn push(&self) -> Result<()> {
        let ok = yices! { yices_push(self.context) };

        if ok != 0 {
            Err(Error::CtxInvalidConfig)
        } else {
            Ok(())
        }
    }

    pub fn pop(&self) -> Result<()> {
        let ok = yices! { yices_pop(self.context) };

        if ok != 0 {
            Err(Error::CtxInvalidConfig)
        } else {
            Ok(())
        }
    }

    pub fn check_with_assumptions<I>(&self, terms: I) -> Result<Status>
    where
        I: IntoIterator<Item = Term>,
    {
        self.check_with_assumptions_and_params(None, terms)
    }

    pub fn check_with_assumptions_and_params<I>(
        &self,
        params: Option<&Param>,
        terms: I,
    ) -> Result<Status>
    where
        I: IntoIterator<Item = Term>,
    {
        let params = params.map_or(null(), |p| p.param);
        let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

        Ok(
            yices! { yices_check_context_with_assumptions(self.context, params, terms.len() as u32, terms.as_ptr()) },
        )
    }

    pub fn unsat_core(&self) -> Result<Vec<Term>> {
        let mut tv = term_vector_t {
            capacity: 0,
            size: 0,
            data: null_mut(),
        };

        yices! { yices_init_term_vector(&mut tv as *mut term_vector_t) };

        let ok = yices! { yices_get_unsat_core(self.context, &mut tv as *mut term_vector_t) };

        if ok != 0 {
            yices! { yices_delete_term_vector(&mut tv as *mut term_vector_t) };
            Err(Error::CtxInvalidConfig)
        } else {
            let terms = (0..tv.size)
                .map(|i| unsafe { *tv.data.offset(i as isize) }.into())
                .collect();

            yices! { yices_delete_term_vector(&mut tv as *mut term_vector_t) };

            Ok(terms)
        }
    }

    pub fn interpolant(&self) -> Result<Term> {
        let term = yices! { yices_get_model_interpolant(self.context) };

        if term == NULL_TERM {
            Err(Error::CtxInvalidConfig)
        } else {
            Ok(term.into())
        }
    }

    pub fn model(&self) -> Result<Model> {
        Ok(Model::from(yices! { yices_get_model(self.context, 0) }))
    }

    pub fn model_with_eliminated(&self) -> Result<Model> {
        unimplemented!()
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        if yices_try! { yices_free_context(self.context) }.is_err() {
            panic!("Failed to free Yices context");
        }
    }
}
