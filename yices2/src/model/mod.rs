use std::{ffi::CStr, fmt::Display, ptr::null_mut};

use crate::{
    error::Error,
    sys::{
        model_t, term_vector_t, type_t, yices_delete_term_vector, yices_delete_yval_vector,
        yices_formulas_true_in_model, yices_free_model, yices_free_string, yices_get_bool_value,
        yices_get_bv_value, yices_get_double_value, yices_get_int32_value, yices_get_int64_value,
        yices_get_rational32_value, yices_get_rational64_value, yices_get_scalar_value,
        yices_get_value, yices_get_value_as_term, yices_implicant_for_formula,
        yices_implicant_for_formulas, yices_init_term_vector, yices_init_yval_vector,
        yices_model_collect_defined_terms, yices_model_from_map, yices_model_set_bool,
        yices_model_set_bv_from_array, yices_model_set_bv_int32, yices_model_set_bv_int64,
        yices_model_set_bv_uint32, yices_model_set_bv_uint64, yices_model_set_int32,
        yices_model_set_int64, yices_model_set_rational32, yices_model_set_rational64,
        yices_model_term_support, yices_model_to_string, yices_term_array_value,
        yices_term_bitsize, yices_val_bitsize, yices_val_expand_function, yices_val_expand_mapping,
        yices_val_expand_tuple, yices_val_function_arity, yices_val_function_type,
        yices_val_get_bool, yices_val_get_bv, yices_val_get_double, yices_val_get_int32,
        yices_val_get_int64, yices_val_get_rational32, yices_val_get_rational64,
        yices_val_get_scalar, yices_val_is_int32, yices_val_is_int64, yices_val_is_integer,
        yices_val_is_rational32, yices_val_is_rational64, yices_val_mapping_arity,
        yices_val_tuple_arity, yval_t, yval_vector_t, NULL_TERM,
    },
    term::Term,
    typ::Type,
    value::Value,
    yices, yices_try, Result,
};

pub struct Model {
    model: *mut model_t,
}

impl Model {
    pub fn from_map<I, T>(variables: I, constants: I) -> Result<Self>
    where
        I: IntoIterator<Item = T>,
        T: Into<Term>,
    {
        let variables: Vec<_> = variables
            .into_iter()
            .map(|t| {
                let t: Term = t.into();
                t.into()
            })
            .collect();
        let constants: Vec<_> = constants
            .into_iter()
            .map(|t| {
                let t: Term = t.into();
                t.into()
            })
            .collect();

        let model = yices! { yices_model_from_map(variables.len() as _, variables.as_ptr(), constants.as_ptr()) };

        if model.is_null() {
            Err(Error::ModelFromMappingFailed)
        } else {
            Ok(Self { model })
        }
    }

    pub fn collect_defined_terms(&self) -> Result<Vec<Term>> {
        let mut terms = term_vector_t {
            capacity: 0,
            size: 0,
            data: null_mut(),
        };

        yices! { yices_init_term_vector(&mut terms as *mut term_vector_t) };

        yices! { yices_model_collect_defined_terms(self.model, &mut terms as *mut term_vector_t) };

        let result = (0..terms.size)
            .map(|i| unsafe { *terms.data.offset(i as isize) }.into())
            .collect();

        yices! { yices_delete_term_vector(&mut terms as *mut term_vector_t) };

        Ok(result)
    }

    pub fn get_bool<T>(&self, term: T) -> Result<bool>
    where
        T: Into<Term>,
    {
        let mut result = 0;
        let term: Term = term.into();

        let ok = yices! { yices_get_bool_value(self.model, term.into(), &mut result as *mut i32) };

        if ok != 0 && ok != 1 {
            Err(Error::TermNotBoolean)
        } else {
            Ok(result != 0)
        }
    }

    pub fn get_int32<T>(&self, term: T) -> Result<i32>
    where
        T: Into<Term>,
    {
        let mut result = 0;
        let term: Term = term.into();

        let ok = yices! { yices_get_int32_value(self.model, term.into(), &mut result as *mut i32) };

        if ok < 0 {
            Err(Error::TermNotInt32)
        } else {
            Ok(result)
        }
    }

    pub fn get_int64<T>(&self, term: T) -> Result<i64>
    where
        T: Into<Term>,
    {
        let mut result = 0;
        let term: Term = term.into();

        let ok = yices! { yices_get_int64_value(self.model, term.into(), &mut result as *mut i64) };

        if ok < 0 {
            Err(Error::TermNotInt64)
        } else {
            Ok(result)
        }
    }

    pub fn get_rational32<T>(&self, term: T) -> Result<(i32, u32)>
    where
        T: Into<Term>,
    {
        let mut num = 0;
        let mut den = 0;
        let term: Term = term.into();

        let ok = yices! { yices_get_rational32_value(self.model, term.into(), &mut num as *mut _, &mut den as *mut _) };

        if ok < 0 {
            Err(Error::TermNotRational32)
        } else {
            Ok((num, den))
        }
    }

    pub fn get_rational64<T>(&self, term: T) -> Result<(i64, u64)>
    where
        T: Into<Term>,
    {
        let mut num = 0;
        let mut den = 0;
        let term: Term = term.into();

        let ok = yices! { yices_get_rational64_value(self.model, term.into(), &mut num as *mut _, &mut den as *mut _) };

        if ok < 0 {
            Err(Error::TermNotRational64)
        } else {
            Ok((num, den))
        }
    }

    pub fn get_double<T>(&self, term: T) -> Result<f64>
    where
        T: Into<Term>,
    {
        let mut result = 0.0;
        let term: Term = term.into();

        let ok =
            yices! { yices_get_double_value(self.model, term.into(), &mut result as *mut f64) };

        if ok < 0 {
            Err(Error::TermNotDouble)
        } else {
            Ok(result)
        }
    }

    pub fn get_bitvector<T>(&self, term: T) -> Result<Vec<bool>>
    where
        T: Into<Term>,
    {
        let term: Term = term.into();
        let size = yices! { yices_term_bitsize(term.into()) };

        let mut result = vec![0; size as usize];

        let ok = yices! { yices_get_bv_value(self.model, term.into(), result.as_mut_ptr()) };

        if ok < 0 {
            Err(Error::TermNotBitVector)
        } else {
            Ok(result.into_iter().map(|b| b != 0).collect())
        }
    }

    pub fn get_scalar<T>(&self, term: T) -> Result<i32>
    where
        T: Into<Term>,
    {
        let mut result = 0;
        let term: Term = term.into();

        let ok = yices! { yices_get_scalar_value(self.model, term.into(), &mut result as *mut _) };

        if ok < 0 {
            Err(Error::TermNotScalar)
        } else {
            Ok(result)
        }
    }

    pub fn formulas_true<I, T>(&self, formulas: I) -> Result<bool>
    where
        I: IntoIterator<Item = T>,
        T: Into<Term>,
    {
        let formulas: Vec<_> = formulas
            .into_iter()
            .map(|t| {
                let t: Term = t.into();
                t.into()
            })
            .collect();

        let ok = yices! { yices_formulas_true_in_model(self.model, formulas.len() as u32, formulas.as_ptr()) };

        if ok < 0 {
            Err(Error::FormulasTrueError)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn value<T>(&self, term: T) -> Result<Value>
    where
        T: Into<Term>,
    {
        let mut value = Value::default();
        let term = term.into();

        let ok =
            yices! { yices_get_value(self.model, term.into(), &mut value.value as *mut yval_t) };

        if ok < 0 {
            Err(Error::TermValueError)
        } else {
            Ok(value)
        }
    }

    pub fn value_is_i32(&self, value: &Value) -> Result<bool> {
        let ok = yices! { yices_val_is_int32(self.model, &value.value as *const yval_t) };

        if ok < 0 {
            Err(Error::ValueNotInt32)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn value_is_i64(&self, value: &Value) -> Result<bool> {
        let ok = yices! { yices_val_is_int64(self.model, &value.value as *const yval_t) };

        if ok < 0 {
            Err(Error::ValueNotInt64)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn value_is_rational32(&self, value: &Value) -> Result<bool> {
        let ok = yices! { yices_val_is_rational32(self.model, &value.value as *const yval_t) };

        if ok < 0 {
            Err(Error::ValueNotRational32)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn value_is_rational64(&self, value: &Value) -> Result<bool> {
        let ok = yices! { yices_val_is_rational64(self.model, &value.value as *const yval_t) };

        if ok < 0 {
            Err(Error::ValueNotRational64)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn value_is_integer(&self, value: &Value) -> Result<bool> {
        let ok = yices! { yices_val_is_integer(self.model, &value.value as *const yval_t) };

        if ok < 0 {
            Err(Error::ValueNotInteger)
        } else {
            Ok(ok != 0)
        }
    }

    pub fn value_bitsize(&self, value: &Value) -> Result<u32> {
        let size = yices! { yices_val_bitsize(self.model, &value.value as *const yval_t) };

        if size == 0 {
            Err(Error::ValueNotBitVector)
        } else {
            Ok(size)
        }
    }

    pub fn value_tuple_arity(&self, value: &Value) -> Result<u32> {
        let arity = yices! { yices_val_tuple_arity(self.model, &value.value as *const yval_t) };

        if arity == 0 {
            Err(Error::ValueTupleArity)
        } else {
            Ok(arity)
        }
    }

    pub fn value_function_arity(&self, value: &Value) -> Result<u32> {
        let arity = yices! { yices_val_function_arity(self.model, &value.value as *const yval_t) };

        if arity == 0 {
            Err(Error::ValueFunctionArity)
        } else {
            Ok(arity)
        }
    }

    pub fn value_mapping_arity(&self, value: &Value) -> Result<u32> {
        let arity = yices! { yices_val_mapping_arity(self.model, &value.value as *const yval_t) };

        if arity == 0 {
            Err(Error::ValueMappingArity)
        } else {
            Ok(arity)
        }
    }

    pub fn value_function_type(&self, value: &Value) -> Result<Term> {
        let term = yices! { yices_val_function_type(self.model, &value.value as *const yval_t) };

        if term < 0 {
            Err(Error::ValueFunctionType)
        } else {
            Ok(term.into())
        }
    }

    pub fn value_get_bool(&self, value: &Value) -> Result<bool> {
        let mut result = 0;

        let ok = yices! { yices_val_get_bool(self.model, &value.value as *const yval_t, &mut result as *mut i32) };

        if ok < 0 {
            Err(Error::ValueAsBoolean)
        } else {
            Ok(result != 0)
        }
    }

    pub fn value_get_int32(&self, value: &Value) -> Result<i32> {
        let mut result = 0;

        let ok = yices! { yices_val_get_int32(self.model, &value.value as *const yval_t, &mut result as *mut i32) };

        if ok < 0 {
            Err(Error::ValueAsInt32)
        } else {
            Ok(result)
        }
    }

    pub fn value_get_int64(&self, value: &Value) -> Result<i64> {
        let mut result = 0;

        let ok = yices! { yices_val_get_int64(self.model, &value.value as *const yval_t, &mut result as *mut i64) };

        if ok < 0 {
            Err(Error::ValueNotInt64)
        } else {
            Ok(result)
        }
    }

    pub fn value_get_rational32(&self, value: &Value) -> Result<(i32, u32)> {
        let mut num = 0;
        let mut den = 0;

        let ok = yices! { yices_val_get_rational32(self.model, &value.value as *const yval_t, &mut num as *mut _, &mut den as *mut _) };

        if ok < 0 {
            Err(Error::ValueNotRational32)
        } else {
            Ok((num, den))
        }
    }

    pub fn value_get_rational64(&self, value: &Value) -> Result<(i64, u64)> {
        let mut num = 0;
        let mut den = 0;

        let ok = yices! { yices_val_get_rational64(self.model, &value.value as *const yval_t, &mut num as *mut _, &mut den as *mut _) };

        if ok < 0 {
            Err(Error::ValueNotRational64)
        } else {
            Ok((num, den))
        }
    }

    pub fn value_get_double(&self, value: &Value) -> Result<f64> {
        let mut result = 0.0;

        let ok = yices! { yices_val_get_double(self.model, &value.value as *const yval_t, &mut result as *mut f64) };

        if ok < 0 {
            Err(Error::ValueAsDouble)
        } else {
            Ok(result)
        }
    }

    pub fn value_get_bv(&self, value: &Value) -> Result<Vec<bool>> {
        let size = yices! { yices_val_bitsize(self.model, &value.value as *const yval_t) };

        let mut result = vec![0; size as usize];

        let ok = yices! { yices_val_get_bv(self.model, &value.value as *const yval_t, result.as_mut_ptr()) };

        if ok < 0 {
            Err(Error::ValueAsBitVector)
        } else {
            Ok(result.into_iter().map(|b| b != 0).collect())
        }
    }

    pub fn value_get_scalar(&self, value: &Value) -> Result<(i32, Type)> {
        let mut result = 0;
        let mut type_result: type_t = 0;

        let ok = yices! { yices_val_get_scalar(self.model, &value.value as *const yval_t, &mut result as *mut _, &mut type_result as *mut _) };

        if ok < 0 {
            Err(Error::ValueAsScalar)
        } else {
            Ok((result, type_result.try_into()?))
        }
    }

    pub fn value_expand_tuple(&self, value: &Value) -> Result<Vec<Value>> {
        let arity = yices! { yices_val_tuple_arity(self.model, &value.value as *const yval_t) };
        let def = Value::default();

        let mut result = (0..arity as usize).map(|_| def.value).collect::<Vec<_>>();

        let ok = yices! { yices_val_expand_tuple(self.model, &value.value as *const yval_t, result.as_mut_ptr() as *mut yval_t) };

        if ok < 0 {
            Err(Error::ValueAsTuple)
        } else {
            Ok(result.iter().map(|v| v.into()).collect())
        }
    }

    pub fn value_expand_function(&self, value: &Value) -> Result<(Value, Vec<Value>)> {
        let mut def = Value::default();

        let mut result = yval_vector_t {
            capacity: 0,
            size: 0,
            data: null_mut(),
        };

        yices! { yices_init_yval_vector(&mut result as *mut yval_vector_t) };

        let ok = yices! { yices_val_expand_function(self.model, &value.value as *const yval_t, &mut def.value as *mut yval_t, &mut result as *mut yval_vector_t) };

        if ok < 0 {
            yices! { yices_delete_yval_vector(&mut result as *mut yval_vector_t) };
            Err(Error::ValueAsFunction)
        } else {
            let res = (0..result.size)
                .map(|i| unsafe { *result.data.offset(i as isize) }.into())
                .collect();

            yices! { yices_delete_yval_vector(&mut result as *mut yval_vector_t) };

            Ok((def, res))
        }
    }

    pub fn value_expand_mapping(&self, value: &Value) -> Result<(Vec<Value>, Value)> {
        let arity = yices! { yices_val_mapping_arity(self.model, &value.value as *const yval_t) };
        let mut def = Value::default();

        let mut result = vec![def.value; arity as usize];

        let ok = yices! { yices_val_expand_mapping(self.model, &value.value as *const yval_t, result.as_mut_ptr() as *mut yval_t, &mut def.value as *mut yval_t) };

        if ok < 0 {
            Err(Error::ValueAsMapping)
        } else {
            let res = result.iter().map(|v| v.into()).collect();

            Ok((res, def))
        }
    }

    pub fn value_as_term<T>(&self, value: T) -> Result<Term>
    where
        T: Into<Term>,
    {
        let value: Term = value.into();
        let term = yices! { yices_get_value_as_term(self.model, value.into()) };

        if term == NULL_TERM {
            Err(Error::ValueAsTerm)
        } else {
            Ok(term.into())
        }
    }

    pub fn values_as_terms<I>(&self, values: I) -> Result<Vec<Term>>
    where
        I: IntoIterator<Item = Term>,
    {
        let values: Vec<_> = values.into_iter().map(|t| t.into()).collect();

        let mut result = vec![0; values.len()];

        let ok = yices! { yices_term_array_value(self.model, values.len() as u32, values.as_ptr(), result.as_mut_ptr()) };

        if ok < 0 {
            Err(Error::ValuesAsTerms)
        } else {
            Ok(result.into_iter().map(|t| t.into()).collect())
        }
    }

    pub fn term_support<T>(&self, value: T) -> Result<Vec<Term>>
    where
        T: Into<Term>,
    {
        let value: Term = value.into();
        let mut result = term_vector_t {
            capacity: 0,
            size: 0,
            data: null_mut(),
        };

        yices! { yices_init_term_vector(&mut result as *mut term_vector_t) };

        let ok = yices! { yices_model_term_support(self.model, value.into(), &mut result as *mut term_vector_t) };

        if ok < 0 {
            yices! { yices_delete_term_vector(&mut result as *mut term_vector_t) };
            Err(Error::TermSupport)
        } else {
            let res = (0..result.size)
                .map(|i| unsafe { *result.data.offset(i as isize) }.into())
                .collect();

            yices! { yices_delete_term_vector(&mut result as *mut term_vector_t) };

            Ok(res)
        }
    }

    pub fn implicant_for_formula<T>(&self, value: T) -> Result<Vec<Term>>
    where
        T: Into<Term>,
    {
        let value: Term = value.into();
        let mut result = term_vector_t {
            capacity: 0,
            size: 0,
            data: null_mut(),
        };

        yices! { yices_init_term_vector(&mut result as *mut term_vector_t) };

        let ok = yices! { yices_implicant_for_formula(self.model, value.into(), &mut result as *mut term_vector_t) };

        if ok < 0 {
            yices! { yices_delete_term_vector(&mut result as *mut term_vector_t) };
            Err(Error::FormulaImplicant)
        } else {
            let res = (0..result.size)
                .map(|i| unsafe { *result.data.offset(i as isize) }.into())
                .collect();

            yices! { yices_delete_term_vector(&mut result as *mut term_vector_t) };

            Ok(res)
        }
    }

    pub fn implicant_for_formulas<I, T>(&self, values: I) -> Result<Vec<Term>>
    where
        I: IntoIterator<Item = T>,
        T: Into<Term>,
    {
        let values: Vec<_> = values
            .into_iter()
            .map(|t| {
                let t: Term = t.into();
                t.into()
            })
            .collect();

        let mut result = term_vector_t {
            capacity: 0,
            size: 0,
            data: null_mut(),
        };

        yices! { yices_init_term_vector(&mut result as *mut term_vector_t) };

        let ok = yices! { yices_implicant_for_formulas(self.model, values.len() as u32, values.as_ptr(), &mut result as *mut term_vector_t) };

        if ok < 0 {
            yices! { yices_delete_term_vector(&mut result as *mut term_vector_t) };
            Err(Error::FormulasImplicant)
        } else {
            let res = (0..result.size)
                .map(|i| unsafe { *result.data.offset(i as isize) }.into())
                .collect();

            yices! { yices_delete_term_vector(&mut result as *mut term_vector_t) };

            Ok(res)
        }
    }

    // TODO: Generalize

    pub fn set_bool<T>(&self, variable: T, value: bool) -> Result<()>
    where
        T: Into<Term>,
    {
        let variable: Term = variable.into();
        let value = if value { 1 } else { 0 };

        let ok = yices! { yices_model_set_bool(self.model, variable.into(), value) };

        if ok < 0 {
            Err(Error::ModelSetBoolean)
        } else {
            Ok(())
        }
    }

    pub fn set_int32<T>(&self, variable: T, value: i32) -> Result<()>
    where
        T: Into<Term>,
    {
        let variable: Term = variable.into();
        let ok = yices! { yices_model_set_int32(self.model, variable.into(), value) };

        if ok < 0 {
            Err(Error::ModelSetInt32)
        } else {
            Ok(())
        }
    }

    pub fn set_int64<T>(&self, variable: T, value: i64) -> Result<()>
    where
        T: Into<Term>,
    {
        let variable: Term = variable.into();
        let ok = yices! { yices_model_set_int64(self.model, variable.into(), value) };

        if ok < 0 {
            Err(Error::ModelSetInt64)
        } else {
            Ok(())
        }
    }

    pub fn set_rational32<T>(&self, variable: T, num: i32, den: u32) -> Result<()>
    where
        T: Into<Term>,
    {
        let variable: Term = variable.into();
        let ok = yices! { yices_model_set_rational32(self.model, variable.into(), num, den) };

        if ok < 0 {
            Err(Error::ModelSetRational32)
        } else {
            Ok(())
        }
    }

    pub fn set_rational64<T>(&self, variable: T, num: i64, den: u64) -> Result<()>
    where
        T: Into<Term>,
    {
        let variable: Term = variable.into();
        let ok = yices! { yices_model_set_rational64(self.model, variable.into(), num, den) };

        if ok < 0 {
            Err(Error::ModelSetRational64)
        } else {
            Ok(())
        }
    }

    pub fn set_bitvector_from_array<T>(&self, variable: T, value: &[bool]) -> Result<()>
    where
        T: Into<Term>,
    {
        let variable: Term = variable.into();
        let value: Vec<_> = value.iter().map(|b| if *b { 1 } else { 0 }).collect();

        let ok = yices! { yices_model_set_bv_from_array(self.model, variable.into(), value.len() as u32, value.as_ptr()) };

        if ok < 0 {
            Err(Error::ModelSetBitVectorFromArray)
        } else {
            Ok(())
        }
    }

    pub fn set_bitvector_int32<T>(&self, variable: T, value: i32) -> Result<()>
    where
        T: Into<Term>,
    {
        let variable: Term = variable.into();
        let ok = yices! { yices_model_set_bv_int32(self.model, variable.into(), value) };

        if ok < 0 {
            Err(Error::ModelSetBitVectorInt32)
        } else {
            Ok(())
        }
    }

    pub fn set_bitvector_uint32<T>(&self, variable: T, value: u32) -> Result<()>
    where
        T: Into<Term>,
    {
        let variable: Term = variable.into();
        let ok = yices! { yices_model_set_bv_uint32(self.model, variable.into(), value) };

        if ok < 0 {
            Err(Error::ModelSetBitVectorUInt32)
        } else {
            Ok(())
        }
    }

    pub fn set_bitvector_int64<T>(&self, variable: T, value: i64) -> Result<()>
    where
        T: Into<Term>,
    {
        let variable: Term = variable.into();
        let ok = yices! { yices_model_set_bv_int64(self.model, variable.into(), value) };

        if ok < 0 {
            Err(Error::ModelSetBitVectorInt64)
        } else {
            Ok(())
        }
    }

    pub fn set_bitvector_uint64(&self, variable: &Term, value: u64) -> Result<()> {
        let ok = yices! { yices_model_set_bv_uint64(self.model, variable.into(), value) };

        if ok < 0 {
            Err(Error::ModelSetBitVectorUInt64)
        } else {
            Ok(())
        }
    }
}

impl From<*mut model_t> for Model {
    fn from(model: *mut model_t) -> Self {
        Self { model }
    }
}

impl Drop for Model {
    fn drop(&mut self) {
        if yices_try! { yices_free_model(self.model) }.is_err() {
            panic!("Failed to free model");
        }
    }
}
impl Display for Model {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let c_str = yices_try! { yices_model_to_string(self.model, u32::MAX, 1, 0) }
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
