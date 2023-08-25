use std::{ffi::CStr, fmt::Display};

use crate::{
    context::{ConfigurationParameter, Logic, Parameter},
    sys::{error_code, yices_clear_error, yices_error_code, yices_error_string},
};
use thiserror::Error;

#[derive(Error, Debug)]
pub struct Yices2Error {
    code: error_code,
    message: String,
}

impl Yices2Error {
    pub fn code(&self) -> error_code {
        self.code
    }

    pub fn message(&self) -> &str {
        &self.message
    }
}

impl Display for Yices2Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}: {}", self.code, self.message)
    }
}

impl From<error_code> for Yices2Error {
    fn from(code: error_code) -> Self {
        let message = unsafe {
            let cstr = yices_error_string();
            CStr::from_ptr(cstr).to_string_lossy().into_owned()
        };

        Self { code, message }
    }
}

#[derive(Error, Debug)]
pub enum Error {
    #[error("{source}")]
    Yices2 {
        #[from]
        source: Yices2Error,
    },
    #[error("Invalid name for logic: {logic}")]
    InvalidLogicName { logic: String },
    #[error("Invalid name for solver type: {solver_type}")]
    InvalidSolverTypeName { solver_type: String },
    #[error("Invalid name for uninterpreted function solver: {uf_solver}")]
    InvalidUninterpretedFunctionSolverName { uf_solver: String },
    #[error("Invalid name for bitvector solver: {bv_solver}")]
    InvalidBitVectorSolvername { bv_solver: String },
    #[error("Invalid name for array solver: {array_solver}")]
    InvalidArraySolverName { array_solver: String },
    #[error("Invalid name for arithmetic solver: {arith_solver}")]
    InvalidArithmeticSolverName { arith_solver: String },
    #[error("Invalid name for arithmetic fragment: {arith_fragment}")]
    InvalidArithmeticFragmentName { arith_fragment: String },
    #[error("Invalid name for configuration parameter: {name}")]
    InvalidConfigParameterName { name: String },
    #[error("Invalid value for configuration parameter: {value}")]
    InvalidConfigParameterValue { value: String },
    #[error("Invalid generalization mode: {mode}")]
    InvalidGeneralizationMode { mode: String },
    #[error("Failed to create a new parameter")]
    NewParameterFailed,
    #[error("Invalid parameter {param:?}")]
    InvalidParameter { param: Parameter },
    #[error("Failed to create a new config")]
    NewConfigFailed,
    #[error("Failed to set configuration parameter {param:?}")]
    SetConfigFailed { param: ConfigurationParameter },
    #[error("Failed to set default configuration for logic {logic:?}")]
    DefaultConfigForLogic { logic: Logic },
    #[error("Failed to create a new context")]
    NewContextFailed,
    #[error("Failed to push to context")]
    PushContextFailed,
    #[error("Failed to pop from context")]
    PopContextFailed,
    #[error("Failed to get model interpolant")]
    ModelInterpolantFailed,
    #[error("Failed to get model for context")]
    ModelForContextFailed,
    #[error("Failed to construct unsat core")]
    UnsatCoreContextFailed,
    #[error("Failed to create a new context with configuration")]
    NewContextWithConfigFailed,
    #[error("Failed to assert blocking")]
    AssertBlockingFailed,

    #[error("Failed to create model from mapping")]
    ModelFromMappingFailed,
    #[error("Term does not have boolean value")]
    TermNotBoolean,
    #[error("Term does not have 32-bit integer value")]
    TermNotInt32,
    #[error("Term does not have 64-bit integer value")]
    TermNotInt64,
    #[error("Term does not have 32-bit rational value")]
    TermNotRational32,
    #[error("Term does not have 64-bit rational value")]
    TermNotRational64,
    #[error("Term does not have double value")]
    TermNotDouble,
    #[error("Term does not have bitvector value")]
    TermNotBitVector,
    #[error("Term does not have scalar value")]
    TermNotScalar,
    #[error("Error checking formula truth value in model")]
    FormulasTrueError,
    #[error("Error getting value for term in model")]
    TermValueError,
    #[error("Value is not 32-bit integer")]
    ValueNotInt32,
    #[error("Value is not 64-bit integer")]
    ValueNotInt64,
    #[error("Value is not integer")]
    ValueNotInteger,
    #[error("Value is not 32-bit rational")]
    ValueNotRational32,
    #[error("Value is not 64-bit rational")]
    ValueNotRational64,
    #[error("Value is not bitvector or has no bitsize")]
    ValueNotBitVector,
    #[error("Could not get tuple arity for value")]
    ValueTupleArity,
    #[error("Could not get function arity for value")]
    ValueFunctionArity,
    #[error("Could not get mapping arity for value")]
    ValueMappingArity,
    #[error("Could not get function type for value")]
    ValueFunctionType,
    #[error("Could not get value as boolean")]
    ValueAsBoolean,
    #[error("Could not get value as 32-bit integer")]
    ValueAsInt32,
    #[error("Could not get value as 64-bit integer")]
    ValueAsInt64,
    #[error("Could not get value as 32-bit rational")]
    ValueAsRational32,
    #[error("Could not get value as 64-bit rational")]
    ValueAsRational64,
    #[error("Could not get value as double")]
    ValueAsDouble,
    #[error("Could not get value as bitvector")]
    ValueAsBitVector,
    #[error("Could not get value as scalar")]
    ValueAsScalar,
    #[error("Could not get value as tuple")]
    ValueAsTuple,
    #[error("Could not get value as function")]
    ValueAsFunction,
    #[error("Could not get value as mapping")]
    ValueAsMapping,
    #[error("Could not get value as term")]
    ValueAsTerm,
    #[error("Could not get values as terms")]
    ValuesAsTerms,
    #[error("Could not get support for term")]
    TermSupport,
    #[error("Could not get implicant for formula")]
    FormulaImplicant,
    #[error("Could not get implicant for formulas")]
    FormulasImplicant,

    #[error("Could not set term name to {name}")]
    TermSetName { name: String },
    #[error("Could not clear term name")]
    TermClearName,
    #[error("Could not incement reference count of term")]
    TermIncRef,
    #[error("Could not decrement reference count of term")]
    TermDecRef,
    #[error("Could not convert from term")]
    TermFromTerm,
    #[error("Error creating new term")]
    NewTerm,
    #[error("No term found with name {name}")]
    TermNotFound { name: String },
    #[error("Failed to parse term from string {term}")]
    TermParse { term: String },
    #[error("Failed to substritute terms")]
    TermSubstitute,
    #[error("Term is not a valid type or term")]
    TermNotTypeOrTerm,

    #[error("Unable to set name of type to {name}")]
    TypeSetName { name: String },
    #[error("Unable to clear name of type")]
    TypeClearName,
    #[error("Unable to convert from type")]
    TypeFromType,
    #[error("No type found with name {name}")]
    TypeNotFound { name: String },
    #[error("Failed to parse type from string {typ}")]
    TypeParse { typ: String },

    #[error("Failed to get number of children of type")]
    TypeNumChildren,
    #[error("Failed to get type of child of type with index {index}")]
    TypeChild { index: i32 },
    #[error("Failed to get type of type children")]
    TypeChildren,
    #[error("Failed to increment reference count of type")]
    TypeIncRef,
    #[error("Failed to decrement reference count of type")]
    TypeDecRef,
    #[error(transparent)]
    External(#[from] anyhow::Error),

    #[error("Failed to set boolean value in model")]
    ModelSetBoolean,
    #[error("Failed to set 32-bit integer value in model")]
    ModelSetInt32,
    #[error("Failed to set 64-bit integer value in model")]
    ModelSetInt64,
    #[error("Failed to set 32-bit unsigned integer value in model")]
    ModelSetUInt32,
    #[error("Failed to set 64-bit unsigned integer value in model")]
    ModelSetUInt64,
    #[error("Failed to set 32-bit rational value in model")]
    ModelSetRational32,
    #[error("Failed to set 64-bit rational value in model")]
    ModelSetRational64,
    #[error("Failed to set bitvector value in model from 32-bit integer")]
    ModelSetBitVectorInt32,
    #[error("Failed to set bitvector value in model from 64-bit integer")]
    ModelSetBitVectorInt64,
    #[error("Failed to set bitvector value in model from 32-bit unsigned integer")]
    ModelSetBitVectorUInt32,
    #[error("Failed to set bitvector value in model from 64-bit unsigned integer")]
    ModelSetBitVectorUInt64,
    #[error("Failed to set bitvector value from array")]
    ModelSetBitVectorFromArray,
}

pub fn error() -> Error {
    let code = unsafe { yices_error_code() };

    let err: Yices2Error = code.into();

    err.into()
}

pub fn clear_error() {
    unsafe { yices_clear_error() };
}

#[macro_export]
macro_rules! err {
    ($ok:expr) => {
        match $crate::error::error() {
            $crate::error::Error::Yices2 { source }
                if source.code() == $crate::sys::error_code::NO_ERROR =>
            {
                $crate::error::clear_error();
                Ok($ok)
            }
            err => Err(err),
        }
    };
}
