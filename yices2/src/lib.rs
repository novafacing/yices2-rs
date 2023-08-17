//! High-level Yices2 bindings

use crate::error::Error;
use crate::sys::{yices_exit, yices_init, yices_set_out_of_mem_callback};
use ctor::{ctor, dtor};

type Result<T> = std::result::Result<T, Error>;

#[no_mangle]
extern "C" fn oom_cb() {
    panic!("yices2: out of memory");
}

#[ctor]
/// Constructor: initialize yices at initialization time
fn init() {
    unsafe { yices_set_out_of_mem_callback(Some(oom_cb)) };
    unsafe { yices_init() };
}

#[dtor]
/// Destructor: clean up yices at exit time
fn exit() {
    unsafe { yices_exit() };
}
pub mod sys {
    pub use yices2_sys::*;

    #[macro_export]
    /// Make a call to the Yices2 API. This macro will automatically report any errors
    /// that occur as an [`Error`](crate::error::Error).
    macro_rules! yices_try {
        ($x:expr) => {
            unsafe {
                let res = $x;
                $crate::err!(res)
            }
        };
    }

    #[macro_export]
    /// Make a call to the Yices2 API. This macro will automatically report any errors
    /// that occur as an [`Error`](crate::error::Error), similar to [`yices_try!`](crate::yices_try!)
    /// but returns immediately if there is an error.
    macro_rules! yices {
        ($x:expr) => {
            unsafe {
                match $crate::yices_try!($x) {
                    Ok(ok) => ok,
                    Err(err) => {
                        return Err(err);
                    }
                }
            }
        };
    }
}

pub mod error {
    use crate::sys::{error_code, yices_clear_error, yices_error_code};
    use thiserror::Error;

    #[derive(Error, Debug)]
    pub enum Error {
        #[error("Everything is fine.")]
        NoError,
        #[error("Invalid type argument (not a valid index in the internal type table).")]
        InvalidType,
        #[error("Invalid term argument (not a valid index in the internal term table).")]
        InvalidTerm,
        #[error("Attempt to create a constant of uninterpreted type with a negative index, or a constant of scalar type with an index that’s larger than the type’s cardinality.")]
        InvalidConstantIndex,
        #[error("Unused")]
        InvalidVarIndex,
        #[error("Components of a tuple are indexed from 1 to N. This error code signals that an operation to extract or update a tuple component was given an index outside the interval [1 .. N].")]
        InvalidTupleIndex,
        #[error("The input to yices_parse_rational does not have the right format.")]
        InvalidRationalFormat,
        #[error("The input to yices_parse_float does not have the right format.")]
        InvalidFloatFormat,
        #[error("The input to yices_parse_bvbin does not have the right format.")]
        InvalidBvbinFormat,
        #[error("The input to yices_parse_bvhex does not have the right format.")]
        InvalidBvhexFormat,
        #[error("Invalid shift amount for a bitvector shift or rotate operation.")]
        InvalidBitshift,
        #[error("Invalid indices given to function yices_bvextract.")]
        InvalidBvextract,
        #[error("Invalid index given to function yices_bitextract.")]
        InvalidBitextract,
        #[error("Attempt to create a type or term of arity larger than YICES_MAX_ARITY")]
        TooManyArguments,
        #[error("Attempt to create a quantified term or a lambda term with more than YICES_MAX_VARS variables.")]
        TooManyVars,
        #[error(
            "Attempt to create a bitvector type or term with more than YICES_MAX_BVSIZE bits."
        )]
        MaxBvsizeExceeded,
        #[error("Attempt to create a polynomial of degree higher than YICES_MAX_DEGREE.")]
        DegreeOverflow,
        #[error("Zero divider in a rational constant.")]
        DivisionByZero,
        #[error("Bad integer argument: the function expects a positive argument.")]
        PosIntRequired,
        #[error("Bad integer argument: the function expects a non-negative argument.")]
        NonnegIntRequired,
        #[error("Bad type argument: the function expects either an uninterpreted type or a scalar type.")]
        ScalarOrUtypeRequired,
        #[error("Bad term argument: a term of function type is expected.")]
        FunctionRequired,
        #[error("Bad term argument: a term of tuple type is expected.")]
        TupleRequired,
        #[error("Bad term argument: a variable is expected. Some functions also report this error when they expect an argument that can be either a variable or an uninterpreted term.")]
        VariableRequired,
        #[error("Bad term argument: an arithmetic term (of type Int or Real) is expected.")]
        ArithtermRequired,
        #[error("Bad term argument: a bitvector term is expected.")]
        BitvectorRequired,
        #[error("Bad term argument: a term of scalar type is expected.")]
        ScalarTermRequired,
        #[error("Wrong number of arguments in a function application or function update.")]
        WrongNumberOfArguments,
        #[error("Type error in various term constructor.")]
        TypeMismatch,
        #[error("Error in functions that require terms of compatible types. The Yices manual explains what this means.")]
        IncompatibleTypes,
        #[error("Error in quantifier or lambda term constructors: the same variable occurs twice or more.")]
        DuplicateVariable,
        #[error("Error in a bitvector operation: the bitvector arguments have different sizes.")]
        IncompatibleBvsizes,
        #[error("Attempt to create a bitvector term of type (bitvector 0).")]
        EmptyBitvector,
        #[error("Invalid term: an arithmetic constant is expected.")]
        ArithconstantRequired,
        #[error("Invalid macro: a macro definition must be of the form (define-macro (name var-list) term).")]
        InvalidMacro,
        #[error("Invalid macro: a macro definition must be of the form (define-macro (name var-list) term).")]
        TooManyMacroParams,
        #[error("Error in a type definition: a type variable is expected.")]
        TypeVarRequired,
        #[error("Error in a type definition: the same type variable occurs twice or more.")]
        DuplicateTypeVar,
        #[error("Bad type parameter: a bitvector type is expected.")]
        BvtypeRequired,
        #[error("Error in reference counting: attempt to decrement the reference counter of a term when the counter is already zero.")]
        BadTermDecref,
        #[error("Error in reference counting: attempt to decrement the reference counter of a type when the counter is already zero.")]
        BadTypeDecref,
        #[error("Error in a type-exploration function.")]
        InvalidTypeOp,
        #[error("Error in a term-exploration function.")]
        InvalidTermOp,
        #[error("Error in the lexer.")]
        InvalidToken,
        #[error("Syntax error.")]
        SyntaxError,
        #[error("A name is not defined in the symbol table for types.")]
        UndefinedTypeName,
        #[error("A name is not defined in the symbol table for terms.")]
        UndefinedTermName,
        #[error("Attempt to redefine an existing type name.")]
        RedefinedTypeName,
        #[error("Attempt to redefine an existing term name.")]
        RedefinedTermName,
        #[error("A scalar-type definition contains the same element name twice (or more).")]
        DuplicateNameInScalar,
        #[error("Error in quantifiers or lambda term definition: the same variable name occurs twice or more.")]
        DuplicateVarName,
        #[error("Integer constant can’t be converted to a signed 32bit integer.")]
        IntegerOverflow,
        #[error("Rational constant provided when an integer is expected.")]
        IntegerRequired,
        #[error("Invalid argument: a rational constant is expected.")]
        RationalRequired,
        #[error("Error in a definition or local declaration: a symbol is expected.")]
        SymbolRequired,
        #[error("Error in a definition or declaration: a type is expected.")]
        TypeRequired,
        #[error("Attempt to divide by a non-constant arithmetic term.")]
        NonConstantDivisor,
        #[error("Error while parsing (bitvector size): the size is negative.")]
        NegativeBvsize,
        #[error("Error while parsing (mk-bv size value): the value is negative.")]
        InvalidBvconstant,
        #[error("Error in a term definition: the term value does not have the declared type.")]
        TypeMismatchInDef,
        #[error("Error in an arithmetic operation: an argument is not an arithmetic term.")]
        ArithError,
        #[error("Error in a bitvector operation: an argument is not a bitvector.")]
        BvarithError,
        #[error("An assertion contains free variables.")]
        CtxFreeVarInFormula,
        #[error("An assertion is not in a logic for which the context was configured.")]
        CtxLogicNotSupported,
        #[error(
            "An assertion contains uninterpreted functions but the context does not support them."
        )]
        CtxUfNotSupported,
        #[error(
            "An assertion contains arithmetic terms but the context does not support arithmetic."
        )]
        CtxArithNotSupported,
        #[error(
            "An assertion contains bitvector terms but the context does not support bitvectors."
        )]
        CtxBvNotSupported,
        #[error("An assertion contains array or function updates but the context does not support arrays.")]
        CtxArraysNotSupported,
        #[error("An assertion contains quantifiers but the context does not support them.")]
        CtxQuantifiersNotSupported,
        #[error("An assertion contains lambda terms but the context does not support them.")]
        CtxLambdasNotSupported,
        #[error("An assertion contains non-linear polynomials but the context supports only linear arithmetic.")]
        CtxNonlinearArithNotSupported,
        #[error("The context is configured for integer difference logic but an assertion is not in this fragment.")]
        CtxFormulaNotIdl,
        #[error("The context is configured for real difference logic but an assertion is not in this fragment.")]
        CtxFormulaNotRdl,
        #[error("An internal limit of the arithmetic solver is exceeded.")]
        CtxTooManyArithVars,
        #[error("An internal limit of the arithmetic solver is exceeded.")]
        CtxTooManyArithAtoms,
        #[error("An internal limit of the bitvector solver is exceeded.")]
        CtxTooManyBvVars,
        #[error("An internal limit of the bitvector solver is exceeded.")]
        CtxTooManyBvAtoms,
        #[error("General error reported by the arithmetic solver.")]
        CtxArithSolverException,
        #[error("General error reported by the bitvector solver.")]
        CtxBvSolverException,
        #[error("General error reported by the array/function solver.")]
        CtxArraySolverException,
        #[error(
            "An assertion contains terms of scalar type but the context does not support them."
        )]
        CtxScalarNotSupported,
        #[error(
            "An assertion contains terms of tuple type but the context does not support them."
        )]
        CtxTupleNotSupported,
        #[error("An assertion contains terms of uninterpreted type but the context does not support them.")]
        CtxUtypeNotSupported,
        #[error(
            "An assertion contains terms of function type but the context does not support them."
        )]
        CtxHighOrderFunNotSupported,
        #[error("Invalid operation on a context: the context is in a state that does not allow the operation to be performed.")]
        CtxInvalidOperation,
        #[error("Invalid operation on a context: the context is not configured to support this operation.")]
        CtxOperationNotSupported,
        #[error(
            "A delegate name is not recognized. See yices_check_formula and yices_check_formulas ."
        )]
        CtxUnknownDelegate,
        #[error("Attempt to use a delegate that was not included in the Yices library at compilation time.")]
        CtxDelegateNotAvailable,
        #[error("Error in existential quantifier elimination: the formula contains uninterpreted functions.")]
        CtxEfAssertionsContainUf,
        #[error("Error in existential quantifier elimination: the formula contains quantifiers.")]
        CtxEfNotExistsForall,
        #[error("Error in existential quantifier elimination: the formula contains lambdas.")]
        CtxEfHighOrderVars,
        #[error("Error in existential quantifier elimination: the formula contains lambdas.")]
        CtxEfInternalError,
        #[error("Reported by yices_new_context if the requested configuration is not supported. This means that the combination of solvers does not implement the set of features requested.")]
        CtxInvalidConfig,
        #[error("Invalid parameter name.")]
        CtxUnknownParameter,
        #[error("Invalid value for a parameter.")]
        CtxInvalidParameterValue,
        #[error("A logic name is not recognized.")]
        CtxUnknownLogic,
        #[error("The model does not assign a value to the specified term.")]
        EvalUnknownTerm,
        #[error("A term value cannot be computed because the term contains free variables.")]
        EvalFreevarInTerm,
        #[error("A term value cannot be computed because the term contains quantifiers.")]
        EvalQuantifier,
        #[error("A term value cannot be computed because the term contains lambdas.")]
        EvalLambda,
        #[error("The value of a term is known but it does not fit in the given variable. For example, yices_get_int32_value will report this error if the term value does not fit in a signed, 32bit integer.")]
        EvalOverflow,
        #[error("A term value cannot be computed for another reason.")]
        EvalFailed,
        #[error("Failed to convert the value of a term in a model into a constant term. This error can be reported by yices_get_value_as_term and yices_term_array_value.")]
        EvalConversionFailed,
        #[error("Error reported by yices_implicant_for_formula and variants when the input formula is false in the model.")]
        EvalNoImplicant,
        #[error("Reported by function yices_get_algebraic_number_value when the library is compiled without MCSAT support.")]
        EvalNotSupported,
        #[error("Invalid map for yices_model_from_map: an element in the domain is not an uninterpreted term.")]
        MdlUnintRequired,
        #[error(
            "Invalid map for yices_model_from_map: an element in the range is not a constant term."
        )]
        MdlConstantRequired,
        #[error("Invalid map for yices_model_from_map: the domain contains duplicate terms.")]
        MdlDuplicateVar,
        #[error(
            "Invalid map for yices_model_from_map: one element in the domain has a function type."
        )]
        MdlFtypeNotAllowed,
        #[error("Function yices_model_from_map failed for some other reason.")]
        MdlConstructionFailed,
        #[error("Invalid operation on a model: the model does not contain a value for the specified variable.")]
        MdlNonnegIntRequired,
        #[error("Invalid operation on a value descriptor (node in the model DAG).")]
        YvalInvalidOp,
        #[error("The value of a leaf node does not fit in the given input variable.")]
        YvalOverflow,
        #[error("Reported by function yices_val_get_algebraic_number when the library is compiled without MCSAT support.")]
        YvalNotSupported,
        #[error("Model generalization failed because variables to eliminate have a type that’s not supported.")]
        MdlGenTypeNotSupported,
        #[error("Model generalization failed because the input formula(s) include non-linear arithmetic.")]
        MdlGenNonlinear,
        #[error("Model generalization failed for some other reason.")]
        MdlGenFailed,
        #[error("Model generalization failed because the input formula(s) include terms that are not supported.")]
        MdlGenUnsupportedTerm,
        #[error("A formula asserted in the MCSAT solver is not in a theory that this solver can process.")]
        McsatErrorUnsupportedTheory,
        #[error("A formula asserted in the MCSAT solver contains an assumption term that is not supported.")]
        McsatErrorAssumptionTermNotSupported,
        #[error("Error when attempting to write to a stream. This error can be reported by the pretty-printing functions if they fail to write to the specified file. If this error is reported, then system variables and functions (e.g., errno, perror, strerror) can be used for diagnosis.")]
        OutputError,
        #[error("Catch-all code for any other error. If you ever see this error code, please report a bug at https://github.com/SRI-CSL/yices2")]
        InternalException,
    }

    impl From<error_code> for Error {
        fn from(value: error_code) -> Self {
            match value {
                error_code::NO_ERROR => Self::NoError,
                error_code::INVALID_TYPE => Self::InvalidType,
                error_code::INVALID_TERM => Self::InvalidTerm,
                error_code::INVALID_CONSTANT_INDEX => Self::InvalidConstantIndex,
                error_code::INVALID_VAR_INDEX => Self::InvalidVarIndex,
                error_code::INVALID_TUPLE_INDEX => Self::InvalidTupleIndex,
                error_code::INVALID_RATIONAL_FORMAT => Self::InvalidRationalFormat,
                error_code::INVALID_FLOAT_FORMAT => Self::InvalidFloatFormat,
                error_code::INVALID_BVBIN_FORMAT => Self::InvalidBvbinFormat,
                error_code::INVALID_BVHEX_FORMAT => Self::InvalidBvhexFormat,
                error_code::INVALID_BITSHIFT => Self::InvalidBitshift,
                error_code::INVALID_BVEXTRACT => Self::InvalidBvextract,
                error_code::INVALID_BITEXTRACT => Self::InvalidBitextract,
                error_code::TOO_MANY_ARGUMENTS => Self::TooManyArguments,
                error_code::TOO_MANY_VARS => Self::TooManyVars,
                error_code::MAX_BVSIZE_EXCEEDED => Self::MaxBvsizeExceeded,
                error_code::DEGREE_OVERFLOW => Self::DegreeOverflow,
                error_code::DIVISION_BY_ZERO => Self::DivisionByZero,
                error_code::POS_INT_REQUIRED => Self::PosIntRequired,
                error_code::NONNEG_INT_REQUIRED => Self::NonnegIntRequired,
                error_code::SCALAR_OR_UTYPE_REQUIRED => Self::ScalarOrUtypeRequired,

                error_code::FUNCTION_REQUIRED => Self::FunctionRequired,
                error_code::TUPLE_REQUIRED => Self::TupleRequired,
                error_code::VARIABLE_REQUIRED => Self::VariableRequired,
                error_code::ARITHTERM_REQUIRED => Self::ArithtermRequired,
                error_code::BITVECTOR_REQUIRED => Self::BitvectorRequired,
                error_code::SCALAR_TERM_REQUIRED => Self::ScalarTermRequired,
                error_code::WRONG_NUMBER_OF_ARGUMENTS => Self::WrongNumberOfArguments,
                error_code::TYPE_MISMATCH => Self::TypeMismatch,
                error_code::INCOMPATIBLE_TYPES => Self::IncompatibleTypes,
                error_code::DUPLICATE_VARIABLE => Self::DuplicateVariable,
                error_code::INCOMPATIBLE_BVSIZES => Self::IncompatibleBvsizes,
                error_code::EMPTY_BITVECTOR => Self::EmptyBitvector,
                error_code::ARITHCONSTANT_REQUIRED => Self::ArithconstantRequired,
                error_code::INVALID_MACRO => Self::InvalidMacro,
                error_code::TOO_MANY_MACRO_PARAMS => Self::TooManyMacroParams,
                error_code::TYPE_VAR_REQUIRED => Self::TypeVarRequired,
                error_code::DUPLICATE_TYPE_VAR => Self::DuplicateTypeVar,
                error_code::BVTYPE_REQUIRED => Self::BvtypeRequired,
                error_code::BAD_TERM_DECREF => Self::BadTermDecref,
                error_code::BAD_TYPE_DECREF => Self::BadTypeDecref,
                error_code::INVALID_TYPE_OP => Self::InvalidTypeOp,
                error_code::INVALID_TERM_OP => Self::InvalidTermOp,
                error_code::INVALID_TOKEN => Self::InvalidToken,
                error_code::SYNTAX_ERROR => Self::SyntaxError,
                error_code::UNDEFINED_TYPE_NAME => Self::UndefinedTypeName,
                error_code::UNDEFINED_TERM_NAME => Self::UndefinedTermName,
                error_code::REDEFINED_TYPE_NAME => Self::RedefinedTypeName,
                error_code::REDEFINED_TERM_NAME => Self::RedefinedTermName,
                error_code::DUPLICATE_NAME_IN_SCALAR => Self::DuplicateNameInScalar,
                error_code::DUPLICATE_VAR_NAME => Self::DuplicateVarName,
                error_code::INTEGER_OVERFLOW => Self::IntegerOverflow,
                error_code::INTEGER_REQUIRED => Self::IntegerRequired,
                error_code::RATIONAL_REQUIRED => Self::RationalRequired,
                error_code::SYMBOL_REQUIRED => Self::SymbolRequired,
                error_code::TYPE_REQUIRED => Self::TypeRequired,
                error_code::NON_CONSTANT_DIVISOR => Self::NonConstantDivisor,
                error_code::NEGATIVE_BVSIZE => Self::NegativeBvsize,
                error_code::INVALID_BVCONSTANT => Self::InvalidBvconstant,
                error_code::TYPE_MISMATCH_IN_DEF => Self::TypeMismatchInDef,
                error_code::ARITH_ERROR => Self::ArithError,
                error_code::BVARITH_ERROR => Self::BvarithError,
                error_code::CTX_FREE_VAR_IN_FORMULA => Self::CtxFreeVarInFormula,
                error_code::CTX_LOGIC_NOT_SUPPORTED => Self::CtxLogicNotSupported,
                error_code::CTX_UF_NOT_SUPPORTED => Self::CtxUfNotSupported,
                error_code::CTX_ARITH_NOT_SUPPORTED => Self::CtxArithNotSupported,
                error_code::CTX_BV_NOT_SUPPORTED => Self::CtxBvNotSupported,
                error_code::CTX_ARRAYS_NOT_SUPPORTED => Self::CtxArraysNotSupported,
                error_code::CTX_QUANTIFIERS_NOT_SUPPORTED => Self::CtxQuantifiersNotSupported,
                error_code::CTX_LAMBDAS_NOT_SUPPORTED => Self::CtxLambdasNotSupported,
                error_code::CTX_NONLINEAR_ARITH_NOT_SUPPORTED => {
                    Self::CtxNonlinearArithNotSupported
                }
                error_code::CTX_FORMULA_NOT_IDL => Self::CtxFormulaNotIdl,
                error_code::CTX_FORMULA_NOT_RDL => Self::CtxFormulaNotRdl,
                error_code::CTX_TOO_MANY_ARITH_VARS => Self::CtxTooManyArithVars,
                error_code::CTX_TOO_MANY_ARITH_ATOMS => Self::CtxTooManyArithAtoms,
                error_code::CTX_TOO_MANY_BV_VARS => Self::CtxTooManyBvVars,
                error_code::CTX_TOO_MANY_BV_ATOMS => Self::CtxTooManyBvAtoms,
                error_code::CTX_ARITH_SOLVER_EXCEPTION => Self::CtxArithSolverException,
                error_code::CTX_BV_SOLVER_EXCEPTION => Self::CtxBvSolverException,
                error_code::CTX_ARRAY_SOLVER_EXCEPTION => Self::CtxArraySolverException,
                error_code::CTX_SCALAR_NOT_SUPPORTED => Self::CtxScalarNotSupported,
                error_code::CTX_TUPLE_NOT_SUPPORTED => Self::CtxTupleNotSupported,
                error_code::CTX_UTYPE_NOT_SUPPORTED => Self::CtxUtypeNotSupported,
                error_code::CTX_HIGH_ORDER_FUN_NOT_SUPPORTED => Self::CtxHighOrderFunNotSupported,
                error_code::CTX_INVALID_OPERATION => Self::CtxInvalidOperation,
                error_code::CTX_OPERATION_NOT_SUPPORTED => Self::CtxOperationNotSupported,
                error_code::CTX_UNKNOWN_DELEGATE => Self::CtxUnknownDelegate,
                error_code::CTX_DELEGATE_NOT_AVAILABLE => Self::CtxDelegateNotAvailable,
                error_code::CTX_EF_ASSERTIONS_CONTAIN_UF => Self::CtxEfAssertionsContainUf,
                error_code::CTX_EF_NOT_EXISTS_FORALL => Self::CtxEfNotExistsForall,
                error_code::CTX_EF_HIGH_ORDER_VARS => Self::CtxEfHighOrderVars,
                error_code::CTX_EF_INTERNAL_ERROR => Self::CtxEfInternalError,
                error_code::CTX_INVALID_CONFIG => Self::CtxInvalidConfig,
                error_code::CTX_UNKNOWN_PARAMETER => Self::CtxUnknownParameter,
                error_code::CTX_INVALID_PARAMETER_VALUE => Self::CtxInvalidParameterValue,
                error_code::CTX_UNKNOWN_LOGIC => Self::CtxUnknownLogic,
                error_code::EVAL_UNKNOWN_TERM => Self::EvalUnknownTerm,
                error_code::EVAL_FREEVAR_IN_TERM => Self::EvalFreevarInTerm,
                error_code::EVAL_QUANTIFIER => Self::EvalQuantifier,
                error_code::EVAL_LAMBDA => Self::EvalLambda,
                error_code::EVAL_OVERFLOW => Self::EvalOverflow,
                error_code::EVAL_FAILED => Self::EvalFailed,
                error_code::EVAL_CONVERSION_FAILED => Self::EvalConversionFailed,
                error_code::EVAL_NO_IMPLICANT => Self::EvalNoImplicant,
                error_code::EVAL_NOT_SUPPORTED => Self::EvalNotSupported,
                error_code::MDL_UNINT_REQUIRED => Self::MdlUnintRequired,
                error_code::MDL_CONSTANT_REQUIRED => Self::MdlConstantRequired,
                error_code::MDL_DUPLICATE_VAR => Self::MdlDuplicateVar,
                error_code::MDL_FTYPE_NOT_ALLOWED => Self::MdlFtypeNotAllowed,
                error_code::MDL_CONSTRUCTION_FAILED => Self::MdlConstructionFailed,
                error_code::MDL_NONNEG_INT_REQUIRED => Self::MdlNonnegIntRequired,
                error_code::YVAL_INVALID_OP => Self::YvalInvalidOp,
                error_code::YVAL_OVERFLOW => Self::YvalOverflow,
                error_code::YVAL_NOT_SUPPORTED => Self::YvalNotSupported,
                error_code::MDL_GEN_TYPE_NOT_SUPPORTED => Self::MdlGenTypeNotSupported,
                error_code::MDL_GEN_NONLINEAR => Self::MdlGenNonlinear,
                error_code::MDL_GEN_FAILED => Self::MdlGenFailed,
                error_code::MDL_GEN_UNSUPPORTED_TERM => Self::MdlGenUnsupportedTerm,
                error_code::MCSAT_ERROR_UNSUPPORTED_THEORY => Self::McsatErrorUnsupportedTheory,
                error_code::MCSAT_ERROR_ASSUMPTION_TERM_NOT_SUPPORTED => {
                    Self::McsatErrorAssumptionTermNotSupported
                }
                error_code::OUTPUT_ERROR => Self::OutputError,
                error_code::INTERNAL_EXCEPTION => Self::InternalException,
            }
        }
    }

    pub fn error() -> Error {
        Error::from(unsafe { yices_error_code() })
    }

    pub fn clear_error() {
        unsafe { yices_clear_error() };
    }

    #[macro_export]
    macro_rules! err {
        ($ok:expr) => {
            match $crate::error::error() {
                $crate::error::Error::NoError => Ok($ok),
                err => {
                    $crate::error::clear_error();
                    Err(err)
                }
            }
        };
    }
}

pub mod typ {

    use paste::paste;

    use crate::{
        error::Error,
        sys::{
            type_t, type_vector_t, yices_bool_type, yices_bv_type, yices_bvtype_size,
            yices_compatible_types, yices_delete_type_vector, yices_function_type,
            yices_init_type_vector, yices_int_type, yices_new_scalar_type,
            yices_new_uninterpreted_type, yices_real_type, yices_scalar_type_card,
            yices_test_subtype, yices_tuple_type, yices_type_child, yices_type_children,
            yices_type_is_bitvector, yices_type_is_bool, yices_type_is_function, yices_type_is_int,
            yices_type_is_real, yices_type_is_scalar, yices_type_is_tuple,
            yices_type_is_uninterpreted, yices_type_num_children, NULL_TYPE,
        },
        yices, yices_try, Result,
    };

    pub trait InnerType {
        fn inner(&self) -> type_t;
    }

    pub trait SubType: InnerType {
        fn subtype<S>(&self, other: &S) -> Result<bool>
        where
            S: SubType + InnerType,
            Self: Sized,
        {
            Ok(yices! { yices_test_subtype(self.inner(), other.inner()) } != 0)
        }
    }
    pub trait CompatibleType: InnerType {
        fn compatible<S>(&self, other: &S) -> Result<bool>
        where
            S: CompatibleType + InnerType,
            Self: Sized,
        {
            Ok(yices! { yices_compatible_types(self.inner(), other.inner()) } != 0)
        }
    }

    pub trait ChildType: InnerType {
        /// Get the number of children of a type. Only valid for Function and Tuple types
        fn num_children(&self) -> Result<i32>
        where
            Self: Sized,
        {
            Ok(yices! { yices_type_num_children(self.inner()) })
        }

        /// Get a child of a type. Only valid for Function and Tuple types
        fn child(&self, index: i32) -> Result<Type>
        where
            Self: Sized,
        {
            let typ = yices! { yices_type_child(self.inner(), index) };

            if typ == NULL_TYPE {
                Err(Error::InvalidType)
            } else {
                Type::try_from(typ)
            }
        }

        /// Get the child types of a type. Only valid for Function and Tuple types
        ///
        /// Returns the most general type of the children, which can be cast back to the
        /// original type.
        fn children(&self) -> Result<Vec<Type>>
        where
            Self: Sized,
        {
            let mut vec = type_vector_t {
                size: 0,
                capacity: 0,
                data: std::ptr::null_mut(),
            };

            yices! { yices_init_type_vector(&mut vec as *mut type_vector_t) };

            if yices! { yices_type_children(self.inner(), &mut vec as *mut type_vector_t) } == -1 {
                yices! { yices_delete_type_vector(&mut vec as *mut type_vector_t) };

                Err(Error::InvalidType)
            } else {
                let mut types = Vec::with_capacity(vec.size as usize);

                (0..vec.size).try_for_each(|i| {
                    let typ = unsafe { *vec.data.offset(i as isize) };

                    if typ == NULL_TYPE {
                        Err(Error::InvalidType)
                    } else {
                        types.push(Type::try_from(typ)?);
                        Ok(())
                    }
                })?;

                yices! { yices_delete_type_vector(&mut vec as *mut type_vector_t) };

                Ok(types)
            }
        }
    }

    /// Implement a type
    ///
    /// # Example
    ///
    /// impl_type! { Bool, bool };
    macro_rules! impl_type {
        ($id:ident) => {
            impl_type! { $id, $id }
        };
        ($id:ident, $abbrev:ident) => {
            paste! {
                #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
                pub struct $id {
                    typ: type_t,
                }

                impl $id {
                    pub fn [<is_ $id:lower>](&self) -> Result<bool> {
                        Ok(yices! { [<yices_type_is_ $abbrev:lower>](self.inner()) } != 0)
                    }
                }

                impl InnerType for $id {
                    fn inner(&self) -> type_t {
                        self.typ
                    }
                }

                impl SubType for $id {}
                impl CompatibleType for $id {}

                impl From<type_t> for $id {
                    fn from(typ: type_t) -> Self {
                        Self { typ }
                    }
                }

                impl From<&type_t> for $id {
                    fn from(typ: &type_t) -> Self {
                        Self { typ: *typ }
                    }
                }

                impl From<$id> for type_t {
                    fn from(typ: $id) -> Self {
                        typ.inner()
                    }
                }

                impl From<&$id> for type_t {
                    fn from(typ: &$id) -> Self {
                        typ.inner()
                    }
                }

                impl TryFrom<Type> for $id {
                    type Error = Error;

                    fn try_from(typ: Type) -> Result<Self> {
                        match typ {
                            Type::$id(typ) => Ok(typ),
                            _ => Err(Error::InvalidType),
                        }
                    }
                }

                impl TryFrom<&Type> for $id {
                    type Error = Error;

                    fn try_from(typ: &Type) -> Result<Self> {
                        match typ {
                            Type::$id(typ) => Ok(*typ),
                            _ => Err(Error::InvalidType),
                        }
                    }
                }

                impl From<$id> for Type {
                    fn from(typ: $id) -> Self {
                        Self::$id(typ)
                    }
                }
            }
        };
    }

    impl_type! { Bool }

    impl Bool {
        fn new() -> Result<Self> {
            Ok(Self {
                typ: yices! { yices_bool_type() },
            })
        }
    }

    impl_type! { Integer, int }

    impl Integer {
        /// Return the integer type
        pub fn new() -> Result<Self> {
            Ok(Self {
                typ: yices! { yices_int_type() },
            })
        }
    }

    impl_type! { Real }

    impl Real {
        /// Return the real type
        pub fn new() -> Result<Self> {
            Ok(Self {
                typ: yices! { yices_real_type() },
            })
        }
    }

    impl_type! { BitVector }

    impl BitVector {
        /// Construct or return the bitvector type for a bitvector with a bit-width of
        /// `size`.
        pub fn new(size: u32) -> Result<Self> {
            Ok(Self {
                typ: yices! { yices_bv_type(size) },
            })
        }

        /// Number of bits in a bitvector type, or an error if this is not a bitvector
        /// type.
        pub fn size(&self) -> Result<u32> {
            Ok(yices! { yices_bvtype_size(self.typ) })
        }
    }

    impl_type! { Scalar }

    impl Scalar {
        /// Construct or return the scalar type with `cardinality` elements.
        pub fn new(card: u32) -> Result<Self> {
            Ok(Self {
                typ: yices! { yices_new_scalar_type(card) },
            })
        }

        pub fn card(&self) -> Result<u32> {
            Ok(yices! { yices_scalar_type_card(self.typ) })
        }
    }

    impl_type! { Uninterpreted }

    impl Uninterpreted {
        /// Construct a new uninterpreted type.
        pub fn new() -> Result<Self> {
            Ok(Self {
                typ: yices! { yices_new_uninterpreted_type() },
            })
        }
    }

    impl_type! { Tuple }

    impl Tuple {
        /// Construct a new tuple type.
        pub fn new<I, T>(types: I) -> Result<Self>
        where
            I: IntoIterator<Item = T>,
            T: InnerType,
        {
            let types: Vec<_> = types.into_iter().map(|t| t.inner()).collect();

            Ok(Self {
                typ: yices! { yices_tuple_type(types.len() as u32, types.as_ptr()) },
            })
        }
    }

    impl ChildType for Tuple {}

    impl_type! { Function }

    impl Function {
        /// Construct a new function type with `domain` as the domain and `range` as
        /// the range.
        pub fn new<I, T>(domain: I, range: T) -> Result<Self>
        where
            I: IntoIterator<Item = T>,
            T: InnerType,
        {
            let domain: Vec<_> = domain.into_iter().map(|t| t.inner()).collect();
            Ok(Self {
                typ: yices! {
                    yices_function_type(domain.len() as u32, domain.as_ptr(), range.inner())
                },
            })
        }
    }

    impl ChildType for Function {}

    pub enum Type {
        Bool(Bool),
        Integer(Integer),
        Real(Real),
        BitVector(BitVector),
        Scalar(Scalar),
        Uninterpreted(Uninterpreted),
        Tuple(Tuple),
        Function(Function),
    }

    impl TryFrom<type_t> for Type {
        type Error = Error;

        fn try_from(value: type_t) -> Result<Self> {
            if yices_try! { yices_type_is_bool(value) }.is_ok_and(|b| b != 0) {
                Ok(Type::Bool(Bool::from(value)))
            } else if yices_try! { yices_type_is_int(value) }.is_ok_and(|b| b != 0) {
                Ok(Type::Integer(Integer::from(value)))
            } else if yices_try! { yices_type_is_real(value) }.is_ok_and(|b| b != 0) {
                Ok(Type::Real(Real::from(value)))
            } else if yices_try! { yices_type_is_bitvector(value) }.is_ok_and(|b| b != 0) {
                Ok(Type::BitVector(BitVector::from(value)))
            } else if yices_try! { yices_type_is_scalar(value) }.is_ok_and(|b| b != 0) {
                Ok(Type::Scalar(Scalar::from(value)))
            } else if yices_try! { yices_type_is_uninterpreted(value) }.is_ok_and(|b| b != 0) {
                Ok(Type::Uninterpreted(Uninterpreted::from(value)))
            } else if yices_try! { yices_type_is_tuple(value) }.is_ok_and(|b| b != 0) {
                Ok(Type::Tuple(Tuple::from(value)))
            } else if yices_try! { yices_type_is_function(value) }.is_ok_and(|b| b != 0) {
                Ok(Type::Function(Function::from(value)))
            } else {
                Err(Error::InvalidType)
            }
        }
    }

    impl From<Type> for type_t {
        fn from(value: Type) -> Self {
            match value {
                Type::Bool(typ) => typ.inner(),
                Type::Integer(typ) => typ.inner(),
                Type::Real(typ) => typ.inner(),
                Type::BitVector(typ) => typ.inner(),
                Type::Scalar(typ) => typ.inner(),
                Type::Uninterpreted(typ) => typ.inner(),
                Type::Tuple(typ) => typ.inner(),
                Type::Function(typ) => typ.inner(),
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use crate::Result;

        #[test]
        fn construct() -> Result<()> {
            Ok(())
        }

        #[test]
        fn bv() -> Result<()> {
            Ok(())
        }

        #[test]
        fn scalar() -> Result<()> {
            Ok(())
        }

        #[test]
        fn tuple() -> Result<()> {
            Ok(())
        }

        #[test]
        fn function() -> Result<()> {
            Ok(())
        }

        #[test]
        fn subtype() -> Result<()> {
            Ok(())
        }
    }
}

mod term {
    use crate::{
        sys::{
            term_t, yices_abs, yices_add, yices_and, yices_application, yices_arith_eq0_atom,
            yices_arith_eq_atom, yices_arith_geq0_atom, yices_arith_geq_atom, yices_arith_gt0_atom,
            yices_arith_gt_atom, yices_arith_leq0_atom, yices_arith_leq_atom, yices_arith_lt0_atom,
            yices_arith_lt_atom, yices_arith_neq0_atom, yices_arith_neq_atom, yices_ashift_right,
            yices_bitextract, yices_bvadd, yices_bvand, yices_bvarray, yices_bvashr,
            yices_bvconcat, yices_bvconst_from_array, yices_bvconst_int32, yices_bvconst_int64,
            yices_bvconst_minus_one, yices_bvconst_one, yices_bvconst_uint32, yices_bvconst_uint64,
            yices_bvconst_zero, yices_bvdiv, yices_bveq_atom, yices_bvextract, yices_bvge_atom,
            yices_bvgt_atom, yices_bvle_atom, yices_bvlshr, yices_bvlt_atom, yices_bvmul,
            yices_bvnand, yices_bvneg, yices_bvneq_atom, yices_bvnor, yices_bvnot, yices_bvor,
            yices_bvpower, yices_bvproduct, yices_bvrem, yices_bvrepeat, yices_bvsdiv,
            yices_bvsge_atom, yices_bvsgt_atom, yices_bvshl, yices_bvsle_atom, yices_bvslt_atom,
            yices_bvsmod, yices_bvsquare, yices_bvsrem, yices_bvsub, yices_bvsum, yices_bvxnor,
            yices_bvxor, yices_ceil, yices_constant, yices_distinct, yices_divides_atom,
            yices_division, yices_eq, yices_exists, yices_false, yices_floor, yices_forall,
            yices_idiv, yices_iff, yices_imod, yices_implies, yices_int32, yices_int64,
            yices_is_int_atom, yices_ite, yices_lambda, yices_mul, yices_neg, yices_neq,
            yices_new_uninterpreted_term, yices_new_variable, yices_not, yices_or,
            yices_parse_bvbin, yices_parse_bvhex, yices_parse_float, yices_parse_rational,
            yices_poly_int32, yices_poly_int64, yices_poly_rational32, yices_poly_rational64,
            yices_power, yices_product, yices_rational32, yices_rational64, yices_redand,
            yices_redcomp, yices_redor, yices_rotate_left, yices_rotate_right, yices_select,
            yices_shift_left0, yices_shift_left1, yices_shift_right0, yices_shift_right1,
            yices_sign_extend, yices_square, yices_sub, yices_sum, yices_term_bitsize,
            yices_term_is_arithmetic, yices_term_is_bitvector, yices_term_is_bool,
            yices_term_is_function, yices_term_is_ground, yices_term_is_int, yices_term_is_real,
            yices_term_is_scalar, yices_term_is_tuple, yices_true, yices_tuple, yices_tuple_update,
            yices_type_of_term, yices_update, yices_xor, yices_zero, yices_zero_extend,
        },
        typ::Type,
        yices, Result,
    };
    use itertools::multiunzip;
    use paste::paste;

    pub trait InnerTerm {
        fn inner(&self) -> term_t;
    }

    macro_rules! impl_term {
        ($id:ident) => {
            paste! {
                pub struct $id {
                    term: term_t,
                }

                impl InnerTerm for $id {
                    fn inner(&self) -> term_t {
                        self.term
                    }
                }
            }
        };
    }

    impl_term! { Uninterpreted }

    impl Uninterpreted {
        pub fn new(typ: Type) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_new_uninterpreted_term(typ.into()) },
            })
        }
    }

    impl_term! { Variable }

    impl Variable {
        pub fn new(typ: Type) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_new_variable(typ.into()) },
            })
        }
    }

    impl_term! { Constant }

    impl Constant {
        /// typ must either be scalar or uninterpreted
        pub fn new(typ: Type, index: i32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_constant(typ.into(), index) },
            })
        }
    }

    impl_term! { IfThenElse }

    impl IfThenElse {
        pub fn new(cond: Term, then: Term, els: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_ite(cond.into(), then.into(), els.into()) },
            })
        }
    }

    impl_term! { Equal }

    impl Equal {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_eq(left.into(), right.into()) },
            })
        }
    }

    impl_term! { NotEqual }

    impl NotEqual {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_neq(left.into(), right.into()) },
            })
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

            Ok(Self {
                term: yices! { yices_distinct(terms.len() as u32, terms.as_mut_ptr()) },
            })
        }
    }

    impl_term! { Application }

    impl Application {
        pub fn new<I>(fun: Term, args: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms: Vec<_> = args.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_application(fun.into(), terms.len() as u32, terms.as_ptr()) },
            })
        }
    }

    impl_term! { Tuple }

    impl Tuple {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_tuple(terms.len() as u32, terms.as_ptr()) },
            })
        }
    }

    impl_term! { Select }

    impl Select {
        pub fn new(tuple: Term, index: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_select(index, tuple.into()) },
            })
        }
    }

    impl_term! { TupleUpdate }

    impl TupleUpdate {
        pub fn new(tuple: Term, index: u32, value: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_tuple_update(tuple.into(), index, value.into()) },
            })
        }
    }

    impl_term! { FunctionUpdate }

    impl FunctionUpdate {
        pub fn new<I>(fun: Term, args: I, value: Term) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms = args.into_iter().map(|t| t.into()).collect::<Vec<_>>();

            Ok(Self {
                term: yices! { yices_update(fun.into(), terms.len() as u32, terms.as_ptr(), value.into()) },
            })
        }
    }

    impl_term! { ForAll }

    impl ForAll {
        pub fn new<I>(vars: I, body: Term) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let mut terms = vars.into_iter().map(|t| t.into()).collect::<Vec<_>>();

            Ok(Self {
                term: yices! { yices_forall(terms.len() as u32, terms.as_mut_ptr(), body.into()) },
            })
        }
    }

    impl_term! { Exists }

    impl Exists {
        pub fn new<I>(vars: I, body: Term) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let mut terms = vars.into_iter().map(|t| t.into()).collect::<Vec<_>>();

            Ok(Self {
                term: yices! { yices_exists(terms.len() as u32, terms.as_mut_ptr(), body.into()) },
            })
        }
    }

    impl_term! { Lambda }

    impl Lambda {
        pub fn new<I>(vars: I, body: Term) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms = vars.into_iter().map(|t| t.into()).collect::<Vec<_>>();

            Ok(Self {
                term: yices! { yices_lambda(terms.len() as u32, terms.as_ptr(), body.into()) },
            })
        }
    }

    impl_term! { True }

    impl True {
        pub fn new() -> Result<Self> {
            Ok(Self {
                term: yices! { yices_true() },
            })
        }
    }

    impl_term! { False }

    impl False {
        pub fn new() -> Result<Self> {
            Ok(Self {
                term: yices! { yices_false() },
            })
        }
    }

    impl_term! { Not }

    impl Not {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_not(term.into()) },
            })
        }
    }

    impl_term! { And }

    impl And {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let mut terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_and(terms.len() as u32, terms.as_mut_ptr()) },
            })
        }
    }

    impl_term! { Or }

    impl Or {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let mut terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_or(terms.len() as u32, terms.as_mut_ptr()) },
            })
        }
    }

    impl_term! { Xor }

    impl Xor {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let mut terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_xor(terms.len() as u32, terms.as_mut_ptr()) },
            })
        }
    }

    impl_term! { Iff }

    impl Iff {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_iff(left.into(), right.into()) },
            })
        }
    }

    impl_term! { Implies }

    impl Implies {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_implies(left.into(), right.into()) },
            })
        }
    }

    impl_term! { Zero }

    impl Zero {
        pub fn new() -> Result<Self> {
            Ok(Self {
                term: yices! { yices_zero() },
            })
        }
    }

    impl_term! { Int32 }

    impl Int32 {
        pub fn new(value: i32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_int32(value) },
            })
        }
    }

    impl_term! { Int64 }

    impl Int64 {
        pub fn new(value: i64) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_int64(value) },
            })
        }
    }

    impl_term! { Rational32 }

    impl Rational32 {
        pub fn new(num: i32, den: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_rational32(num, den) },
            })
        }
    }

    impl_term! { Rational64 }

    impl Rational64 {
        pub fn new(num: i64, den: u64) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_rational64(num, den) },
            })
        }
    }

    impl_term! { Add }

    impl Add {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_add(left.into(), right.into()) },
            })
        }
    }

    impl_term! { Sub }

    impl Sub {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_sub(left.into(), right.into()) },
            })
        }
    }

    impl_term! { Neg }

    impl Neg {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_neg(term.into()) },
            })
        }
    }

    impl_term! { Mul }

    impl Mul {
        pub fn new<I>(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_mul(left.into(), right.into()) },
            })
        }
    }

    impl_term! { Square }

    impl Square {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_square(term.into()) },
            })
        }
    }

    impl_term! { Power }

    impl Power {
        pub fn new(base: Term, exponent: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_power(base.into(), exponent) },
            })
        }
    }

    impl_term! { Division }

    impl Division {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_division(left.into(), right.into()) },
            })
        }
    }

    impl_term! { Sum }

    impl Sum {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_sum(terms.len() as u32, terms.as_ptr()) },
            })
        }
    }

    impl_term! { Product }

    impl Product {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_product(terms.len() as u32, terms.as_ptr()) },
            })
        }
    }

    impl_term! { PolynomialInt32 }

    impl PolynomialInt32 {
        pub fn new<I>(terms: I) -> Result<Self>
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

            Ok(Self {
                term: yices! { yices_poly_int32(terms.len() as u32, coefficients.as_ptr(), terms.as_ptr()) },
            })
        }
    }

    impl_term! { PolynomialInt64 }

    impl PolynomialInt64 {
        pub fn new<I>(terms: I) -> Result<Self>
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

            Ok(Self {
                term: yices! { yices_poly_int64(terms.len() as u32, coefficients.as_ptr(), terms.as_ptr()) },
            })
        }
    }

    impl_term! { PolynomialRational32 }

    impl PolynomialRational32 {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = (Term, i32, u32)>,
        {
            let (terms, numerators, denominators): (Vec<term_t>, Vec<i32>, Vec<u32>) =
                multiunzip(terms.into_iter().map(|(term, numerator, denominator)| {
                    let term: term_t = term.into();
                    (term, numerator, denominator)
                }));

            Ok(Self {
                term: yices! { yices_poly_rational32(terms.len() as u32, numerators.as_ptr(), denominators.as_ptr(), terms.as_ptr()) },
            })
        }
    }

    impl_term! { PolynomialRational64 }

    impl PolynomialRational64 {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = (Term, i64, u64)>,
        {
            let (terms, numerators, denominators): (Vec<term_t>, Vec<i64>, Vec<u64>) =
                multiunzip(terms.into_iter().map(|(term, numerator, denominator)| {
                    let term: term_t = term.into();
                    (term, numerator, denominator)
                }));

            Ok(Self {
                term: yices! { yices_poly_rational64(terms.len() as u32, numerators.as_ptr(), denominators.as_ptr(), terms.as_ptr()) },
            })
        }
    }

    impl_term! { AbsoluteValue }

    impl AbsoluteValue {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_abs(term.into()) },
            })
        }
    }

    impl_term! { Floor }

    impl Floor {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_floor(term.into()) },
            })
        }
    }

    impl_term! { Ceiling }

    impl Ceiling {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_ceil(term.into()) },
            })
        }
    }

    impl_term! { IntegerDivision }

    impl IntegerDivision {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_idiv(left.into(), right.into()) },
            })
        }
    }

    impl_term! { IntegerModulo }

    impl IntegerModulo {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_imod(left.into(), right.into()) },
            })
        }
    }

    impl_term! { ArithmticEqualAtom }

    impl ArithmticEqualAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_arith_eq_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { ArithmticNotEqualAtom }

    impl ArithmticNotEqualAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_arith_neq_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { ArithmticLessThanAtom }

    impl ArithmticLessThanAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_arith_lt_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { ArithmticLessThanEqualAtom }

    impl ArithmticLessThanEqualAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_arith_leq_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { ArithmticGreaterThanAtom }

    impl ArithmticGreaterThanAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_arith_gt_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { ArithmticGreaterThanEqualAtom }

    impl ArithmticGreaterThanEqualAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_arith_geq_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { ArithmticLessThanZeroAtom }

    impl ArithmticLessThanZeroAtom {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_arith_lt0_atom(term.into()) },
            })
        }
    }

    impl_term! { ArithmticLessThanEqualZeroAtom }

    impl ArithmticLessThanEqualZeroAtom {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_arith_leq0_atom(term.into()) },
            })
        }
    }

    impl_term! { ArithmticGreaterThanZeroAtom }

    impl ArithmticGreaterThanZeroAtom {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_arith_gt0_atom(term.into()) },
            })
        }
    }

    impl_term! { ArithmticGreaterThanEqualZeroAtom }

    impl ArithmticGreaterThanEqualZeroAtom {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_arith_geq0_atom(term.into()) },
            })
        }
    }

    impl_term! { ArithmticEqualZeroAtom }

    impl ArithmticEqualZeroAtom {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_arith_eq0_atom(term.into()) },
            })
        }
    }

    impl_term! { ArithmticNotEqualZeroAtom }

    impl ArithmticNotEqualZeroAtom {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_arith_neq0_atom(term.into()) },
            })
        }
    }

    impl_term! { DividesAtom }

    impl DividesAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_divides_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { IsIntegerAtom }

    impl IsIntegerAtom {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_is_int_atom(term.into()) },
            })
        }
    }

    impl_term! { BitVectorConstantUInt32 }

    impl BitVectorConstantUInt32 {
        pub fn new(size: u32, value: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvconst_uint32(size, value) },
            })
        }
    }

    impl_term! { BitVectorConstantInt32 }

    impl BitVectorConstantInt32 {
        pub fn new(size: u32, value: i32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvconst_int32(size, value) },
            })
        }
    }

    impl_term! { BitVectorConstantUInt64 }

    impl BitVectorConstantUInt64 {
        pub fn new(size: u32, value: u64) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvconst_uint64(size, value) },
            })
        }
    }

    impl_term! { BitVectorConstantInt64 }

    impl BitVectorConstantInt64 {
        pub fn new(size: u32, value: i64) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvconst_int64(size, value) },
            })
        }
    }

    impl_term! { BitVectorConstantZero }

    impl BitVectorConstantZero {
        pub fn new(size: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvconst_zero(size) },
            })
        }
    }

    impl_term! { BitVectorConstantOne }

    impl BitVectorConstantOne {
        pub fn new(size: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvconst_one(size) },
            })
        }
    }

    impl_term! { BitVectorConstantMinusOne }

    impl BitVectorConstantMinusOne {
        pub fn new(size: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvconst_minus_one(size) },
            })
        }
    }

    impl_term! { BitVectorConstantFromIntArray }

    impl BitVectorConstantFromIntArray {
        pub fn new<I>(values: I) -> Result<Self>
        where
            I: IntoIterator<Item = i32>,
        {
            let values: Vec<_> = values.into_iter().collect();

            Ok(Self {
                term: yices! { yices_bvconst_from_array(values.len() as u32, values.as_ptr()) },
            })
        }
    }

    impl_term! { BitVectorAdd }

    impl BitVectorAdd {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvadd(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorSub }

    impl BitVectorSub {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvsub(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorNeg }

    impl BitVectorNeg {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvneg(term.into()) },
            })
        }
    }

    impl_term! { BitVectorMul }

    impl BitVectorMul {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvmul(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorSquare }

    impl BitVectorSquare {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvsquare(term.into()) },
            })
        }
    }

    impl_term! { BitVectorPower }

    impl BitVectorPower {
        pub fn new(base: Term, exponent: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvpower(base.into(), exponent) },
            })
        }
    }

    impl_term! { BitVectorSum }

    impl BitVectorSum {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_bvsum(terms.len() as u32, terms.as_ptr()) },
            })
        }
    }

    impl_term! { BitVectorProduct }

    impl BitVectorProduct {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_bvproduct(terms.len() as u32, terms.as_ptr()) },
            })
        }
    }

    impl_term! { BitVectorDivision }

    impl BitVectorDivision {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvdiv(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorRemainder }

    impl BitVectorRemainder {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvrem(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorSignedDivision }

    impl BitVectorSignedDivision {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvsdiv(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorSignedRemainder }

    impl BitVectorSignedRemainder {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvsrem(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorSignedModulo }

    impl BitVectorSignedModulo {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvsmod(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorNot }

    impl BitVectorNot {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvnot(term.into()) },
            })
        }
    }

    impl_term! { BitVectorAnd }

    impl BitVectorAnd {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_bvand(terms.len() as u32, terms.as_ptr()) },
            })
        }
    }

    impl_term! { BitVectorOr }

    impl BitVectorOr {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_bvor(terms.len() as u32, terms.as_ptr()) },
            })
        }
    }

    impl_term! { BitVectorXor }

    impl BitVectorXor {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_bvxor(terms.len() as u32, terms.as_ptr()) },
            })
        }
    }

    impl_term! { BitVectorNAnd }

    impl BitVectorNAnd {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvnand(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorNOr }

    impl BitVectorNOr {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvnor(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorXNor }

    impl BitVectorXNor {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvxnor(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorShiftLeftFill0 }

    impl BitVectorShiftLeftFill0 {
        pub fn new(left: Term, n: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_shift_left0(left.into(), n) },
            })
        }
    }

    impl_term! { BitVectorShiftLeftFill1 }

    impl BitVectorShiftLeftFill1 {
        pub fn new(left: Term, n: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_shift_left1(left.into(), n) },
            })
        }
    }

    impl_term! { BitVectorShiftRightFill0 }

    impl BitVectorShiftRightFill0 {
        pub fn new(left: Term, n: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_shift_right0(left.into(), n) },
            })
        }
    }

    impl_term! { BitVectorShiftRightFill1 }

    impl BitVectorShiftRightFill1 {
        pub fn new(left: Term, n: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_shift_right1(left.into(), n) },
            })
        }
    }

    impl_term! { BitVectorArithmeticShiftRightConstant }

    impl BitVectorArithmeticShiftRightConstant {
        pub fn new(left: Term, n: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_ashift_right(left.into(), n) },
            })
        }
    }

    impl_term! { BitVectorRotateLeft }

    impl BitVectorRotateLeft {
        pub fn new(left: Term, n: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_rotate_left(left.into(), n) },
            })
        }
    }

    impl_term! { BitVectorRotateRight }

    impl BitVectorRotateRight {
        pub fn new(left: Term, n: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_rotate_right(left.into(), n) },
            })
        }
    }

    impl_term! { BitVectorShiftLeft }

    impl BitVectorShiftLeft {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvshl(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorShiftRight }

    impl BitVectorShiftRight {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvlshr(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorArithmeticShiftRight }

    impl BitVectorArithmeticShiftRight {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvashr(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorExtract }

    impl BitVectorExtract {
        pub fn new(term: Term, lower: u32, upper: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvextract(term.into(), lower, upper) },
            })
        }
    }

    impl_term! { BitVectorBitExtract }

    impl BitVectorBitExtract {
        pub fn new(term: Term, bit: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bitextract(term.into(), bit) },
            })
        }
    }

    impl_term! { BitVectorConcatenate }

    impl BitVectorConcatenate {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_bvconcat(terms.len() as u32, terms.as_ptr()) },
            })
        }
    }

    impl_term! { BitVectorRepeat }

    impl BitVectorRepeat {
        pub fn new(term: Term, n: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvrepeat(term.into(), n) },
            })
        }
    }

    impl_term! { BitVectorSignExtend }

    impl BitVectorSignExtend {
        pub fn new(term: Term, n: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_sign_extend(term.into(), n) },
            })
        }
    }

    impl_term! { BitVectorZeroExtend }

    impl BitVectorZeroExtend {
        pub fn new(term: Term, n: u32) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_zero_extend(term.into(), n) },
            })
        }
    }

    impl_term! { BitVectorReduceAnd }

    impl BitVectorReduceAnd {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_redand(term.into()) },
            })
        }
    }

    impl_term! { BitVectorReduceOr }

    impl BitVectorReduceOr {
        pub fn new(term: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_redor(term.into()) },
            })
        }
    }

    impl_term! { BitVectorReduceEqual }

    impl BitVectorReduceEqual {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_redcomp(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorArray }

    impl BitVectorArray {
        pub fn new<I>(terms: I) -> Result<Self>
        where
            I: IntoIterator<Item = Term>,
        {
            let terms: Vec<_> = terms.into_iter().map(|t| t.into()).collect();

            Ok(Self {
                term: yices! { yices_bvarray(terms.len() as u32, terms.as_ptr()) },
            })
        }
    }

    impl_term! { BitVectorEqualAtom }

    impl BitVectorEqualAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bveq_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorNotEqualAtom }

    impl BitVectorNotEqualAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvneq_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorLessThanAtom }

    impl BitVectorLessThanAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvlt_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorLessThanEqualAtom }

    impl BitVectorLessThanEqualAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvle_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorGreaterThanAtom }

    impl BitVectorGreaterThanAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvgt_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorGreaterThanEqualAtom }

    impl BitVectorGreaterThanEqualAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvge_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorSignedLessThanAtom }

    impl BitVectorSignedLessThanAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvsle_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorSignedLessThanEqualAtom }

    impl BitVectorSignedLessThanEqualAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvsle_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorSignedGreaterThanAtom }

    impl BitVectorSignedGreaterThanAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvsgt_atom(left.into(), right.into()) },
            })
        }
    }

    impl_term! { BitVectorSignedGreaterThanEqualAtom }

    impl BitVectorSignedGreaterThanEqualAtom {
        pub fn new(left: Term, right: Term) -> Result<Self> {
            Ok(Self {
                term: yices! { yices_bvsge_atom(left.into(), right.into()) },
            })
        }
    }

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
        True(True),
        False(False),
        Not(Not),
        And(And),
        Or(Or),
        Xor(Xor),
        Iff(Iff),
        Implies(Implies),
        Zero(Zero),
        Int32(Int32),
        Int64(Int64),
        Rational32(Rational32),
        Rational64(Rational64),
        Add(Add),
        Sub(Sub),
        Neg(Neg),
        Mul(Mul),
        Square(Square),
        Power(Power),
        Division(Division),
        Sum(Sum),
        Product(Product),
        PolynomialInt32(PolynomialInt32),
        PolynomialInt64(PolynomialInt64),
        PolynomialRational32(PolynomialRational32),
        PolynomialRational64(PolynomialRational64),
        AbsoluteValue(AbsoluteValue),
        Floor(Floor),
        Ceiling(Ceiling),
        IntegerDivision(IntegerDivision),
        IntegerModulo(IntegerModulo),
        ArithmticEqualAtom(ArithmticEqualAtom),
        ArithmticNotEqualAtom(ArithmticNotEqualAtom),
        ArithmticLessThanAtom(ArithmticLessThanAtom),
        ArithmticLessThanEqualAtom(ArithmticLessThanEqualAtom),
        ArithmticGreaterThanAtom(ArithmticGreaterThanAtom),
        ArithmticGreaterThanEqualAtom(ArithmticGreaterThanEqualAtom),
        ArithmticLessThanZeroAtom(ArithmticLessThanZeroAtom),
        ArithmticLessThanEqualZeroAtom(ArithmticLessThanEqualZeroAtom),
        ArithmticGreaterThanZeroAtom(ArithmticGreaterThanZeroAtom),
        ArithmticGreaterThanEqualZeroAtom(ArithmticGreaterThanEqualZeroAtom),
        ArithmticEqualZeroAtom(ArithmticEqualZeroAtom),
        ArithmticNotEqualZeroAtom(ArithmticNotEqualZeroAtom),
        DividesAtom(DividesAtom),
        IsIntegerAtom(IsIntegerAtom),
        BitVectorConstantUInt32(BitVectorConstantUInt32),
        BitVectorConstantInt32(BitVectorConstantInt32),
        BitVectorConstantUInt64(BitVectorConstantUInt64),
        BitVectorConstantInt64(BitVectorConstantInt64),
        BitVectorConstantZero(BitVectorConstantZero),
        BitVectorConstantOne(BitVectorConstantOne),
        BitVectorConstantMinusOne(BitVectorConstantMinusOne),
        BitVectorConstantFromIntArray(BitVectorConstantFromIntArray),
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
    }

    impl From<Term> for term_t {
        fn from(value: Term) -> Self {
            match value {
                Term::Uninterpreted(term) => term.inner(),
                Term::Variable(term) => term.inner(),
                Term::Constant(term) => term.inner(),
                Term::IfThenElse(term) => term.inner(),
                Term::Equal(term) => term.inner(),
                Term::NotEqual(term) => term.inner(),
                Term::Distinct(term) => term.inner(),
                Term::Application(term) => term.inner(),
                Term::Tuple(term) => term.inner(),
                Term::Select(term) => term.inner(),
                Term::TupleUpdate(term) => term.inner(),
                Term::FunctionUpdate(term) => term.inner(),
                Term::ForAll(term) => term.inner(),
                Term::Exists(term) => term.inner(),
                Term::Lambda(term) => term.inner(),
                Term::True(term) => term.inner(),
                Term::False(term) => term.inner(),
                Term::Not(term) => term.inner(),
                Term::And(term) => term.inner(),
                Term::Or(term) => term.inner(),
                Term::Xor(term) => term.inner(),
                Term::Iff(term) => term.inner(),
                Term::Implies(term) => term.inner(),
                Term::Zero(term) => term.inner(),
                Term::Int32(term) => term.inner(),
                Term::Int64(term) => term.inner(),
                Term::Rational32(term) => term.inner(),
                Term::Rational64(term) => term.inner(),
                Term::Add(term) => term.inner(),
                Term::Sub(term) => term.inner(),
                Term::Neg(term) => term.inner(),
                Term::Mul(term) => term.inner(),
                Term::Square(term) => term.inner(),
                Term::Power(term) => term.inner(),
                Term::Division(term) => term.inner(),
                Term::Sum(term) => term.inner(),
                Term::Product(term) => term.inner(),
                Term::PolynomialInt32(term) => term.inner(),
                Term::PolynomialInt64(term) => term.inner(),
                Term::PolynomialRational32(term) => term.inner(),
                Term::PolynomialRational64(term) => term.inner(),
                Term::AbsoluteValue(term) => term.inner(),
                Term::Floor(term) => term.inner(),
                Term::Ceiling(term) => term.inner(),
                Term::IntegerDivision(term) => term.inner(),
                Term::IntegerModulo(term) => term.inner(),
                Term::ArithmticEqualAtom(term) => term.inner(),
                Term::ArithmticNotEqualAtom(term) => term.inner(),
                Term::ArithmticLessThanAtom(term) => term.inner(),
                Term::ArithmticLessThanEqualAtom(term) => term.inner(),
                Term::ArithmticGreaterThanAtom(term) => term.inner(),
                Term::ArithmticGreaterThanEqualAtom(term) => term.inner(),
                Term::ArithmticLessThanZeroAtom(term) => term.inner(),
                Term::ArithmticLessThanEqualZeroAtom(term) => term.inner(),
                Term::ArithmticGreaterThanZeroAtom(term) => term.inner(),
                Term::ArithmticGreaterThanEqualZeroAtom(term) => term.inner(),
                Term::ArithmticEqualZeroAtom(term) => term.inner(),
                Term::ArithmticNotEqualZeroAtom(term) => term.inner(),
                Term::DividesAtom(term) => term.inner(),
                Term::IsIntegerAtom(term) => term.inner(),
                Term::BitVectorConstantUInt32(term) => term.inner(),
                Term::BitVectorConstantInt32(term) => term.inner(),
                Term::BitVectorConstantUInt64(term) => term.inner(),
                Term::BitVectorConstantInt64(term) => term.inner(),
                Term::BitVectorConstantZero(term) => term.inner(),
                Term::BitVectorConstantOne(term) => term.inner(),
                Term::BitVectorConstantMinusOne(term) => term.inner(),
                Term::BitVectorConstantFromIntArray(term) => term.inner(),
                Term::BitVectorAdd(term) => term.inner(),
                Term::BitVectorSub(term) => term.inner(),
                Term::BitVectorNeg(term) => term.inner(),
                Term::BitVectorMul(term) => term.inner(),
                Term::BitVectorSquare(term) => term.inner(),
                Term::BitVectorPower(term) => term.inner(),
                Term::BitVectorSum(term) => term.inner(),
                Term::BitVectorProduct(term) => term.inner(),
                Term::BitVectorDivision(term) => term.inner(),
                Term::BitVectorRemainder(term) => term.inner(),
                Term::BitVectorSignedDivision(term) => term.inner(),
                Term::BitVectorSignedRemainder(term) => term.inner(),
                Term::BitVectorSignedModulo(term) => term.inner(),
                Term::BitVectorNot(term) => term.inner(),
                Term::BitVectorAnd(term) => term.inner(),
                Term::BitVectorOr(term) => term.inner(),
                Term::BitVectorXor(term) => term.inner(),
                Term::BitVectorNAnd(term) => term.inner(),
                Term::BitVectorNOr(term) => term.inner(),
                Term::BitVectorXNor(term) => term.inner(),
                Term::BitVectorShiftLeftFill0(term) => term.inner(),
                Term::BitVectorShiftLeftFill1(term) => term.inner(),
                Term::BitVectorShiftRightFill0(term) => term.inner(),
                Term::BitVectorShiftRightFill1(term) => term.inner(),
                Term::BitVectorArithmeticShiftRightConstant(term) => term.inner(),
                Term::BitVectorRotateLeft(term) => term.inner(),
                Term::BitVectorRotateRight(term) => term.inner(),
                Term::BitVectorShiftLeft(term) => term.inner(),
                Term::BitVectorShiftRight(term) => term.inner(),
                Term::BitVectorArithmeticShiftRight(term) => term.inner(),
                Term::BitVectorExtract(term) => term.inner(),
                Term::BitVectorBitExtract(term) => term.inner(),
                Term::BitVectorConcatenate(term) => term.inner(),
                Term::BitVectorRepeat(term) => term.inner(),
                Term::BitVectorSignExtend(term) => term.inner(),
                Term::BitVectorZeroExtend(term) => term.inner(),
                Term::BitVectorReduceAnd(term) => term.inner(),
                Term::BitVectorReduceOr(term) => term.inner(),
                Term::BitVectorReduceEqual(term) => term.inner(),
                Term::BitVectorArray(term) => term.inner(),
                Term::BitVectorEqualAtom(term) => term.inner(),
                Term::BitVectorNotEqualAtom(term) => term.inner(),
                Term::BitVectorLessThanAtom(term) => term.inner(),
                Term::BitVectorLessThanEqualAtom(term) => term.inner(),
                Term::BitVectorGreaterThanAtom(term) => term.inner(),
                Term::BitVectorGreaterThanEqualAtom(term) => term.inner(),
                Term::BitVectorSignedLessThanAtom(term) => term.inner(),
                Term::BitVectorSignedLessThanEqualAtom(term) => term.inner(),
                Term::BitVectorSignedGreaterThanAtom(term) => term.inner(),
                Term::BitVectorSignedGreaterThanEqualAtom(term) => term.inner(),
            }
        }
    }
}
