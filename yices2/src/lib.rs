//! High-level Yices2 bindings

use crate::error::Error;
use ctor::{ctor, dtor};

type Result<T> = std::result::Result<T, Error>;

#[ctor]
/// Constructor: initialize yices at initialization time
fn yices_init() {
    unsafe { sys::yices_init() };
}

#[dtor]
/// Destructor: clean up yices at exit time
fn yices_exit() {
    unsafe { sys::yices_exit() };
}
pub mod sys {
    pub use yices2_sys::*;

    #[macro_export]
    macro_rules! api {
        ($x:expr) => {
            unsafe {
                let res = $x;
                $crate::report!();
                res
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
    macro_rules! report {
        () => {
            match $crate::error::error() {
                Error::NoError => {}
                err => {
                    $crate::error::clear_error();
                    return Err(err);
                }
            }
        };
    }
}

pub mod typ {

    use yices2_sys::yices_type_is_bool;

    use crate::{
        api,
        error::Error,
        sys::{
            type_t, type_vector_t, yices_bool_type, yices_bv_type, yices_bvtype_size,
            yices_compatible_types, yices_delete_type_vector, yices_function_type,
            yices_init_type_vector, yices_int_type, yices_new_scalar_type,
            yices_new_uninterpreted_type, yices_real_type, yices_scalar_type_card,
            yices_test_subtype, yices_tuple_type, yices_type_child, yices_type_children,
            yices_type_is_arithmetic, yices_type_is_bitvector, yices_type_is_function,
            yices_type_is_int, yices_type_is_real, yices_type_is_scalar, yices_type_is_tuple,
            yices_type_is_uninterpreted, yices_type_num_children, NULL_TYPE,
        },
        Result,
    };

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct Type {
        typ: type_t,
    }

    /// Constructor implementations for Type
    impl Type {
        /// Return the Boolean type
        pub fn bool() -> Self {
            Self {
                typ: unsafe { yices_bool_type() },
            }
        }

        /// Return the integer type
        pub fn integer() -> Self {
            Self {
                typ: unsafe { yices_int_type() },
            }
        }

        /// Return the real type
        pub fn real() -> Self {
            Self {
                typ: unsafe { yices_real_type() },
            }
        }

        /// Construct or return the bitvector type for a bitvector with a bit-width of
        /// `size`.
        pub fn bv(size: u32) -> Result<Self> {
            let typ = api! { yices_bv_type(size) };

            Ok(Self { typ })
        }

        /// Construct or return the scalar type with `cardinality` elements.
        pub fn scalar(card: u32) -> Result<Self> {
            let typ = api! { yices_new_scalar_type(card) };

            Ok(Self { typ })
        }

        /// Construct a new uninterpreted type.
        pub fn uninterpreted() -> Self {
            Self {
                typ: unsafe { yices_new_uninterpreted_type() },
            }
        }

        /// Construct a new tuple type.
        pub fn tuple<I, T>(types: I) -> Result<Self>
        where
            I: IntoIterator<Item = T>,
            T: Into<Type>,
        {
            let types: Vec<_> = types.into_iter().map(|t| t.into().typ).collect();
            let typ = api! { yices_tuple_type(types.len() as u32, types.as_ptr()) };

            Ok(Self { typ })
        }

        /// Construct a new function type with `domain` as the domain and `range` as
        /// the range.
        pub fn function<I, T>(domain: I, range: T) -> Self
        where
            I: IntoIterator<Item = T>,
            T: Into<Type>,
        {
            let domain: Vec<_> = domain.into_iter().map(|t| t.into().typ).collect();
            Self {
                typ: unsafe {
                    yices_function_type(domain.len() as u32, domain.as_ptr(), range.into().typ)
                },
            }
        }
    }

    impl Type {
        /// Returns whether this type is a subtype of `other`.
        pub fn subtype(&self, other: &Self) -> Result<bool> {
            Ok(api! { yices_test_subtype(self.typ, other.typ) } != 0)
        }

        /// Returns whether this type is compatible with `other, that is they share
        /// a common supertype. For example `real` and `int` are compatible.
        pub fn compatible(&self, other: &Self) -> Result<bool> {
            Ok(api! { yices_compatible_types(self.typ, other.typ) } != 0)
        }
    }

    impl Type {
        pub fn is_bool(&self) -> Result<bool> {
            Ok(api! { yices_type_is_bool(self.typ) } != 0)
        }

        pub fn is_int(&self) -> Result<bool> {
            Ok(api! { yices_type_is_int(self.typ) } != 0)
        }

        pub fn is_real(&self) -> Result<bool> {
            Ok(api! { yices_type_is_real(self.typ) } != 0)
        }

        pub fn is_arithmetic(&self) -> Result<bool> {
            Ok(api! { yices_type_is_arithmetic(self.typ) } != 0)
        }

        pub fn is_bitvector(&self) -> Result<bool> {
            Ok(api! { yices_type_is_bitvector(self.typ) } != 0)
        }

        pub fn is_scalar(&self) -> Result<bool> {
            Ok(api! { yices_type_is_scalar(self.typ) } != 0)
        }

        pub fn is_uninterpreted(&self) -> Result<bool> {
            Ok(api! { yices_type_is_uninterpreted(self.typ) } != 0)
        }

        pub fn is_tuple(&self) -> Result<bool> {
            Ok(api! { yices_type_is_tuple(self.typ) } != 0)
        }

        pub fn is_function(&self) -> Result<bool> {
            Ok(api! { yices_type_is_function(self.typ) } != 0)
        }
    }

    impl Type {
        /// Number of bits in a bitvector type, or an error if this is not a bitvector
        /// type.
        pub fn size(&self) -> Result<u32> {
            Ok(api! { yices_bvtype_size(self.typ) })
        }

        pub fn card(&self) -> Result<u32> {
            Ok(api! { yices_scalar_type_card(self.typ) })
        }

        pub fn num_children(&self) -> Result<i32> {
            Ok(api! { yices_type_num_children(self.typ) })
        }

        pub fn child(&self, index: i32) -> Result<Self> {
            let typ = api! { yices_type_child(self.typ, index) };

            if typ == NULL_TYPE {
                Err(Error::InvalidType)
            } else {
                Ok(Self { typ })
            }
        }

        pub fn children(&self) -> Result<Vec<Self>> {
            let mut vec = type_vector_t {
                size: 0,
                capacity: 0,
                data: std::ptr::null_mut(),
            };

            api! { yices_init_type_vector(&mut vec as *mut type_vector_t) };

            if api! { yices_type_children(self.typ, &mut vec as *mut type_vector_t) } == -1 {
                api! { yices_delete_type_vector(&mut vec as *mut type_vector_t) };

                Err(Error::InvalidType)
            } else {
                let mut types = Vec::with_capacity(vec.size as usize);

                for i in 0..vec.size {
                    types.push(Self {
                        typ: unsafe { *vec.data.offset(i as isize) },
                    });
                }

                api! { yices_delete_type_vector(&mut vec as *mut type_vector_t) };

                Ok(types)
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use crate::Result;

        #[test]
        fn construct() -> Result<()> {
            let _ = super::Type::bool();
            let _ = super::Type::integer();
            let _ = super::Type::real();
            let _ = super::Type::bv(8)?;
            let _ = super::Type::bv(16)?;
            let _ = super::Type::bv(32)?;
            let _ = super::Type::bv(64)?;
            let _ = super::Type::bv(128)?;
            let _ = super::Type::bv(256)?;
            let _ = super::Type::scalar(32)?;
            let _ = super::Type::uninterpreted();
            let _ = super::Type::tuple(vec![super::Type::bool(), super::Type::integer()])?;
            let _ = super::Type::function(
                vec![super::Type::bool(), super::Type::integer()],
                super::Type::real(),
            );

            Ok(())
        }

        #[test]
        fn bv() -> Result<()> {
            assert_eq!(super::Type::bv(8)?.size()?, 8);
            assert_eq!(super::Type::bv(16)?.size()?, 16);
            assert_eq!(super::Type::bv(32)?.size()?, 32);
            assert_eq!(super::Type::bv(64)?.size()?, 64);
            assert_eq!(super::Type::bv(128)?.size()?, 128);
            assert_eq!(super::Type::bv(256)?.size()?, 256);

            Ok(())
        }

        #[test]
        fn scalar() -> Result<()> {
            assert_eq!(super::Type::scalar(32)?.card()?, 32);

            Ok(())
        }

        #[test]
        fn tuple() -> Result<()> {
            let typ = super::Type::tuple(vec![super::Type::bool(), super::Type::integer()])?;

            assert_eq!(typ.num_children()?, 2);

            Ok(())
        }

        #[test]
        fn function() -> Result<()> {
            let typ = super::Type::function(
                vec![super::Type::bool(), super::Type::integer()],
                super::Type::real(),
            );

            assert_eq!(typ.num_children()?, 3, "function type has 3 children");

            Ok(())
        }

        #[test]
        fn subtype() -> Result<()> {
            let bool = super::Type::bool();
            let int = super::Type::integer();
            let real = super::Type::real();
            let bv8 = super::Type::bv(8)?;
            let bv16 = super::Type::bv(16)?;
            let bv32 = super::Type::bv(32)?;
            let bv64 = super::Type::bv(64)?;
            let bv128 = super::Type::bv(128)?;
            let bv256 = super::Type::bv(256)?;
            let scalar32 = super::Type::scalar(32)?;
            let scalar64 = super::Type::scalar(64)?;
            let tuple = super::Type::tuple(vec![bool, int])?;
            let function = super::Type::function(vec![bool, int], real);

            assert!(bool.subtype(&bool)?);
            assert!(int.subtype(&int)?);
            assert!(real.subtype(&real)?);
            assert!(bv8.subtype(&bv8)?);
            assert!(bv16.subtype(&bv16)?);
            assert!(bv32.subtype(&bv32)?);
            assert!(bv64.subtype(&bv64)?);
            assert!(bv128.subtype(&bv128)?);
            assert!(bv256.subtype(&bv256)?);
            assert!(scalar32.subtype(&scalar32)?);
            assert!(scalar64.subtype(&scalar64)?);
            assert!(tuple.subtype(&tuple)?);
            assert!(function.subtype(&function)?);

            assert!(int.subtype(&real)?);

            Ok(())
        }
    }
}

mod term {
    use crate::sys::term_t;

    pub struct Term {
        term: term_t,
    }

    impl Term {}
}
