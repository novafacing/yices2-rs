use std::{
    ffi::CString,
    ptr::{null, null_mut},
    str::FromStr,
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

trait AsKeyValue {
    fn as_kv(&self) -> (String, String);
}

impl<S> AsKeyValue for (S, S)
where
    S: AsRef<str>,
{
    fn as_kv(&self) -> (String, String) {
        (self.0.as_ref().to_string(), self.1.as_ref().to_string())
    }
}

#[allow(non_camel_case_types)]
#[derive(Clone, Debug)]
/// See https://smtlib.cs.uiowa.edu/logics.shtml for more information.
pub enum Logic {
    /// Arrays and Bitvectors
    QF_ABV,
    /// Arrays and Linear Integer Arithmetic
    QF_ALIA,
    /// Arrays, Uninterpreted Functions, and Bitvectors
    QF_AUFBV,
    /// Arrays, Uninterpreted Functions, and Linear Integer Arithmetic
    QF_AUFLIA,
    /// Arrays (with extensionality)
    QF_AX,
    /// Bitvectors
    QF_BV,
    /// Integer Difference Logic
    QF_IDL,
    /// Linear Integer Arithmetic
    QF_LIA,
    /// Linear Real Arithmetic
    QF_LRA,
    /// Nonlinear Integer Arithmetic
    QF_NIA,
    /// Mixed Nonlinear Arithmetic
    QF_NIRA,
    /// Nonlinear Real Arithmetic
    QF_NRA,
    /// Real Difference Logic
    QF_RDL,
    /// Uninterpreted Functions
    QF_UF,
    /// Uninterpreted Functions and Bitvectors
    QF_UFBV,
    /// Uninterpreted Functions and Integer Difference Logic
    QF_UFIDL,
    /// Uninterpreted Functions and Linear Integer Arithmetic
    QF_UFLIA,
    /// Uninterpreted Functions and Linear Real Arithmetic
    QF_UFLRA,
    /// Uninterpreted Functions and Nonlinear Integer Arithmetic
    QF_UFNIA,
    /// Uninterpreted Functions and Mixed Nonlinear Arithmetic
    QF_UFNIRA,
    /// Uninterpreted Functions and Nonlinear Real Arithmetic
    QF_UFNRA,
    /// Arrays and Linear Real Arithmetic
    QF_ALRA,
    /// Arrays and Mixed Linear Arithmetic
    QF_ALIRA,
    /// Arrays and Uninterpreted Functions
    QF_AUF,
    /// Arrays, Uninterpreted Functions, Linear Real Arithmetic
    QF_AUFLRA,
    /// Arrays, Uninterpreted Functions, Mixed Linear Arithmetic
    QF_AUFLIRA,
    /// Mixed Linear Arithmetic
    QF_LIRA,
    /// Uninterpreted Functions and Mixed Linear Arithmetic
    QF_UFLIRA,
    /// Uninterpreted Functions and Real Difference Logic
    QF_UFRDL,
}

impl ToString for Logic {
    fn to_string(&self) -> String {
        match self {
            Logic::QF_ABV => "QF_ABV",
            Logic::QF_AUFBV => "QF_AUFBV",
            Logic::QF_AUFLIA => "QF_AUFLIA",
            Logic::QF_AX => "QF_AX",
            Logic::QF_BV => "QF_BV",
            Logic::QF_IDL => "QF_IDL",
            Logic::QF_LIA => "QF_LIA",
            Logic::QF_LRA => "QF_LRA",
            Logic::QF_NIA => "QF_NIA",
            Logic::QF_NRA => "QF_NRA",
            Logic::QF_RDL => "QF_RDL",
            Logic::QF_UF => "QF_UF",
            Logic::QF_UFBV => "QF_UFBV",
            Logic::QF_UFIDL => "QF_UFIDL",
            Logic::QF_UFLIA => "QF_UFLIA",
            Logic::QF_UFLRA => "QF_UFLRA",
            Logic::QF_UFNRA => "QF_UFNRA",
            Logic::QF_ALIA => "QF_ALIA",
            Logic::QF_NIRA => "QF_NIRA",
            Logic::QF_UFNIA => "QF_UFNIA",
            Logic::QF_UFNIRA => "QF_UFNIRA",
            Logic::QF_ALRA => "QF_ALRA",
            Logic::QF_ALIRA => "QF_ALIRA",
            Logic::QF_AUF => "QF_AUF",
            Logic::QF_AUFLRA => "QF_AUFLRA",
            Logic::QF_AUFLIRA => "QF_AUFLIRA",
            Logic::QF_LIRA => "QF_LIRA",
            Logic::QF_UFLIRA => "QF_UFLIRA",
            Logic::QF_UFRDL => "QF_UFRDL",
        }
        .to_string()
    }
}

impl FromStr for Logic {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "QF_ABV" => Ok(Logic::QF_ABV),
            "QF_AUFBV" => Ok(Logic::QF_AUFBV),
            "QF_AUFLIA" => Ok(Logic::QF_AUFLIA),
            "QF_AX" => Ok(Logic::QF_AX),
            "QF_BV" => Ok(Logic::QF_BV),
            "QF_IDL" => Ok(Logic::QF_IDL),
            "QF_LIA" => Ok(Logic::QF_LIA),
            "QF_LRA" => Ok(Logic::QF_LRA),
            "QF_NIA" => Ok(Logic::QF_NIA),
            "QF_NRA" => Ok(Logic::QF_NRA),
            "QF_RDL" => Ok(Logic::QF_RDL),
            "QF_UF" => Ok(Logic::QF_UF),
            "QF_UFBV" => Ok(Logic::QF_UFBV),
            "QF_UFIDL" => Ok(Logic::QF_UFIDL),
            "QF_UFLIA" => Ok(Logic::QF_UFLIA),
            "QF_UFLRA" => Ok(Logic::QF_UFLRA),
            "QF_UFNRA" => Ok(Logic::QF_UFNRA),
            "QF_ALIA" => Ok(Logic::QF_ALIA),
            "QF_NIRA" => Ok(Logic::QF_NIRA),
            "QF_UFNIA" => Ok(Logic::QF_UFNIA),
            "QF_UFNIRA" => Ok(Logic::QF_UFNIRA),
            "QF_ALRA" => Ok(Logic::QF_ALRA),
            "QF_ALIRA" => Ok(Logic::QF_ALIRA),
            "QF_AUF" => Ok(Logic::QF_AUF),
            "QF_AUFLRA" => Ok(Logic::QF_AUFLRA),
            "QF_AUFLIRA" => Ok(Logic::QF_AUFLIRA),
            "QF_LIRA" => Ok(Logic::QF_LIRA),
            "QF_UFLIRA" => Ok(Logic::QF_UFLIRA),
            "QF_UFRDL" => Ok(Logic::QF_UFRDL),
            _ => Err(Error::InvalidLogicName {
                logic: s.to_string(),
            }),
        }
    }
}

#[derive(Clone, Debug)]
pub enum SolverType {
    /// use DPLL(T) approach
    DPLLT,
    /// use MCSat
    MCSAT,
}

impl ToString for SolverType {
    fn to_string(&self) -> String {
        match self {
            SolverType::DPLLT => "dpllt",
            SolverType::MCSAT => "mcsat",
        }
        .to_string()
    }
}

impl FromStr for SolverType {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "dpllt" => Ok(SolverType::DPLLT),
            "mcsat" => Ok(SolverType::MCSAT),
            _ => Err(Error::InvalidSolverTypeName {
                solver_type: s.to_string(),
            }),
        }
    }
}

impl AsKeyValue for SolverType {
    fn as_kv(&self) -> (String, String) {
        ("solver-type".to_string(), self.to_string())
    }
}

#[derive(Clone, Debug)]
pub enum UninterpretedFunctionSolver {
    /// No UF Solver
    None,
    /// Use the egraph solver (default)
    EGraph,
}

impl ToString for UninterpretedFunctionSolver {
    fn to_string(&self) -> String {
        match self {
            UninterpretedFunctionSolver::None => "none",
            UninterpretedFunctionSolver::EGraph => "default",
        }
        .to_string()
    }
}

impl FromStr for UninterpretedFunctionSolver {
    type Err = Error;
    fn from_str(s: &str) -> Result<Self> {
        match s {
            "none" => Ok(UninterpretedFunctionSolver::None),
            "default" => Ok(UninterpretedFunctionSolver::EGraph),
            _ => Err(Error::InvalidUninterpretedFunctionSolverName {
                uf_solver: s.to_string(),
            }),
        }
    }
}

impl AsKeyValue for UninterpretedFunctionSolver {
    fn as_kv(&self) -> (String, String) {
        ("uf-solver".to_string(), self.to_string())
    }
}

#[derive(Clone, Debug)]
pub enum BitVectorSolver {
    /// No BV Solver
    None,
    /// Use the bitvector solver (default)
    BitVector,
}

impl ToString for BitVectorSolver {
    fn to_string(&self) -> String {
        match self {
            BitVectorSolver::None => "none",
            BitVectorSolver::BitVector => "bv",
        }
        .to_string()
    }
}

impl FromStr for BitVectorSolver {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "none" => Ok(BitVectorSolver::None),
            "bv" => Ok(BitVectorSolver::BitVector),
            _ => Err(Error::InvalidBitVectorSolvername {
                bv_solver: s.to_string(),
            }),
        }
    }
}

impl AsKeyValue for BitVectorSolver {
    fn as_kv(&self) -> (String, String) {
        ("bv-solver".to_string(), self.to_string())
    }
}

#[derive(Clone, Debug)]
pub enum ArraySolver {
    /// No Array Solver
    None,
    /// Use the array solver (default)
    Array,
}

impl ToString for ArraySolver {
    fn to_string(&self) -> String {
        match self {
            ArraySolver::None => "none",
            ArraySolver::Array => "array",
        }
        .to_string()
    }
}

impl FromStr for ArraySolver {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "none" => Ok(ArraySolver::None),
            "array" => Ok(ArraySolver::Array),
            _ => Err(Error::InvalidArraySolverName {
                array_solver: s.to_string(),
            }),
        }
    }
}

impl AsKeyValue for ArraySolver {
    fn as_kv(&self) -> (String, String) {
        ("array-solver".to_string(), self.to_string())
    }
}

#[derive(Clone, Debug)]
pub enum ArithmeticSolver {
    /// No Arithmetic Solver
    None,
    /// Use the integer floyd-warshall solver
    IntegerFloydWarshall,
    /// Use the real floyd-warshall solver
    RealFloydWarshall,
    /// Use the simplex solver (default)
    Simplex,
    /// Use simplex unless mode is one-shot and logic is [`Logic::QF_IDL`] or [`Logic::QF_RDL`]
    Auto,
}

impl ToString for ArithmeticSolver {
    fn to_string(&self) -> String {
        match self {
            ArithmeticSolver::None => "none",
            ArithmeticSolver::IntegerFloydWarshall => "ifw",
            ArithmeticSolver::RealFloydWarshall => "rfw",
            ArithmeticSolver::Simplex => "simplex",
            ArithmeticSolver::Auto => "auto",
        }
        .to_string()
    }
}

impl FromStr for ArithmeticSolver {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "none" => Ok(ArithmeticSolver::None),
            "ifw" => Ok(ArithmeticSolver::IntegerFloydWarshall),
            "rfw" => Ok(ArithmeticSolver::RealFloydWarshall),
            "simplex" => Ok(ArithmeticSolver::Simplex),
            "auto" => Ok(ArithmeticSolver::Auto),
            _ => Err(Error::InvalidArithmeticSolverName {
                arith_solver: s.to_string(),
            }),
        }
    }
}

impl AsKeyValue for ArithmeticSolver {
    fn as_kv(&self) -> (String, String) {
        ("arith-solver".to_string(), self.to_string())
    }
}

#[derive(Clone, Debug)]
pub enum ArithmeticFragment {
    /// Integer Difference Logic
    IDL,
    /// Rational Difference Logic
    RDL,
    /// Linear Rational Arithmetic
    LRA,
    /// Linear Integer Arithmetic
    LIA,
    /// Linear Mixed Integer Real Arithmetic
    LIRA,
}

impl ToString for ArithmeticFragment {
    fn to_string(&self) -> String {
        match self {
            ArithmeticFragment::IDL => "IDL",
            ArithmeticFragment::RDL => "RDL",
            ArithmeticFragment::LRA => "LRA",
            ArithmeticFragment::LIA => "LIA",
            ArithmeticFragment::LIRA => "LIRA",
        }
        .to_string()
    }
}

impl FromStr for ArithmeticFragment {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "IDL" => Ok(ArithmeticFragment::IDL),
            "RDL" => Ok(ArithmeticFragment::RDL),
            "LRA" => Ok(ArithmeticFragment::LRA),
            "LIA" => Ok(ArithmeticFragment::LIA),
            "LIRA" => Ok(ArithmeticFragment::LIRA),
            _ => Err(Error::InvalidArithmeticFragmentName {
                arith_fragment: s.to_string(),
            }),
        }
    }
}

impl AsKeyValue for ArithmeticFragment {
    fn as_kv(&self) -> (String, String) {
        ("arith-fragment".to_string(), self.to_string())
    }
}

#[derive(Clone, Debug)]
pub enum Mode {
    OneShot,
    MultiChecks,
    PushPop,
    Interactive,
}

impl ToString for Mode {
    fn to_string(&self) -> String {
        match self {
            Mode::OneShot => "one-shot",
            Mode::MultiChecks => "multi-checks",
            Mode::PushPop => "push-pop",
            Mode::Interactive => "interactive",
        }
        .to_string()
    }
}

impl FromStr for Mode {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "one-shot" => Ok(Mode::OneShot),
            "multi-checks" => Ok(Mode::MultiChecks),
            "push-pop" => Ok(Mode::PushPop),
            "interactive" => Ok(Mode::Interactive),
            _ => Err(Error::InvalidConfigParameterValue {
                value: s.to_string(),
            }),
        }
    }
}

impl AsKeyValue for Mode {
    fn as_kv(&self) -> (String, String) {
        ("mode".to_string(), self.to_string())
    }
}

#[derive(Clone, Debug)]
pub enum ConfigurationParameter {
    SolverType(SolverType),
    UninterpretedFunctionSolver(UninterpretedFunctionSolver),
    BitVectorSolver(BitVectorSolver),
    ArraySolver(ArraySolver),
    ArithmeticSolver(ArithmeticSolver),
    Mode(Mode),
}

impl ToString for ConfigurationParameter {
    fn to_string(&self) -> String {
        match self {
            ConfigurationParameter::SolverType(s) => s.to_string(),
            ConfigurationParameter::UninterpretedFunctionSolver(u) => u.to_string(),
            ConfigurationParameter::BitVectorSolver(b) => b.to_string(),
            ConfigurationParameter::ArraySolver(a) => a.to_string(),
            ConfigurationParameter::ArithmeticSolver(a) => a.to_string(),
            ConfigurationParameter::Mode(m) => m.to_string(),
        }
    }
}

impl AsKeyValue for ConfigurationParameter {
    fn as_kv(&self) -> (String, String) {
        match self {
            ConfigurationParameter::SolverType(s) => s.as_kv(),
            ConfigurationParameter::UninterpretedFunctionSolver(u) => u.as_kv(),
            ConfigurationParameter::BitVectorSolver(b) => b.as_kv(),
            ConfigurationParameter::ArraySolver(a) => a.as_kv(),
            ConfigurationParameter::ArithmeticSolver(a) => a.as_kv(),
            ConfigurationParameter::Mode(m) => m.as_kv(),
        }
    }
}

#[derive(Clone, Debug)]
pub enum PreprocessingOption {
    /// Eliminate variables by substitution
    VariableElimination,
    /// Gaussian elimination
    ArithmeticElimination,
    /// Variable elimination for bitvector arithmetic
    BitVectorArithmeticElimination,
    /// Eager lemma generation for the Simplex solver
    EagerArithmeticLemmas,
    /// Flattening of nested (or ...)
    Flatten,
    /// Heuristic to learn equalities in QF_UF problems
    LearnEqualities,
    /// Keep if-then-else terms in the egraph
    KeepIfThenElse,
    /// Heuristic to detect and break symmetries in QF_UF problems
    BreakSymmetries,
    /// Attempt to learn and assert upper/lower bounds on if-then-else terms
    AssertIfThenElseBounds,
}

impl ToString for PreprocessingOption {
    fn to_string(&self) -> String {
        match self {
            PreprocessingOption::VariableElimination => "var-elim",
            PreprocessingOption::ArithmeticElimination => "arith-elim",
            PreprocessingOption::BitVectorArithmeticElimination => "bvarith-elim",
            PreprocessingOption::EagerArithmeticLemmas => "eager-arith-lemmas",
            PreprocessingOption::Flatten => "flatten",
            PreprocessingOption::LearnEqualities => "learn-eq",
            PreprocessingOption::KeepIfThenElse => "keep-ite",
            PreprocessingOption::BreakSymmetries => "break-symmetries",
            PreprocessingOption::AssertIfThenElseBounds => "assert-ite-bounds",
        }
        .to_string()
    }
}

impl FromStr for PreprocessingOption {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "var-elim" => Ok(PreprocessingOption::VariableElimination),
            "arith-elim" => Ok(PreprocessingOption::ArithmeticElimination),
            "bvarith-elim" => Ok(PreprocessingOption::BitVectorArithmeticElimination),
            "eager-arith-lemmas" => Ok(PreprocessingOption::EagerArithmeticLemmas),
            "flatten" => Ok(PreprocessingOption::Flatten),
            "learn-eq" => Ok(PreprocessingOption::LearnEqualities),
            "keep-ite" => Ok(PreprocessingOption::KeepIfThenElse),
            "break-symmetries" => Ok(PreprocessingOption::BreakSymmetries),
            "assert-ite-bounds" => Ok(PreprocessingOption::AssertIfThenElseBounds),
            _ => Err(Error::InvalidConfigParameterValue {
                value: s.to_string(),
            }),
        }
    }
}

#[derive(Clone, Debug)]
pub enum RestartHeuristic {
    FastRestart(bool),
    ConflictThreshold(i32),
    ConflictFactor(f32),
    DepthThreshold(i32),
    DepthFactor(f32),
}

impl ToString for RestartHeuristic {
    fn to_string(&self) -> String {
        match self {
            RestartHeuristic::FastRestart(b) => b.to_string(),
            RestartHeuristic::ConflictThreshold(i) => i.to_string(),
            RestartHeuristic::ConflictFactor(f) => f.to_string(),
            RestartHeuristic::DepthThreshold(i) => i.to_string(),
            RestartHeuristic::DepthFactor(f) => f.to_string(),
        }
    }
}

impl AsKeyValue for RestartHeuristic {
    fn as_kv(&self) -> (String, String) {
        (
            match self {
                RestartHeuristic::FastRestart(_) => "fast-restart",
                RestartHeuristic::ConflictThreshold(_) => "c-threshold",
                RestartHeuristic::ConflictFactor(_) => "c-factor",
                RestartHeuristic::DepthThreshold(_) => "d-threshold",
                RestartHeuristic::DepthFactor(_) => "d-factor",
            }
            .to_string(),
            self.to_string(),
        )
    }
}

#[derive(Clone, Debug)]
pub enum ClauseDeletion {
    ReductionThreshold(i32),
    ReductionFraction(f32),
    ReductionFactor(f32),
    ClauseDecay(f32),
}

impl ToString for ClauseDeletion {
    fn to_string(&self) -> String {
        match self {
            ClauseDeletion::ReductionThreshold(i) => i.to_string(),
            ClauseDeletion::ReductionFraction(f) => f.to_string(),
            ClauseDeletion::ReductionFactor(f) => f.to_string(),
            ClauseDeletion::ClauseDecay(f) => f.to_string(),
        }
    }
}

impl AsKeyValue for ClauseDeletion {
    fn as_kv(&self) -> (String, String) {
        (
            match self {
                ClauseDeletion::ReductionThreshold(_) => "r-threshold",
                ClauseDeletion::ReductionFraction(_) => "r-fraction",
                ClauseDeletion::ReductionFactor(_) => "r-factor",
                ClauseDeletion::ClauseDecay(_) => "clause-decay",
            }
            .to_string(),
            self.to_string(),
        )
    }
}

#[derive(Clone, Debug)]
pub enum DecisionHeuristic {
    VarDecay(f32),
    Randomness(f32),
}

impl ToString for DecisionHeuristic {
    fn to_string(&self) -> String {
        match self {
            DecisionHeuristic::VarDecay(f) => f.to_string(),
            DecisionHeuristic::Randomness(f) => f.to_string(),
        }
    }
}

impl AsKeyValue for DecisionHeuristic {
    fn as_kv(&self) -> (String, String) {
        (
            match self {
                DecisionHeuristic::VarDecay(_) => "var-decay",
                DecisionHeuristic::Randomness(_) => "randomness",
            }
            .to_string(),
            self.to_string(),
        )
    }
}

#[derive(Clone, Debug)]
pub enum BranchingMode {
    Default,
    Negative,
    Positive,
    Theory,
    TheoryNegative,
    TheoryPositive,
}

impl ToString for BranchingMode {
    fn to_string(&self) -> String {
        match self {
            BranchingMode::Default => "default",
            BranchingMode::Negative => "negative",
            BranchingMode::Positive => "positive",
            BranchingMode::Theory => "theory",
            BranchingMode::TheoryNegative => "theory-negative",
            BranchingMode::TheoryPositive => "theory-positive",
        }
        .to_string()
    }
}

impl AsKeyValue for BranchingMode {
    fn as_kv(&self) -> (String, String) {
        ("branching".to_string(), self.to_string())
    }
}

#[derive(Clone, Debug)]
pub enum LemmaGeneration {
    CacheTClauses(bool),
    TClauseSize(i32),
    DynamicAckermann(bool),
    MaximumAckermann(i32),
    DynamicAckermannThreshold(i32),
    DynamicBooleanAckermann(bool),
    MaximumBooleanAckermann(i32),
    DynamicBooleanAckermannThreshold(i32),
    AuxiliaryEqualitiesQuota(i32),
    AuxiliaryEqualitiesRatio(f32),
}

impl ToString for LemmaGeneration {
    fn to_string(&self) -> String {
        match self {
            LemmaGeneration::CacheTClauses(b) => b.to_string(),
            LemmaGeneration::TClauseSize(i) => i.to_string(),
            LemmaGeneration::DynamicAckermann(b) => b.to_string(),
            LemmaGeneration::MaximumAckermann(i) => i.to_string(),
            LemmaGeneration::DynamicAckermannThreshold(i) => i.to_string(),
            LemmaGeneration::DynamicBooleanAckermann(b) => b.to_string(),
            LemmaGeneration::MaximumBooleanAckermann(i) => i.to_string(),
            LemmaGeneration::DynamicBooleanAckermannThreshold(i) => i.to_string(),
            LemmaGeneration::AuxiliaryEqualitiesQuota(i) => i.to_string(),
            LemmaGeneration::AuxiliaryEqualitiesRatio(f) => f.to_string(),
        }
    }
}

impl AsKeyValue for LemmaGeneration {
    fn as_kv(&self) -> (String, String) {
        (
            match self {
                LemmaGeneration::CacheTClauses(_) => "cache-tclauses",
                LemmaGeneration::TClauseSize(_) => "tclause-size",
                LemmaGeneration::DynamicAckermann(_) => "dyn-ack",
                LemmaGeneration::MaximumAckermann(_) => "max-ack",
                LemmaGeneration::DynamicAckermannThreshold(_) => "dyn-ack-threshold",
                LemmaGeneration::DynamicBooleanAckermann(_) => "dyn-bool-ack",
                LemmaGeneration::MaximumBooleanAckermann(_) => "max-bool-ack",
                LemmaGeneration::DynamicBooleanAckermannThreshold(_) => "dyn-bool-ack-threshold",
                LemmaGeneration::AuxiliaryEqualitiesQuota(_) => "aux-eq-quota",
                LemmaGeneration::AuxiliaryEqualitiesRatio(_) => "aux-eq-ratio",
            }
            .to_string(),
            self.to_string(),
        )
    }
}

#[derive(Clone, Debug)]
pub enum Simplex {
    Propagation(bool),
    PropagationThreshold(i32),
    Adjust(bool),
    BlandThreshold(i32),
    IntegerCheck(bool),
    IntegerCheckPeriod(i32),
}

impl ToString for Simplex {
    fn to_string(&self) -> String {
        match self {
            Simplex::Propagation(b) => b.to_string(),
            Simplex::PropagationThreshold(i) => i.to_string(),
            Simplex::Adjust(b) => b.to_string(),
            Simplex::BlandThreshold(i) => i.to_string(),
            Simplex::IntegerCheck(b) => b.to_string(),
            Simplex::IntegerCheckPeriod(i) => i.to_string(),
        }
    }
}

impl AsKeyValue for Simplex {
    fn as_kv(&self) -> (String, String) {
        (
            match self {
                Simplex::Propagation(_) => "simplex-prop",
                Simplex::PropagationThreshold(_) => "prop-threshold",
                Simplex::Adjust(_) => "simplex-adjust",
                Simplex::BlandThreshold(_) => "bland-threshold",
                Simplex::IntegerCheck(_) => "icheck",
                Simplex::IntegerCheckPeriod(_) => "icheck-period",
            }
            .to_string(),
            self.to_string(),
        )
    }
}

#[derive(Clone, Debug)]
pub enum Array {
    MaxUpdateConflicts(i32),
    MaxExtensionality(i32),
}

impl ToString for Array {
    fn to_string(&self) -> String {
        match self {
            Array::MaxUpdateConflicts(i) => i.to_string(),
            Array::MaxExtensionality(i) => i.to_string(),
        }
    }
}

impl AsKeyValue for Array {
    fn as_kv(&self) -> (String, String) {
        (
            match self {
                Array::MaxUpdateConflicts(_) => "max-update-conflicts",
                Array::MaxExtensionality(_) => "max-extensionality",
            }
            .to_string(),
            self.to_string(),
        )
    }
}

#[derive(Clone, Debug)]
pub enum Reconciliation {
    OptimisticFinalCheck(bool),
    MaxInterfaceEqualities(i32),
}

impl ToString for Reconciliation {
    fn to_string(&self) -> String {
        match self {
            Reconciliation::OptimisticFinalCheck(b) => b.to_string(),
            Reconciliation::MaxInterfaceEqualities(i) => i.to_string(),
        }
    }
}

impl AsKeyValue for Reconciliation {
    fn as_kv(&self) -> (String, String) {
        (
            match self {
                Reconciliation::OptimisticFinalCheck(_) => "optimistic-final-check",
                Reconciliation::MaxInterfaceEqualities(_) => "max-interface-eqs",
            }
            .to_string(),
            self.to_string(),
        )
    }
}

#[derive(Clone, Debug)]
pub enum GeneralizationMode {
    None,
    Substitution,
    Projection,
    Auto,
}

impl ToString for GeneralizationMode {
    fn to_string(&self) -> String {
        match self {
            GeneralizationMode::None => "none",
            GeneralizationMode::Substitution => "substitution",
            GeneralizationMode::Projection => "projection",
            GeneralizationMode::Auto => "auto",
        }
        .to_string()
    }
}

impl FromStr for GeneralizationMode {
    type Err = Error;

    fn from_str(s: &str) -> Result<Self> {
        match s {
            "none" => Ok(GeneralizationMode::None),
            "substitution" => Ok(GeneralizationMode::Substitution),
            "projection" => Ok(GeneralizationMode::Projection),
            "auto" => Ok(GeneralizationMode::Auto),
            _ => Err(Error::InvalidGeneralizationMode {
                mode: s.to_string(),
            }),
        }
    }
}

#[derive(Clone, Debug)]
pub enum ExistsForall {
    MaxIters(i32),
    GeneralizationMode(GeneralizationMode),
    MaxSamples(i32),
    FlattenIff(bool),
    FlattenIfThenElse(bool),
}

impl ToString for ExistsForall {
    fn to_string(&self) -> String {
        match self {
            ExistsForall::MaxIters(i) => i.to_string(),
            ExistsForall::GeneralizationMode(g) => g.to_string(),
            ExistsForall::MaxSamples(i) => i.to_string(),
            ExistsForall::FlattenIff(b) => b.to_string(),
            ExistsForall::FlattenIfThenElse(b) => b.to_string(),
        }
    }
}

impl AsKeyValue for ExistsForall {
    fn as_kv(&self) -> (String, String) {
        (
            match self {
                ExistsForall::MaxIters(_) => "ef-max-iters",
                ExistsForall::GeneralizationMode(_) => "ef-gen-mode",
                ExistsForall::MaxSamples(_) => "ef-max-samples",
                ExistsForall::FlattenIff(_) => "ef-flatten-iff",
                ExistsForall::FlattenIfThenElse(_) => "ef-flatten-ite",
            }
            .to_string(),
            self.to_string(),
        )
    }
}

#[derive(Clone, Debug)]
pub enum Parameter {
    RestartHeuristic(RestartHeuristic),
    ClauseDeletion(ClauseDeletion),
    DecisionHeuristic(DecisionHeuristic),
    BranchingMode(BranchingMode),
    LemmaGeneration(LemmaGeneration),
    Simplex(Simplex),
    Array(Array),
    Reconciliation(Reconciliation),
    ExistsForall(ExistsForall),
}

impl ToString for Parameter {
    fn to_string(&self) -> String {
        match self {
            Parameter::RestartHeuristic(r) => r.to_string(),
            Parameter::ClauseDeletion(c) => c.to_string(),
            Parameter::DecisionHeuristic(d) => d.to_string(),
            Parameter::BranchingMode(b) => b.to_string(),
            Parameter::LemmaGeneration(l) => l.to_string(),
            Parameter::Simplex(s) => s.to_string(),
            Parameter::Array(a) => a.to_string(),
            Parameter::Reconciliation(r) => r.to_string(),
            Parameter::ExistsForall(e) => e.to_string(),
        }
    }
}

impl AsKeyValue for Parameter {
    fn as_kv(&self) -> (String, String) {
        match self {
            Parameter::RestartHeuristic(r) => r.as_kv(),
            Parameter::ClauseDeletion(c) => c.as_kv(),
            Parameter::DecisionHeuristic(d) => d.as_kv(),
            Parameter::BranchingMode(b) => b.as_kv(),
            Parameter::LemmaGeneration(l) => l.as_kv(),
            Parameter::Simplex(s) => s.as_kv(),
            Parameter::Array(a) => a.as_kv(),
            Parameter::Reconciliation(r) => r.as_kv(),
            Parameter::ExistsForall(e) => e.as_kv(),
        }
    }
}

/// Configuration settings for a Yices context
pub struct Config {
    /// Inner Yices context config pointer
    config: *mut ctx_config_t,
}

impl Config {
    /// Create a new configuration with no settings applied
    pub fn new() -> Result<Self> {
        let config = yices! { yices_new_config() };

        if config.is_null() {
            Err(Error::NewConfigFailed)
        } else {
            Ok(Self { config })
        }
    }

    pub fn with_defaults_for_logics<I>(logics: I) -> Result<Self>
    where
        I: IntoIterator<Item = Logic>,
    {
        let config = Self::new()?;

        for logic in logics {
            config.set_defaults_for_logic(&logic)?;
        }

        Ok(config)
    }

    pub fn with_defaults_for_logic_and_config_params<IL, IP>(logics: IL, params: IP) -> Result<Self>
    where
        IL: IntoIterator<Item = Logic>,
        IP: IntoIterator<Item = ConfigurationParameter>,
    {
        let config = Self::new()?;

        for logic in logics {
            config.set_defaults_for_logic(&logic)?;
        }

        for param in params {
            config.set_configuration_parameter(&param)?;
        }

        Ok(config)
    }

    /// Set a configuration key to a value
    ///
    ///
    pub fn set_configuration_parameter(&self, param: &ConfigurationParameter) -> Result<()> {
        let (key, value) = param.as_kv();
        let c_key = CString::new(key).map_err(|e| Error::External(e.into()))?;
        let c_value = CString::new(value).map_err(|e| Error::External(e.into()))?;

        if yices! { yices_set_config(self.config, c_key.as_ptr(), c_value.as_ptr()) } < 0 {
            Err(Error::SetConfigFailed {
                param: param.clone(),
            })
        } else {
            Ok(())
        }
    }

    pub fn set_defaults_for_logic(&self, logic: &Logic) -> Result<()> {
        let c_logic = CString::new(logic.to_string()).map_err(|e| Error::External(e.into()))?;
        let ok = yices! { yices_default_config_for_logic(self.config, c_logic.as_ptr()) };

        if ok < 0 {
            Err(Error::DefaultConfigForLogic {
                logic: logic.clone(),
            })
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

pub struct Params {
    params: *mut param_t,
}

impl Params {
    pub fn new() -> Result<Self> {
        let param = yices! { yices_new_param_record() };

        if param.is_null() {
            Err(Error::NewParameterFailed)
        } else {
            Ok(Self { params: param })
        }
    }

    pub fn with_params<I>(params: I) -> Result<Self>
    where
        I: IntoIterator<Item = Parameter>,
    {
        let with_params = Self::new()?;

        for param in params {
            with_params.set_parameter(&param)?;
        }

        Ok(with_params)
    }

    pub fn set_parameter(&self, param: &Parameter) -> Result<()> {
        let (key, value) = param.as_kv();
        let key = CString::new(key).map_err(|e| Error::External(e.into()))?;
        let value = CString::new(value).map_err(|e| Error::External(e.into()))?;

        if yices! { yices_set_param(self.params, key.as_ptr(), value.as_ptr()) } != 0 {
            Err(Error::InvalidParameter {
                param: param.clone(),
            })
        } else {
            Ok(())
        }
    }

    pub fn set_default_for_context(&self, context: &Context) -> Result<()> {
        yices! { yices_default_params_for_context(context.context, self.params) };
        Ok(())
    }
}

impl Drop for Params {
    fn drop(&mut self) {
        if yices_try! { yices_free_param_record(self.params) }.is_err() {
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
            Err(Error::NewContextFailed)
        } else {
            Ok(Self { context })
        }
    }

    pub fn with_config(config: &Config) -> Result<Self> {
        let context = yices! { yices_new_context(config.config) };

        if context.is_null() {
            Err(Error::NewContextWithConfigFailed)
        } else {
            Ok(Self { context })
        }
    }

    pub fn enable_option(&self, option: &PreprocessingOption) -> Result<()> {
        let option = CString::new(option.to_string()).map_err(|e| Error::External(e.into()))?;

        yices! { yices_context_enable_option(self.context, option.as_ptr()) };

        Ok(())
    }

    pub fn disable_option(&self, option: &PreprocessingOption) -> Result<()> {
        let option = CString::new(option.to_string()).map_err(|e| Error::External(e.into()))?;

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

    pub fn check_with_params(&self, params: Option<&Params>) -> Result<Status> {
        let params = params.map_or(null(), |p| p.params);

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

        if ok < 0 {
            Err(Error::AssertBlockingFailed)
        } else {
            Ok(())
        }
    }

    pub fn push(&self) -> Result<()> {
        let ok = yices! { yices_push(self.context) };

        if ok < 0 {
            Err(Error::PushContextFailed)
        } else {
            Ok(())
        }
    }

    pub fn pop(&self) -> Result<()> {
        let ok = yices! { yices_pop(self.context) };

        if ok < 0 {
            Err(Error::PopContextFailed)
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
        params: Option<&Params>,
        terms: I,
    ) -> Result<Status>
    where
        I: IntoIterator<Item = Term>,
    {
        let params = params.map_or(null(), |p| p.params);
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

        if ok < 0 {
            yices! { yices_delete_term_vector(&mut tv as *mut term_vector_t) };
            Err(Error::UnsatCoreContextFailed)
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
            Err(Error::ModelInterpolantFailed)
        } else {
            Ok(term.into())
        }
    }

    pub fn model(&self) -> Result<Model> {
        let model = yices! { yices_get_model(self.context, 0) };

        if model.is_null() {
            Err(Error::ModelForContextFailed)
        } else {
            Ok(Model::from(model))
        }
    }

    pub fn model_with_eliminated(&self) -> Result<Model> {
        let model = yices! { yices_get_model(self.context, 1) };

        if model.is_null() {
            Err(Error::ModelForContextFailed)
        } else {
            Ok(Model::from(model))
        }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        if yices_try! { yices_free_context(self.context) }.is_err() {
            panic!("Failed to free Yices context");
        }
    }
}
