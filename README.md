# Yices2

Low and high-level Rust bindings to the [Yices2](https://yices.csl.sri.com) SMT solver.

- [Yices2](#yices2)
  - [Example](#example)
    - [Linear Real Arithmetic](#linear-real-arithmetic)
    - [BitVectors](#bitvectors)
  - [Usage](#usage)
  - [Features](#features)
  - [Notes](#notes)

## Example

### Linear Real Arithmetic

```rust
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
```

### BitVectors

```rust
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
```

## Usage

You can add this crate to your project by running:

```sh
cargo add yices2
```

Or by adding this line to your `Cargo.toml`:

```toml
yices2 = { version = "2.6.4" }
```

## Features

By default, `yices2` enables the `ctor` feature, which calls `yices_init` at program
initialization and `yices_exit` at program exit. If you'd like to disable this behavior,
you can use the `default-features = false` flag in your `Cargo.toml`.

```toml
yices2 = { version = "2.6.4", default-features = false }
```

## Notes

This library is not thread safe, because the underlying `Yices2` library is not thread
safe. Do not use this library in multithreaded code. To use in multi-threaded code,
create a separate process and submit requests to the solver running in that process or
disable the `ctor` feature and manage state yourself.