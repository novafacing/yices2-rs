# Yices2

High level bindings to the Yices2 SMT solver.

## Examples

Some examples to demonstrate usage of this library.

### Linear Real Arithmetic

```rust,no_run
use yices2::prelude::*;

fn main() -> Result<(), Error> {
  let config = Config::with_defaults_for_logics([Logic::QF_LRA])?;
  let ctx = Context::with_config(&config)?;
  let x = Uninterpreted::with_name(RealType::new()?, "x")?;
  let y = Uninterpreted::with_name(RealType::new()?, "y")?;
  let t1 = Add::new(x, y)?;
  let t2: Term = ArithmeticGreaterThanAtom::new(t1, ArithmeticConstant::zero()?)?.into();
  let t3: Term = Or::new([
      ArithmeticLessThanAtom::new(x, ArithmeticConstant::zero()?)?,
      ArithmeticLessThanAtom::new(y, ArithmeticConstant::zero()?)?,
  ])?.into();
  ctx.assert([t2, t3])?;
  let status = ctx.check()?;
  assert_eq!(status, Status::STATUS_SAT);
  let xv = ctx.model()?.get_double(x)?;
  let yv = ctx.model()?.get_double(y)?;
  assert_eq!(xv, 2.0);
  assert_eq!(yv, -1.0);

  Ok(())
}
```

### BitVectors

```rust,no_run
use yices2::prelude::*;

fn main() -> Result<(), Error> {
  let config = Config::with_defaults_for_logics([Logic::QF_BV])?;
  let ctx = Context::with_config(&config)?;
  let bv = BitVectorType::new(32)?;
  let bvc = BitVectorConstant::from_hex_with_name("00000000", "c")?;
  let x = Uninterpreted::with_name(bv, "x")?;
  let y = Uninterpreted::with_name(bv, "y")?;
  let a1: Term = BitVectorSignedGreaterThanAtom::new(x, bvc)?.into();
  let a2: Term = BitVectorSignedGreaterThanAtom::new(y, bvc)?.into();
  let a3: Term = BitVectorSignedLessThanAtom::new(
      BitVectorAdd::new(x, y)?,
      x,
  )?.into();
  ctx.assert([a1, a2, a3])?;

  assert_eq!(ctx.check()?, Status::STATUS_SAT);

  Ok(())
}
```

## Usage

You can add this crate to your project by running:

```sh
cargo add yices2
```

Or by adding this line to your `Cargo.toml` (note the patch pseudo-prerelease flag. In
order to maintain version number compatibility with Yices2, changes to the `sys` crate
will be made available under linearly increasing patch versions):

```toml
yices2 = { version = "2.6.4-patch.1" }
```

## Features

By default, `yices2` enables the `ctor` feature, which calls `yices_init` at program
initialization and `yices_exit` at program exit. If you'd like to disable this behavior,
you can use the `default-features = false` flag in your `Cargo.toml`.

```toml
yices2 = { version = "2.6.4-patch.1", default-features = false }
```

## Notes

This library is not thread safe, because the underlying `Yices2` library is not thread
safe. Do not use this library in multithreaded code. To use in multi-threaded code,
create a separate process and submit requests to the solver running in that process or
disable the `ctor` feature and manage state yourself.