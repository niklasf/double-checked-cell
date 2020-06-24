double-checked-cell
===================

A thread-safe lazily initialized cell using double-checked locking.

[![Build Status](https://travis-ci.org/niklasf/double-checked-cell.svg?branch=master)](https://travis-ci.org/niklasf/double-checked-cell)
[![crates.io](https://img.shields.io/crates/v/double-checked-cell.svg)](https://crates.io/crates/double-checked-cell)
[![docs.rs](https://docs.rs/double-checked-cell/badge.svg)](https://docs.rs/double-checked-cell)
[![Passively maintained](https://img.shields.io/badge/passively%20maintained-x-yellow.svg)](#)

Introduction
------------

Provides a memory location that can be safely shared between threads and
initialized at most once. Once the cell is initialized it becomes immutable.

If you do not need to change the value after initialization
`DoubleCheckedCell<T>` is more efficient than a `Mutex<Option<T>>`.

```rust
extern crate double_checked_cell;

use double_checked_cell::DoubleCheckedCell;

fn main() {
    let cell = DoubleCheckedCell::new();

    // The cell starts uninitialized.
    assert_eq!(cell.get(), None);

    // Perform potentially expensive initialization.
    let value = cell.get_or_init(|| 21 + 21);
    assert_eq!(*value, 42);
    assert_eq!(cell.get(), Some(&42));

    // The cell is already initialized.
    let value = cell.get_or_init(|| unreachable!());
    assert_eq!(*value, 42);
    assert_eq!(cell.get(), Some(&42));
}
```

Related crates
--------------

* [once_cell](https://crates.io/crates/once_cell) - Provides a superset of this crate's functionality, with a nicely consistent API.

These crates are similar but distinct by design:

* [lazy-init](https://crates.io/crates/lazy-init) – Based on a `LazyTransform<T, U>` which can lazily consume `T` to produce an `U`. Therefore cannot support fallible initialization.
* [lazycell](https://crates.io/crates/lazycell) – `AtomicLazyCell` does not support lazy initialization (unlike its non-thread-safe counterpart `LazyCell` using `LazyCell::borrow_with()`).
* [mitochondria](https://crates.io/crates/mitochondria) – Not `Sync`.
* [lazy_static](https://crates.io/crates/lazy_static) - With the optional (currently nightly only) `const_fn` feature, `DoubleCheckedCell::new()` can also be used in static/const context. However `lazy_static!` is more convenient when there is only a single way to initialize the cell.

Documentation
-------------

[Read the documentation](https://docs.rs/double-checked-cell)

Changelog
---------

* 2.0.3
  - Update to parking_lot 0.11.
* 2.0.2
  - Update to parking_lot 0.9.
* 2.0.1
  - Update to parking_lot 0.7.
* 2.0.0
  - Changed unwinding behavior: `DoubleCheckedCell` no longer implements
    poisoning.
  - New optional cargo features: `parking_lot_mutex`, `const_fn`.
* 1.1.0
  - Fix unsoundness: `DoubleCheckedCell<T>` where `T: !Send` cannot be `Sync`.
* 1.0.1
  - Ignore `unused_unsafe` warning due to `UnsafeCell::into_inner()` no longer
    beeing unsafe.
* 1.0.0
  - Initial release.

License
-------

double-checked-cell is licensed under the [Apache 2.0](http://www.apache.org/licenses/LICENSE-2.0)
and [MIT](http://opensource.org/licenses/MIT) license, at your option.
