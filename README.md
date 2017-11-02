double-checked-cell
===================

A thread-safe lazily initialized cell using double-checked locking.

[![Build Status](https://travis-ci.org/niklasf/double-checked-cell.svg?branch=master)](https://travis-ci.org/niklasf/double-checked-cell)
[![crates.io](https://img.shields.io/crates/v/double-checked-cell.svg)](https://crates.io/crates/double-checked-cell)

Introduction
------------

Provides a memory location that can be safely shared between threads and
initialized at most once. Once the cell is initialized it becomes immutable.

If you do not need to change the value after initialization
`DoubleCheckedCell<T>` is more efficient than a `Mutex<Option<T>>`.

```rust
extern crate double_checked_cell;

use double_checked_cell::DoubleCheckedCell;

let cell = DoubleCheckedCell::new();

// The cell starts uninitialized.
assert_eq!(cell.get(), None);

// Perform potentially expensive initialization.
let value = cell.get_or_init(|| 21 + 21);
assert_eq!(*value, 42);
assert_eq!(cell.get(), Some(&42));

// The cell is already initialized.
let value = cell.get_or_init(|| {
    panic!("initilization does not run again")
});
assert_eq!(*value, 42);
assert_eq!(cell.get(), Some(&42));
```


Related crates
--------------

These crates are similar but distinct by design:

* [lazy-init](https://crates.io/crates/lazy-init) – Based on a `LazyTransform<T, U>` which can lazily consume `T` to produce an `U`. Therefore can not support fallible initialization.
* [lazycell](https://crates.io/crates/lazycell) – `AtomicLazyCell` does not support lazy initialization (unlike it's non-thread-safe counterpart `LazyCell` using `LazyCell::borrow_with()`).

Documentation
-------------

[Read the documentation](https://docs.rs/double-checked-cell)

Changelog
---------

* 1.0.0
  - Initial release.

License
-------

double-checked-cell is licensed under the [Apache 2.0](http://www.apache.org/licenses/LICENSE-2.0)
and [MIT](http://opensource.org/licenses/MIT) license, at your option.
