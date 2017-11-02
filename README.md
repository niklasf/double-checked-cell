double-checked-cell
===================

A thread-safe lazily initialized cell using double-checked locking.

Related crates
--------------

* [lazy-init](https://crates.io/crates/lazy-init) ![](https://img.shields.io/crates/v/lazy-init.svg) – Very similar. Based on a `LazyTransform<T, U>` which can lazily consume `T` to produce an `U`, and therefore can not support fallible initialization.
* [lazycell](https://crates.io/crates/lazycell) ![](https://img.shields.io/crates/v/lazycell.svg) – `AtomicLazyCell` does not support lazy initialization like the non-sync `LazyCell::borrow_with()`.

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
