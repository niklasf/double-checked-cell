double-checked-cell
===================

A thread-safe lazily initialized cell using double-checked locking.

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
