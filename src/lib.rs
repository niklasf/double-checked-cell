// Copyright 2017-2018 Niklas Fiekas <niklas.fiekas@backscattering.de>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A thread-safe lazily initialized cell using double-checked locking.
//!
//! Provides a memory location that can be safely shared between threads and
//! initialized at most once. Once the cell is initialized it becomes
//! immutable.
//!
//! You can only initialize a `DoubleCheckedCell<T>` once, but then it is
//! more efficient than a `Mutex<Option<T>>`.
//!
//! # Examples
//!
//! ```
//! use double_checked_cell::DoubleCheckedCell;
//!
//! let cell = DoubleCheckedCell::new();
//!
//! // The cell starts uninitialized.
//! assert_eq!(cell.get(), None);
//!
//! // Perform potentially expensive initialization.
//! let value = cell.get_or_init(|| 21 + 21);
//! assert_eq!(*value, 42);
//! assert_eq!(cell.get(), Some(&42));
//!
//! // The cell is already initialized.
//! let value = cell.get_or_init(|| unreachable!());
//! assert_eq!(*value, 42);
//! assert_eq!(cell.get(), Some(&42));
//! ```
//!
//! # Errors
//!
//! `DoubleCheckedCell` supports fallible initialization.
//!
//! ```
//! use std::fs::File;
//! use std::io;
//! use std::io::prelude::*;
//! use double_checked_cell::DoubleCheckedCell;
//!
//! let cell = DoubleCheckedCell::new();
//!
//! let contents: io::Result<&String> = cell.get_or_try_init(|| {
//!     let mut file = File::open("not-found.txt")?;
//!     let mut contents = String::new();
//!     file.read_to_string(&mut contents)?;
//!     Ok(contents)
//! });
//!
//! // File not found.
//! assert!(contents.is_err());
//!
//! // Cell remains uninitialized for now.
//! assert_eq!(cell.get(), None);
//! ```
//!
//! # Unwind safety
//!
//! If an initialization closure panics, the `DoubleCheckedCell` remains
//! uninitialized. Initialization can be retried later, there is no poisoning.
//!
//! ```
//! use std::panic;
//! use double_checked_cell::DoubleCheckedCell;
//!
//! let cell = DoubleCheckedCell::new();
//!
//! // Panic during initialization.
//! assert!(panic::catch_unwind(|| {
//!     cell.get_or_init(|| panic!("oh no!"));
//! }).is_err());
//!
//! // Cell remains uninitialized.
//! assert!(cell.get().is_none());
//! ```
//!
//! # Cargo features
//!
//! * `parking_lot_mutex`: Internally use mutexes backed by
//!   [parking_lot](https://crates.io/crates/parking_lot). Optional.
//! * `const_fn`: Allows instanciating `DoubleCheckedCell` in const context.
//!   Can be used as a replacement for
//!   [lazy_static](https://crates.io/crates/lazy_static).
//!   Currently nightly only. Optional.
//!
//!   ```rust,ignore
//!   static LAZY_STATIC: DoubleCheckedCell<u32> = DoubleCheckedCell::new();
//!   ```

#![doc(html_root_url = "https://docs.rs/double-checked-cell/2.0.3")]
#![warn(missing_debug_implementations)]

#[cfg(feature = "parking_lot_mutex")]
extern crate parking_lot;
extern crate unreachable;
extern crate void;

use std::cell::UnsafeCell;
use std::fmt;
use std::panic::{UnwindSafe, RefUnwindSafe};
use std::sync::atomic::{AtomicBool, Ordering};

use unreachable::UncheckedOptionExt;
use void::ResultVoidExt;

/// A thread-safe lazily initialized cell.
///
/// The cell is immutable once it is initialized.
/// See the [module-level documentation](index.html) for more.
pub struct DoubleCheckedCell<T> {
    value: UnsafeCell<Option<T>>,
    initialized: AtomicBool,
    #[cfg(not(feature = "parking_lot_mutex"))]
    lock: std::sync::Mutex<()>,
    #[cfg(feature = "parking_lot_mutex")]
    lock: parking_lot::Mutex<()>,
}

impl<T> Default for DoubleCheckedCell<T> {
    fn default() -> DoubleCheckedCell<T> {
        DoubleCheckedCell::new()
    }
}

impl<T: fmt::Debug> fmt::Debug for DoubleCheckedCell<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("DoubleCheckedCell")
            .field("value", &self.get())
            .finish()
    }
}

impl<T> DoubleCheckedCell<T> {
    /// Creates a new uninitialized `DoubleCheckedCell`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_checked_cell::DoubleCheckedCell;
    ///
    /// let cell = DoubleCheckedCell::<u32>::new();
    /// assert_eq!(cell.get(), None);
    /// ```
    #[cfg(not(feature = "const_fn"))]
    pub fn new() -> DoubleCheckedCell<T> {
        DoubleCheckedCell {
            value: UnsafeCell::new(None),
            initialized: AtomicBool::new(false),
            #[cfg(not(feature = "parking_lot_mutex"))]
            lock: std::sync::Mutex::new(()),
            #[cfg(feature = "parking_lot_mutex")]
            lock: parking_lot::Mutex::new(()),
        }
    }

    /// Creates a new uninitialized `DoubleCheckedCell`.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_checked_cell::DoubleCheckedCell;
    ///
    /// let cell = DoubleCheckedCell::<u32>::new();
    /// assert_eq!(cell.get(), None);
    /// ```
    #[cfg(feature = "const_fn")]
    pub const fn new() -> DoubleCheckedCell<T> {
        DoubleCheckedCell {
            value: UnsafeCell::new(None),
            initialized: AtomicBool::new(false),
            lock: parking_lot::Mutex::new(()),
        }
    }

    /// Borrows the value if the cell is initialized.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_checked_cell::DoubleCheckedCell;
    ///
    /// let cell = DoubleCheckedCell::from("hello");
    /// assert_eq!(cell.get(), Some(&"hello"));
    /// ```
    pub fn get(&self) -> Option<&T> {
        self.get_or_try_init(|| Err(())).ok()
    }

    /// Borrows the value if the cell is initialized or initializes it from
    /// a closure.
    ///
    /// # Panics
    ///
    /// Panics or deadlocks when trying to access the cell from the
    /// initilization closure.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use double_checked_cell::DoubleCheckedCell;
    ///
    /// let cell = DoubleCheckedCell::new();
    ///
    /// // Initialize the cell.
    /// let value = cell.get_or_init(|| 1 + 2);
    /// assert_eq!(*value, 3);
    ///
    /// // The cell is now immutable.
    /// let value = cell.get_or_init(|| 42);
    /// assert_eq!(*value, 3);
    /// ```
    pub fn get_or_init<F>(&self, init: F) -> &T
    where
        F: FnOnce() -> T,
    {
        self.get_or_try_init(|| Ok(init())).void_unwrap()
    }

    /// Borrows the value if the cell is initialized or attempts to initialize
    /// it from a closure.
    ///
    /// # Errors
    ///
    /// Forwards any error from the closure if the cell is not yet initialized.
    /// The cell then remains uninitialized.
    ///
    /// # Panics
    ///
    /// Panics or deadlocks when trying to access the cell from the
    /// initilization closure.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_checked_cell::DoubleCheckedCell;
    ///
    /// let cell = DoubleCheckedCell::new();
    ///
    /// let result = cell.get_or_try_init(|| "not an integer".parse());
    /// assert!(result.is_err());
    ///
    /// let result = cell.get_or_try_init(|| "42".parse());
    /// assert_eq!(result, Ok(&42));
    ///
    /// let result = cell.get_or_try_init(|| "irrelevant".parse());
    /// assert_eq!(result, Ok(&42));
    /// ```
    pub fn get_or_try_init<F, E>(&self, init: F) -> Result<&T, E>
    where
        F: FnOnce() -> Result<T, E>,
    {
        // Safety comes down to the double checked locking here. All other
        // borrowing methods are implemented by calling this.

        if !self.initialized.load(Ordering::Acquire) {
            // Lock the internal mutex.
            #[cfg(not(feature = "parking_lot_mutex"))]
            let _lock = self.lock.lock().unwrap_or_else(|poison| poison.into_inner());
            #[cfg(feature = "parking_lot_mutex")]
            let _lock = self.lock.lock();

            if !self.initialized.load(Ordering::Relaxed) {
                // We claim that it is safe to make a mutable reference to
                // `self.value` because no other references exist. The only
                // places that could have taken another reference are
                // (A) and (B).
                //
                // We will be the only one holding a mutable reference, because
                // we are holding a mutex. The mutex guard lives longer
                // than the reference taken at (A).
                //
                // No thread could have reached (B) yet, because that implies
                // the cell is already initialized. When we last checked the
                // cell was not yet initialized, and no one else could have
                // initialized it, because that requires holding the mutex.
                {
                    let value = unsafe { &mut *self.value.get() }; // (A)

                    // Consider all possible control flows:
                    // - init returns Ok(T)
                    // - init returns Err(E)
                    // - init recursively tries to initialize the cell
                    // - init panics
                    *value = Some(init()?);
                }

                self.initialized.store(true, Ordering::Release);
            }
        }

        // The cell is now guaranteed to be initialized.

        // We claim that it is safe to take a shared reference of `self.value`.
        // The only place that could have created a conflicting mutable
        // reference is (A). But no one can be in that scope while the cell
        // is already initialized.
        let value = unsafe { &*self.value.get() }; // (B)

        // Value is guaranteed to be initialized.
        Ok(unsafe { value.as_ref().unchecked_unwrap() })
    }

    /// Unwraps the value.
    ///
    /// # Examples
    ///
    /// ```
    /// use double_checked_cell::DoubleCheckedCell;
    ///
    /// let cell = DoubleCheckedCell::from(42);
    /// let contents = cell.into_inner();
    /// assert_eq!(contents, Some(42));
    /// ```
    pub fn into_inner(self) -> Option<T> {
        // into_inner() is actually unconditionally safe:
        // https://github.com/rust-lang/rust/issues/35067
        #[allow(unused_unsafe)]
        unsafe { self.value.into_inner() }
    }
}

impl<T> From<T> for DoubleCheckedCell<T> {
    fn from(t: T) -> DoubleCheckedCell<T> {
        let cell = DoubleCheckedCell::new();
        cell.get_or_init(|| t);
        cell
    }
}

// Can DoubleCheckedCell<T> be Sync?
//
// The internal state of the DoubleCheckedCell is only mutated while holding
// a mutex, so we only need to consider T.
//
// We need T: Send, because we can share a DoubleCheckedCell with another
// thread, initialize it there and unpack it on the original thread.
// We trivially need T: Sync, because a reference to the contents can be
// retrieved on multiple threads.
unsafe impl<T: Send + Sync> Sync for DoubleCheckedCell<T> {}

// A panic during initialization will leave the cell in a valid, uninitialized
// state.
impl<T: RefUnwindSafe + UnwindSafe> RefUnwindSafe for DoubleCheckedCell<T> {}
impl<T: UnwindSafe> UnwindSafe for DoubleCheckedCell<T> {}

#[cfg(test)]
extern crate scoped_pool;

#[cfg(test)]
mod tests {
    use super::*;

    use std::rc::Rc;
    use std::sync::atomic::AtomicUsize;

    use scoped_pool::Pool;

    #[test]
    fn test_drop() {
        let rc = Rc::new(true);
        assert_eq!(Rc::strong_count(&rc), 1);

        {
            let cell = DoubleCheckedCell::new();
            cell.get_or_init(|| rc.clone());

            assert_eq!(Rc::strong_count(&rc), 2);
        }

        assert_eq!(Rc::strong_count(&rc), 1);
    }

    #[test]
    fn test_threading() {
        let n = AtomicUsize::new(0);
        let cell = DoubleCheckedCell::new();

        let pool = Pool::new(32);

        pool.scoped(|scope| {
            for _ in 0..1000 {
                scope.execute(|| {
                    let value = cell.get_or_init(|| {
                        n.fetch_add(1, Ordering::Relaxed);
                        true
                    });

                    assert!(*value);
                });
            }
        });

        assert_eq!(n.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn test_sync_send() {
        fn assert_sync<T: Sync>(_: T) {}
        fn assert_send<T: Send>(_: T) {}

        assert_sync(DoubleCheckedCell::<usize>::new());
        assert_send(DoubleCheckedCell::<usize>::new());
    }

    #[cfg(feature = "const_fn")]
    #[test]
    fn test_static_cell() {
        fn wrapper(v: u32) -> u32 {
            static STATIC_CELL: DoubleCheckedCell<u32> = DoubleCheckedCell::new();
            *STATIC_CELL.get_or_init(|| v)
        }

        assert_eq!(wrapper(1), 1);
        assert_eq!(wrapper(2), 1);
        assert_eq!(wrapper(3), 1);
    }

    struct _AssertObjectSafe(Box<DoubleCheckedCell<usize>>);
}
