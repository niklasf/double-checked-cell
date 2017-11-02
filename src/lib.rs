// Copyright 2017 Niklas Fiekas <niklas.fiekas@backscattering.de>
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
//! If you do not need to change the value after initialization
//! `DoubleCheckedCell<T>` is more efficient than a `Mutex<Option<T>>`.
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
//! let value = cell.get_or_init(|| {
//!     panic!("initilization does not run again")
//! });
//! assert_eq!(*value, 42);
//! assert_eq!(cell.get(), Some(&42));
//! ```
//!
//! # Poisoning
//!
//! `DoubleCheckedCell` achieves unwind safety by implementing "poisoning".
//! If an initilization closure is executed and panics, the `DoubleCheckedCell`
//! becomes poisoned. Any subsequent reads will then also panic.
//!
//! ```
//! use std::panic;
//! use double_checked_cell::DoubleCheckedCell;
//!
//! let cell = DoubleCheckedCell::new();
//!
//! // Cell gets poisoned.
//! assert!(panic::catch_unwind(|| {
//!     cell.get_or_init(|| panic!("oh no!"));
//! }).is_err());
//!
//! // Now it is poisoned forever.
//! assert!(panic::catch_unwind(|| {
//!     cell.get_or_init(|| true);
//! }).is_err());
//! ```

#![warn(missing_debug_implementations)]

extern crate void;
extern crate unreachable;

use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};
use std::cell::UnsafeCell;
use std::panic::RefUnwindSafe;
use std::fmt;

use void::ResultVoidExt;
use unreachable::UncheckedOptionExt;

/// A thread-safe lazily initialized cell.
///
/// The cell is immutable once it is initialized.
/// See the [module-level documentation](index.html) for more.
pub struct DoubleCheckedCell<T> {
    initialized: AtomicBool,
    lock: Mutex<()>,
    value: UnsafeCell<Option<T>>,
}

impl<T> Default for DoubleCheckedCell<T> {
    fn default() -> DoubleCheckedCell<T> {
        DoubleCheckedCell {
            initialized: AtomicBool::new(false),
            lock: Mutex::new(()),
            value: UnsafeCell::new(None),
        }
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
    pub fn new() -> DoubleCheckedCell<T> {
        Self::default()
    }

    /// Borrows the value if the cell is initialized.
    ///
    /// # Panics
    ///
    /// Panics if the cell is [poisoned](index.html#poisoning).
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
    /// Panics if the cell is [poisoned](index.html#poisoning).
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
        where F: FnOnce() -> T
    {
        self.get_or_try_init(|| Ok(init())).void_unwrap()
    }

    /// Borrows the value if the cell is initialized or attempts to initialize
    /// it from a closure.
    ///
    /// # Errors
    ///
    /// Forwards errors from the closure if the cell is not yet initialized.
    ///
    /// # Panics
    ///
    /// Panics if the cell is [poisoned](index.html#poisoning).
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
        where F: FnOnce() -> Result<T, E>
    {
        if !self.initialized.load(Ordering::Acquire) {
            let _lock = self.lock.lock().unwrap();

            if !self.initialized.load(Ordering::Relaxed) {
                // There are no shared references to value because it is
                // not yet initialized.
                // There are no mutable references to value because we are
                // holding a mutex.
                let value = unsafe { &mut *self.value.get() };
                *value = Some(init()?);
                self.initialized.store(true, Ordering::Release);
            }
        }

        // The value is now guaranteed to be initialized. This means no one
        // is holding the mutex self.lock, and no one is holding a mutable
        // reference.
        let value = unsafe { &*self.value.get() };

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
        // This method consumes self. Therefore no references can be around.
        unsafe { self.value.into_inner() }
    }
}

impl<T> From<T> for DoubleCheckedCell<T> {
    fn from(t: T) -> DoubleCheckedCell<T> {
        DoubleCheckedCell {
            initialized: AtomicBool::new(true),
            lock: Mutex::new(()),
            value: UnsafeCell::new(Some(t)),
        }
    }
}

// The internal state is only mutated while holding a mutex.
unsafe impl<T: Sync> Sync for DoubleCheckedCell<T> { }

// A panic during initialization will poison the interal mutex, thereby
// poisoning the cell itself.
impl<T> RefUnwindSafe for DoubleCheckedCell<T> { }

#[cfg(test)]
extern crate scoped_pool;

#[cfg(test)]
mod tests {
    use super::*;

    use std::sync::atomic::AtomicUsize;
    use std::rc::Rc;

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
        fn assert_sync<T: Sync>(_: T) { }
        fn assert_send<T: Send>(_: T) { }

        assert_sync(DoubleCheckedCell::<usize>::new());
        assert_send(DoubleCheckedCell::<usize>::new());
    }

    struct _AssertObjectSafe(Box<DoubleCheckedCell<usize>>);
}
