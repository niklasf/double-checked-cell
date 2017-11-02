// Copyright 2017 Niklas Fiekas <niklas.fiekas@backscattering.de>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate void;
extern crate unreachable;

use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};
use std::cell::UnsafeCell;
use std::panic::RefUnwindSafe;

use void::ResultVoidExt;
use unreachable::UncheckedOptionExt;

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

impl<T> DoubleCheckedCell<T> {
    pub fn new() -> DoubleCheckedCell<T> {
        Self::default()
    }

    pub fn into_inner(self) -> Option<T> {
        unsafe { self.value.into_inner() }
    }

    pub fn get_or_try_init<F, E>(&self, init: F) -> Result<&T, E>
        where F: FnOnce() -> Result<T, E>
    {
        if !self.initialized.load(Ordering::Acquire) {
            let _lock = self.lock.lock().unwrap();

            if !self.initialized.load(Ordering::Relaxed) {
                let value = unsafe { &mut *self.value.get() };
                *value = Some(init()?);
                self.initialized.store(true, Ordering::Release);
            }
        }

        let value = unsafe { &*self.value.get() };
        Ok(unsafe { value.as_ref().unchecked_unwrap() })
    }

    pub fn get_or_init<F>(&self, init: F) -> &T
        where F: FnOnce() -> T
    {
        self.get_or_try_init(|| Ok(init())).void_unwrap()
    }

    pub fn get(&self) -> Option<&T> {
        self.get_or_try_init(|| Err(())).ok()
    }
}

// A panic during initialization will poison the interal mutex, thereby
// poisoning the cell itself.
impl<T> RefUnwindSafe for DoubleCheckedCell<T> { }

#[cfg(test)]
mod tests {
    use super::*;
    use std::panic;

    #[test]
    fn test_poison() {
        let cell = DoubleCheckedCell::new();

        // Poison the cell.
        assert!(panic::catch_unwind(|| {
            cell.get_or_init(|| panic!("oh no!"));
        }).is_err());

        // Now it is poisoned forever.
        assert!(panic::catch_unwind(|| {
            cell.get_or_init(|| true)
        }).is_err());
    }
}
