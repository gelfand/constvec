#![allow(incomplete_features)]
#![no_std]
#![feature(
    const_ptr_write,
    const_option,
    const_trait_impl,
    const_heap,
    const_ptr_read,
    const_intrinsic_copy,
    const_intrinsic_forget,
    const_maybe_uninit_as_mut_ptr,
    const_mut_refs,
    core_intrinsics,
    inline_const,
    intrinsics
)]

use core::{
    intrinsics::{const_allocate, copy_nonoverlapping, forget},
    marker::PhantomData,
    mem::{self, align_of, MaybeUninit},
    ops::Add,
    ptr,
    ptr::NonNull,
};

pub struct Vec<T> {
    ptr: NonNull<T>,
    len: usize,
    _marker: PhantomData<T>,
}

const fn check_align<T>() {
    let align = align_of::<T>();
    assert!(
        (align != 0) && ((align & (align - 1)) == 0),
        "Alignment is not a power of 2"
    );
}

impl<T> Vec<T> {
    pub const fn with_capacity(cap: usize) -> Self {
        check_align::<T>();
        let ptr = unsafe { Self::alloc(cap) };
        Vec {
            ptr,
            len: 0,
            _marker: PhantomData,
        }
    }

    pub const fn push(&mut self, elem: T) {
        unsafe {
            ptr::write(self.ptr.as_ptr().add(self.len), elem);
        }
        self.len += 1;
    }

    pub const fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            let mut tmp = MaybeUninit::<T>::uninit();
            unsafe {
                copy_nonoverlapping(self.ptr.as_ptr().add(self.len), tmp.as_mut_ptr(), 1);
                Some(tmp.assume_init())
            }
        }
    }

    pub const fn insert(&mut self, index: usize, elem: T) {
        unsafe {
            ptr::copy(
                self.ptr.as_ptr().add(index),
                self.ptr.as_ptr().add(index + 1),
                self.len - index,
            );
            ptr::write(self.ptr.as_ptr().add(index), elem);
            self.len += 1;
        }
    }
    pub const fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len, "index out of bounds");
        unsafe {
            self.len -= 1;
            let result = ptr::read(self.ptr.as_ptr().add(index));
            ptr::copy(
                self.ptr.as_ptr().add(index + 1),
                self.ptr.as_ptr().add(index),
                self.len - index,
            );
            result
        }
    }

    /// # Safety
    ///
    /// - Must be called from a const context.
    /// - T must be aligned to a power of 2.
    const unsafe fn alloc(cap: usize) -> NonNull<T> {
        NonNull::new_unchecked(const_allocate(mem::size_of::<T>() * cap, align_of::<T>()) as *mut T)
    }

    pub const fn len(&self) -> usize {
        self.len
    }
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub const fn for_each<F: ~const FnMut(T)>(&self, mut f: F) {
        let mut i = 0;
        while i < self.len {
            f(unsafe { ptr::read(self.ptr.as_ptr().add(i)) });
            i += 1;
        }
        forget(f);
    }

    pub const fn for_each_mut<F: ~const FnMut(&mut T)>(&mut self, mut f: F) {
        let mut i = 0;
        while i < self.len {
            f(unsafe { &mut *self.ptr.as_ptr().add(i) });
            i += 1;
        }
        forget(f);
    }

    pub const fn fold<F: ~const FnMut(T, T) -> T>(&self, mut f: F, init: T) -> T {
        let mut result = init;
        let mut i = 0;
        while i < self.len {
            result = f(unsafe { ptr::read(self.ptr.as_ptr().add(i)) }, result);
            i += 1;
        }
        forget(f);
        result
    }
}

unsafe impl<T: Send> Send for Vec<T> {}
unsafe impl<T: Sync> Sync for Vec<T> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn const_closure() {
        const {
            let mut v = Vec::with_capacity(10);
            v.push(10);
            v.push(10);
            v.push(10);

            const fn assert_eq_10(x: u64) {
                assert!(x == 10);
            }
            // This works.
            v.for_each(assert_eq_10);
        }
    }
    #[test]
    fn it_works() {
        const {
            // doesn't work in non const context.
            let mut v = Vec::<u64>::with_capacity(255);
            assert!(v.is_empty());

            v.push(10);
            assert!(v.len() == 1);
            assert!(!v.is_empty());
            let elem = v.pop().unwrap();
            assert!(elem == 10);
            assert!(v.is_empty());
            assert!(v.pop().is_none());

            v.insert(0, 64);
            assert!(v.len() == 1);
            assert!(!v.is_empty());
            assert!(v.pop().unwrap() == 64);
            v.insert(0, 64);
            let val = v.remove(0);
            assert!(val == 64);

            v.push(10);
            v.push(10);
            v.push(10);
            v.push(10);
            v.push(10);
            v.push(10);
            v.push(10);
            v.push(10);
            v.push(10);
            v.push(10);
            v.push(10);
            v.push(10);
            v.push(10);
            v.push(10);
        }
    }
    #[test]
    fn test_zerosize() {
        const {
            let mut v = Vec::<()>::with_capacity(1);
            v.push(());
            assert!(v.len() == 1);
            assert!(!v.is_empty());
            assert!(v.pop().is_some());
        }
    }

    #[test]
    fn test_iter() {
        const {
            let mut v = Vec::<u64>::with_capacity(255);
            let mut i = 0;
            while i < 255 {
                v.push(10);
                i += 1;
            }

            const fn f(x: u64) {
                assert!(x == 10);
            }
            v.for_each(f);

            const fn f2(x: &mut u64) {
                *x = 20;
            }
            v.for_each_mut(f2);

            const fn f3(x: u64) {
                assert!(x == 20);
            }
            v.for_each(f3);
        }
    }

    #[test]
    fn test_fold() {
        const {
            let mut v = Vec::<u64>::with_capacity(255);
            let mut i = 0;
            while i < 255 {
                v.push(10);
                i += 1;
            }

            const fn fold_inner(acc: u64, x: u64) -> u64 {
                acc + x
            }
            let val = v.fold(fold_inner, 0);
            assert!(val == 2550);
        }
    }
}
