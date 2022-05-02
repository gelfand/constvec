#![allow(incomplete_features)]
#![no_std]
#![feature(
    test,
    const_ptr_write,
    const_option,
    const_trait_impl,
    const_black_box,
    const_heap,
    optimize_attribute,
    const_ptr_read,
    unchecked_math,
    const_intrinsic_copy,
    negative_impls,
    const_inherent_unchecked_arith,
    const_intrinsic_forget,
    const_maybe_uninit_as_mut_ptr,
    const_mut_refs,
    core_intrinsics,
    inline_const,
    intrinsics,
    rustc_attrs
)]

#[cfg(feature = "std")]
extern crate std;

use core::{
    intrinsics::{const_allocate, const_deallocate, copy_nonoverlapping, forget, needs_drop},
    marker::PhantomData,
    mem::{self, align_of, MaybeUninit},
    ptr,
    ptr::NonNull,
};
extern crate alloc;

pub struct Vec<T> {
    ptr: NonNull<T>,
    len: usize,
    cap: usize,
    _marker: PhantomData<T>,
}

const fn assert_safety_requirements<T>() {
    assert!(
        !needs_drop::<T>(),
        "Drop of T is not possible in const context"
    );

    let alignment = align_of::<T>();
    assert!(
        (alignment != 0) && ((alignment & (alignment - 1)) == 0),
        "Alignment is not a power of 2"
    );
}

impl<T> Vec<T> {
    #[inline(always)]
    pub const fn with_capacity(cap: usize) -> Self {
        assert_safety_requirements::<T>();
        let ptr = Self::allocate(cap);

        Vec {
            ptr,
            cap,
            len: 0,
            _marker: PhantomData,
        }
    }

    #[inline(always)]
    pub const fn push(&mut self, elem: T) {
        assert!(self.len < self.cap);
        unsafe { self.push_unchecked(elem) }
    }

    /// # Safety
    ///
    /// - `self.len` must be less than `self.cap`
    #[inline(always)]
    pub const unsafe fn push_unchecked(&mut self, elem: T) {
        ptr::write(self.ptr.as_ptr().add(self.len), elem);
        self.len = self.len.unchecked_add(1);
    }

    #[inline(always)]
    pub const fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            Some(unsafe { self.pop_unchecked() })
        }
    }

    /// # Safety
    /// - `self.len` must be greater than 0
    #[inline(always)]
    pub const unsafe fn pop_unchecked(&mut self) -> T {
        self.len = self.len.unchecked_sub(1);
        let mut tmp = MaybeUninit::<T>::uninit();
        copy_nonoverlapping(self.ptr.as_ptr().add(self.len), tmp.as_mut_ptr(), 1);
        tmp.assume_init()
    }

    #[inline(always)]
    pub const fn insert(&mut self, index: usize, elem: T) {
        assert!(index <= self.len);
        unsafe { self.insert_unchecked(index, elem) }
    }

    /// # Safety
    /// - `index` must be less than `self.cap`
    #[inline(always)]
    pub const unsafe fn insert_unchecked(&mut self, index: usize, elem: T) {
        ptr::copy(
            self.ptr.as_ptr().add(index),
            self.ptr.as_ptr().add(index.unchecked_add(1)),
            self.len - index,
        );
        ptr::write(self.ptr.as_ptr().add(index), elem);
        self.len = self.len.unchecked_add(1);
    }

    #[inline(always)]
    pub const fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len, "index out of bounds");
        unsafe { self.remove_unchecked(index) }
    }

    /// # Safety
    ///
    /// - `index` must be less than `self.len()`
    ///
    #[inline(always)]
    pub const unsafe fn remove_unchecked(&mut self, index: usize) -> T {
        self.len = self.len.unchecked_sub(1);
        let result = ptr::read(self.ptr.as_ptr().add(index));
        ptr::copy(
            self.ptr.as_ptr().add(index.unchecked_add(1)),
            self.ptr.as_ptr().add(index),
            self.len.unchecked_sub(index),
        );
        result
    }

    #[inline(always)]
    const fn allocate(cap: usize) -> NonNull<T> {
        unsafe {
            NonNull::new_unchecked(
                const_allocate(mem::size_of::<T>() * cap, align_of::<T>()) as *mut T
            )
        }
    }
    #[inline(always)]
    pub const fn deallocate(self) {
        unsafe {
            const_deallocate(
                self.ptr.as_ptr() as *mut u8,
                mem::size_of::<T>() * self.cap,
                align_of::<T>(),
            )
        };
    }

    #[inline(always)]
    pub const fn len(&self) -> usize {
        self.len
    }
    #[inline(always)]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub const fn map<U, F>(self, mut f: F) -> Vec<U>
    where
        F: ~const FnMut(T) -> U,
    {
        assert!(!needs_drop::<F>());

        let mut result = Vec::with_capacity(self.len);
        let mut i = 0;
        unsafe {
            while i < self.len {
                result.push(f(ptr::read(self.ptr.as_ptr().add(i))));
                i = i.unchecked_add(1);
            }
        }
        forget(f);
        result
    }

    pub const fn filter<F>(self, mut f: F) -> Vec<T>
    where
        F: ~const FnMut(T) -> bool,
    {
        assert!(!needs_drop::<F>());

        let mut result = Vec::with_capacity(self.len);
        let mut i = 0;
        unsafe {
            while i < self.len {
                if f(ptr::read(self.ptr.as_ptr().add(i))) {
                    result.push(ptr::read(self.ptr.as_ptr().add(i)));
                }
                i = i.unchecked_add(1);
            }
        }
        forget(f);
        result
    }

    pub const fn find<F>(&self, mut f: F) -> Option<T>
    where
        F: ~const FnMut(T) -> bool,
    {
        assert!(!needs_drop::<F>());

        let mut i = 0;
        unsafe {
            while i < self.len {
                if f(ptr::read(self.ptr.as_ptr().add(i))) {
                    forget(f);
                    return Some(ptr::read(self.ptr.as_ptr().add(i)));
                }
                i = i.unchecked_add(1);
            }
        }
        forget(f);
        None
    }

    pub const fn zip<U, F>(self, other: Vec<U>, mut f: F) -> Vec<T>
    where
        F: ~const FnMut(T, U) -> T,
    {
        assert!(!needs_drop::<F>());

        let cap = if self.len < other.len {
            self.len
        } else {
            other.len
        };

        let mut result = Vec::with_capacity(cap);
        let mut i = 0;
        unsafe {
            while i < self.len && i < other.len {
                result.push(f(
                    ptr::read(self.ptr.as_ptr().add(i)),
                    ptr::read(other.ptr.as_ptr().add(i)),
                ));
                i = i.unchecked_add(1);
            }
        }
        forget(f);
        result
    }

    #[inline(always)]
    pub const fn for_each<F: ~const FnMut(T)>(&self, mut f: F) {
        assert!(!needs_drop::<F>());

        let mut i = 0;
        unsafe {
            while i < self.len {
                f(ptr::read(self.ptr.as_ptr().add(i)));
                i = i.unchecked_add(1);
            }
        }
        forget(f);
    }

    #[inline(always)]
    pub const fn for_each_mut<F: ~const FnMut(&mut T)>(&mut self, mut f: F) {
        assert!(!needs_drop::<F>());

        let mut i = 0;
        unsafe {
            while i < self.len {
                f(&mut *self.ptr.as_ptr().add(i));
                i = i.unchecked_add(1);
            }
        }
        forget(f);
    }

    #[inline(always)]
    pub const fn fold<F: ~const FnMut(T, T) -> T>(&self, mut f: F, init: T) -> T {
        assert!(!needs_drop::<F>());

        let mut result = init;
        let mut i = 0;
        unsafe {
            while i < self.len {
                result = f(ptr::read(self.ptr.as_ptr().add(i)), result);
                i = i.unchecked_add(1);
            }
        }
        forget(f);
        result
    }
}

unsafe impl<T: Send> Send for Vec<T> {}
unsafe impl<T: Sync> Sync for Vec<T> {}

impl<T> const Drop for Vec<T> {
    fn drop(&mut self) {
        unsafe {
            const_deallocate(
                self.ptr.as_ptr() as *mut u8,
                mem::size_of::<T>() * self.cap,
                align_of::<T>(),
            )
        };
    }
}

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

            const fn f(x: u64) {
                assert!(x == 10);
            }
            v.for_each(f);
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
    fn test_map() {
        const {
            let mut v = Vec::<u64>::with_capacity(255);
            let mut i = 0;
            while i < 255 {
                v.push(10);
                i += 1;
            }

            const fn f(x: u64) -> u64 {
                x + 1
            }
            let mut v2 = v.map(f);
            assert!(v2.len() == 255);
            assert!(v2.pop().unwrap() == 11);
        }
    }

    #[test]
    fn test_filter() {
        const {
            let mut v = Vec::<u64>::with_capacity(255);
            let mut i = 0;
            while i < 255 {
                v.push(10);
                i += 1;
            }

            const fn f(x: u64) -> bool {
                x == 10
            }
            let mut v2 = v.filter(f);
            assert!(v2.len() == 255);
            assert!(v2.pop().unwrap() == 10);
        }
    }

    #[test]
    fn test_zip() {
        const {
            let mut v = Vec::<u64>::with_capacity(255);
            let mut i = 0;
            while i < 255 {
                v.push(10);
                i += 1;
            }

            const fn f(x: u64, y: u64) -> u64 {
                x + y
            }
            let v2 = Vec::<u64>::with_capacity(255);
            while i < 255 {
                v.push(100);
                i += 1;
            }
            let mut v2 = v.zip(v2, f);

            while i < 255 {
                let val = v2.pop().unwrap();
                assert!(val == 110);
                i += 1;
            }

            const fn find_inner_val(x: u64) -> bool {
                x == 10
            }

            v2.find(find_inner_val);
        }
    }

    #[inline(always)]
    #[allow(dead_code)]
    const fn sum_const(iter: usize) {
        let mut v = Vec::<usize>::with_capacity(iter);
        let mut i = 0;
        while i < iter {
            v.push(i);
            i += 1;
        }

        #[inline(always)]
        const fn fold_inner(acc: usize, x: usize) -> usize {
            acc + x
        }
        let _ = v.fold(fold_inner, 0);
    }

    #[inline(always)]
    #[allow(dead_code)]
    fn sum_non_const(iter: usize) {
        let mut v = alloc::vec::Vec::with_capacity(iter);
        for i in 0..iter {
            v.push(i);
        }

        let val: usize = v.into_iter().sum();
        let _ = val;
    }

    #[cfg_attr(feature = "std", test)]
    fn bench() {
        extern crate alloc;
        extern crate std;

        use core::intrinsics::black_box;
        use std::println;

        const MUL: usize = 128;

        macro_rules! bench_suite {
            ($iter:expr, $const_fn:expr, $non_const_fn:expr) => {
                let now = std::time::Instant::now();
                const { $const_fn($iter * MUL) };
                let const_took = now.elapsed().as_nanos();
                println!("const: {:?} ns, iterations: {}", const_took, $iter * MUL);

                let now = std::time::Instant::now();
                $non_const_fn($iter * MUL);
                let non_const_took = now.elapsed().as_nanos();
                println!(
                    "non-const: {:?} ns, iterations: {}\n",
                    non_const_took,
                    $iter * MUL
                );
            };
        }

        macro_rules! bench {
            ($name:expr, $const_fn:expr, $non_const_fn:expr) => {
                println!("Benchmarking: {}\n", $name);

                bench_suite!(1, $const_fn, $non_const_fn);
                bench_suite!(2, $const_fn, $non_const_fn);
                bench_suite!(4, $const_fn, $non_const_fn);
                bench_suite!(8, $const_fn, $non_const_fn);
                bench_suite!(16, $const_fn, $non_const_fn);
                bench_suite!(32, $const_fn, $non_const_fn);
                bench_suite!(64, $const_fn, $non_const_fn);
                bench_suite!(128, $const_fn, $non_const_fn);
                println!("");
            };
        }

        bench!(
            "sum with black box",
            black_box(sum_const),
            black_box(sum_non_const)
        );
        bench!("sum without blackbox", sum_const, sum_non_const);
    }
}
