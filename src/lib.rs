#![allow(incomplete_features)]
#![no_std]
#![feature(
    const_ptr_write,
    const_option,
    const_trait_impl,
    core_intrinsics,
    const_heap,
    const_ptr_read,
    const_intrinsic_copy,
    const_maybe_uninit_as_mut_ptr,
    const_mut_refs,
    inline_const,
    intrinsics
)]

use core::{
    intrinsics::{const_allocate, const_deallocate, copy_nonoverlapping},
    marker::PhantomData,
    mem::{self, align_of, size_of, MaybeUninit},
    ptr,
    ptr::NonNull,
};

pub struct Vec<T> {
    ptr: NonNull<T>,
    cap: usize,
    len: usize,
    _marker: PhantomData<T>,
}

const fn check_align<T>() {
    let align = align_of::<T>();
    debug_assert!(
        (align != 0) && ((align & (align - 1)) == 0),
        "Alignment is not a power of 2"
    );
}

impl<T> Vec<T> {
    pub const fn new() -> Self {
        assert!(size_of::<T>() != 0, "zero-sized type");
        Vec {
            ptr: NonNull::dangling(),
            cap: 0,
            len: 0,
            _marker: PhantomData,
        }
    }

    pub const fn push(&mut self, elem: T) {
        if self.len == self.cap {
            self.grow();
        }
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
        assert!(index <= self.len, "index out of bounds");
        if self.cap == self.len {
            self.grow();
        }

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

    const fn grow(&mut self) {
        let new_cap = if self.cap == 0 {
            mem::size_of::<T>()
        } else {
            self.cap * 2
        };
        let new_ptr = if self.cap == 0 {
            check_align::<T>();
            unsafe { const_allocate(new_cap, align_of::<T>()) }
        } else {
            let ptr = self.ptr.as_ptr();
            let align = align_of::<T>();
            unsafe {
                const_deallocate(ptr as *mut u8, self.cap, align);
                const_allocate(new_cap, align)
            }
        };

        self.ptr = unsafe { NonNull::new_unchecked(new_ptr as *mut T) };
        self.cap = new_cap;
    }

    pub const fn len(&self) -> usize {
        self.len
    }
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
}

unsafe impl<T: Send> Send for Vec<T> {}
unsafe impl<T: Sync> Sync for Vec<T> {}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        const {
            // doesn't work in non const context.
            let mut v = Vec::<u64>::new();
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
        }
    }
}
