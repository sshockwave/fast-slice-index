//! Fast slice indexing through ghost token scopes.
//!
//! This crate provides a sound way to eliminate bounds checking by using
//! ghost tokens with higher-rank trait bounds (HRTB) to ensure indices
//! remain valid within a scope.
//!
//! # Example
//!
//! ```
//! use fast_slice_index::*;
//!
//! let vec = vec![1, 2, 3, 4, 5];
//! with_slice(&vec, |slice, len| {
//!     if let Some(idx) = LessThan::check(&len, 2) {
//!         let value = slice[idx];
//!         assert_eq!(value, 3);
//!     }
//! });
//! ```

mod anchor;

pub use anchor::Anchor;

use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

/// A slice with a branded lifetime 'id
#[derive(Copy, Clone)]
pub struct Slice<'id, T> {
    ptr: *const T,
    _marker: PhantomData<(&'id (), *const T)>,
}

/// A mutable slice with a branded lifetime 'id
pub struct SliceMut<'id, T> {
    ptr: *mut T,
    _marker: PhantomData<(&'id (), *mut T)>,
}

/// An append-only view of a Vec with a branded lifetime 'id
pub struct VecAppend<'id, T> {
    vec: *mut Vec<T>,
    _marker: PhantomData<&'id ()>,
}

/// A proof that an index is less than (or no more than) a length
/// INCLUSIVE = false: index < length (LessThan)
/// INCLUSIVE = true: index <= length (NoMoreThan)
#[derive(Copy, Clone)]
pub struct Bound<'id, const INCLUSIVE: bool, I = usize> {
    index: I,
    _marker: PhantomData<(&'id (), I)>,
}

/// A proof that an index is less than a length
pub type LessThan<'id, I = usize> = Bound<'id, false, I>;

/// A proof that an index is no more than a length (i.e., index <= length)
pub type NoMoreThan<'id, I = usize> = Bound<'id, true, I>;

/// A range proof: left < right, with left proven less than some bound
#[derive(Copy, Clone)]
pub struct Range<'id, I = usize> {
    left: LessThan<'id, I>,
    right: Anchor<'id, I>,
}

/// A proof that a value is greater than N
#[derive(Copy, Clone)]
pub struct GreaterThan<const N: usize> {
    value: usize,
    _marker: PhantomData<()>,
}

/// A proof that a value is greater than one
pub type GreaterThanOne = GreaterThan<1>;

impl<'id, I> Range<'id, I>
where
    I: PartialOrd + Copy,
{
    /// Create a range by checking that left < right
    #[inline]
    pub fn new(left: LessThan<'id, I>, right: Anchor<'id, I>) -> Option<Self> {
        if left.get() < right.get() {
            Some(Range { left, right })
        } else {
            None
        }
    }

    /// Get the left bound (proven less than some outer bound)
    #[inline]
    pub fn left(&self) -> LessThan<'id, I> {
        self.left
    }

    /// Get the right bound
    #[inline]
    pub fn right(&self) -> Anchor<'id, I> {
        self.right
    }

    /// Get the length of the range (right - left)
    #[inline]
    pub fn len(&self) -> I
    where
        I: std::ops::Sub<Output = I>,
    {
        self.right.get() - self.left.get()
    }
}

impl<'id, const INCLUSIVE: bool, I> Bound<'id, INCLUSIVE, I>
where
    I: PartialOrd + Copy,
{
    /// Check if an index satisfies the bound against a Anchor
    #[inline]
    pub fn check(num: &Anchor<'id, I>, index: I) -> Option<Self> {
        let valid = if INCLUSIVE {
            index <= num.get()
        } else {
            index < num.get()
        };

        if valid {
            Some(Bound {
                index,
                _marker: PhantomData,
            })
        } else {
            None
        }
    }

    /// Get the raw index value
    #[inline]
    pub fn get(&self) -> I {
        self.index
    }
}

impl<'id, T> Slice<'id, T> {
    /// Create a new slice from a raw pointer
    fn new(ptr: *const T) -> Self {
        Self {
            ptr,
            _marker: PhantomData,
        }
    }
}

impl<'id, T> SliceMut<'id, T> {
    /// Create a new mutable slice from a raw pointer
    fn new(ptr: *mut T) -> Self {
        Self {
            ptr,
            _marker: PhantomData,
        }
    }
}

impl<'id, T> VecAppend<'id, T> {
    /// Create a new append-only vec view
    fn new(vec: &mut Vec<T>) -> Self {
        Self {
            vec: vec as *mut Vec<T>,
            _marker: PhantomData,
        }
    }

    /// Push an element to the vec
    #[inline]
    pub fn push(&mut self, value: T) {
        // Safe: we have exclusive access to the vec through &mut self
        unsafe { (*self.vec).push(value) }
    }

    /// Get the current length
    #[inline]
    pub fn len(&self) -> usize {
        // Safe: we have access to the vec
        unsafe { (*self.vec).len() }
    }

    /// Check if the vec is empty
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<const N: usize> GreaterThan<N> {
    /// Create a new GreaterThan proof by checking a value
    #[inline]
    pub fn new(value: usize) -> Option<Self> {
        if value > N {
            Some(GreaterThan {
                value,
                _marker: PhantomData,
            })
        } else {
            None
        }
    }

    /// Create a new GreaterThan proof, panicking if the value is not > N
    #[inline]
    pub const fn new_const<const V: usize>() -> Self {
        const { assert!(V > N) };
        GreaterThan {
            value: V,
            _marker: PhantomData,
        }
    }

    /// Get the value
    #[inline]
    pub fn get(&self) -> usize {
        self.value
    }
}

impl<'id, T, U> PartialOrd<U> for LessThan<'id, T>
where
    T: PartialOrd<U>,
{
    fn partial_cmp(&self, other: &U) -> Option<std::cmp::Ordering> {
        self.index.partial_cmp(other)
    }
}

impl<'id, T, U> PartialEq<U> for LessThan<'id, T>
where
    T: PartialEq<U>,
{
    fn eq(&self, other: &U) -> bool {
        self.index.eq(other)
    }
}

impl<'id> LessThan<'id, usize> {
    /// Floor division: dividend / divisor
    /// When divisor > 1, the result is strictly less than the dividend
    #[inline]
    pub fn floor_div_gt_one(&self, divisor: GreaterThanOne) -> LessThan<'id, usize> {
        // Since divisor > 1 and self.index < len, we have:
        // self.index / divisor < self.index < len
        Bound {
            index: self.index / divisor.value,
            _marker: PhantomData,
        }
    }

    /// Add two indices
    #[inline]
    pub fn add(&self, other: usize) -> Option<usize> {
        self.index.checked_add(other)
    }

    /// Multiply by a constant
    #[inline]
    pub fn mul(&self, factor: usize) -> Option<usize> {
        self.index.checked_mul(factor)
    }
}

impl<'id> NoMoreThan<'id, usize> {
}

impl<'id> From<LessThan<'id, usize>> for NoMoreThan<'id, usize> {
    #[inline]
    fn from(less: LessThan<'id, usize>) -> Self {
        Bound {
            index: less.index,
            _marker: PhantomData,
        }
    }
}

impl<'id, T> Index<LessThan<'id, usize>> for Slice<'id, T> {
    type Output = T;

    #[inline]
    fn index(&self, index: LessThan<'id, usize>) -> &T {
        // Safe: LessThan proves the index is within bounds
        unsafe { &*self.ptr.add(index.index) }
    }
}

impl<'id, T> Index<LessThan<'id, usize>> for SliceMut<'id, T> {
    type Output = T;

    #[inline]
    fn index(&self, index: LessThan<'id, usize>) -> &T {
        // Safe: LessThan proves the index is within bounds
        unsafe { &*self.ptr.add(index.index) }
    }
}

impl<'id, T> IndexMut<LessThan<'id, usize>> for SliceMut<'id, T> {
    #[inline]
    fn index_mut(&mut self, index: LessThan<'id, usize>) -> &mut T {
        // Safe: LessThan proves the index is within bounds
        unsafe { &mut *self.ptr.add(index.index) }
    }
}

/// Execute a function with a slice and its length token
///
/// The closure receives a branded slice and length that are
/// guaranteed to be consistent within the scope.
#[inline]
pub fn with_slice<T, R>(slice: &[T], f: impl for<'id> FnOnce(Slice<'id, T>, Anchor<'id, usize>) -> R) -> R {
    Anchor::scope(slice.len(), |num| {
        let slice_ref = Slice::new(slice.as_ptr());
        f(slice_ref, num)
    })
}

/// Execute a function with a mutable slice and its length token
///
/// The closure receives a branded mutable slice and length that are
/// guaranteed to be consistent within the scope.
#[inline]
pub fn with_slice_mut<T, R>(slice: &mut [T], f: impl for<'id> FnOnce(&mut SliceMut<'id, T>, Anchor<'id, usize>) -> R) -> R {
    Anchor::scope(slice.len(), |num| {
        let mut slice_mut = SliceMut::new(slice.as_mut_ptr());
        f(&mut slice_mut, num)
    })
}

/// Execute a function with an append-only vec and its initial length token
///
/// The closure receives an append-only view of the vec and an anchor
/// representing the vec's length at the start of the scope.
/// The anchor remains valid even as elements are pushed to the vec.
#[inline]
pub fn with_vec<T, R>(vec: &mut Vec<T>, f: impl for<'id> FnOnce(VecAppend<'id, T>, Anchor<'id, usize>) -> R) -> R {
    Anchor::scope(vec.len(), |anchor| {
        let vec_append = VecAppend::new(vec);
        f(vec_append, anchor)
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_indexing() {
        let vec = vec![1, 2, 3, 4, 5];
        with_slice(&vec, |slice, len| {
            assert_eq!(len.get(), 5);

            if let Some(idx) = LessThan::check(&len, 2) {
                assert_eq!(slice[idx], 3);
            }
        });
    }

    #[test]
    fn test_bounds_checking() {
        let vec = vec![1, 2, 3];
        with_slice(&vec, |_slice, len| {
            assert!(LessThan::check(&len, 0).is_some());
            assert!(LessThan::check(&len, 2).is_some());
            assert!(LessThan::check(&len, 3).is_none());
            assert!(LessThan::check(&len, 10).is_none());
        });
    }

    #[test]
    fn test_loop_indexing() {
        let vec = vec![1, 2, 3, 4, 5];
        with_slice(&vec, |slice, len| {
            let mut sum = 0;
            for i in 0..len.get() {
                if let Some(idx) = LessThan::check(&len, i) {
                    sum += slice[idx];
                }
            }
            assert_eq!(sum, 15);
        });
    }

    #[test]
    fn test_empty_slice() {
        let vec: Vec<i32> = vec![];
        with_slice(&vec, |_slice, len| {
            assert_eq!(len.get(), 0);
            assert!(LessThan::check(&len, 0).is_none());
        });
    }

    #[test]
    fn test_floor_div_gt_one() {
        let vec = vec![0; 10];
        with_slice(&vec, |_slice, len| {
            if let Some(idx) = LessThan::check(&len, 8) {
                // 8 / 2 = 4, which is < 10
                let divisor = GreaterThan::<1>::new_const::<2>();
                let result = idx.floor_div_gt_one(divisor);
                assert_eq!(result.get(), 4);

                // 8 / 3 = 2, which is < 10
                let divisor = GreaterThan::<1>::new_const::<3>();
                let result = idx.floor_div_gt_one(divisor);
                assert_eq!(result.get(), 2);
            }
        });
    }

    #[test]
    fn test_add_mul() {
        let vec = vec![0; 10];
        with_slice(&vec, |_slice, len| {
            if let Some(idx) = LessThan::check(&len, 3) {
                // 3 + 2 = 5
                let sum = idx.add(2).unwrap();
                assert_eq!(sum, 5);
                // Can check against a bound if needed
                assert!(LessThan::check(&len, sum).is_some());

                // 3 * 2 = 6
                let product = idx.mul(2).unwrap();
                assert_eq!(product, 6);
                assert!(LessThan::check(&len, product).is_some());

                // 3 * 4 = 12 >= 10
                let overflow = idx.mul(4).unwrap();
                assert!(LessThan::check(&len, overflow).is_none());
            }
        });
    }

    #[test]
    fn test_from_conversion() {
        let vec = vec![0; 10];
        with_slice(&vec, |_slice, len| {
            if let Some(idx) = LessThan::check(&len, 8) {
                // LessThan can convert to NoMoreThan
                let _no_more: NoMoreThan<usize> = idx.into();
            }
        });
    }

    #[test]
    fn test_slice_mut() {
        let mut vec = vec![1, 2, 3, 4, 5];
        with_slice_mut(&mut vec, |slice, len| {
            // Modify elements
            for i in 0..len.get() {
                if let Some(idx) = LessThan::check(&len, i) {
                    slice[idx] *= 2;
                }
            }
        });
        assert_eq!(vec, vec![2, 4, 6, 8, 10]);
    }

    #[test]
    fn test_vec_append() {
        let mut vec = vec![1, 2, 3];
        with_vec(&mut vec, |mut vec_append, anchor| {
            // Initial length is 3
            assert_eq!(anchor.get(), 3);

            // Push more elements
            vec_append.push(4);
            vec_append.push(5);

            // Length has grown
            assert_eq!(vec_append.len(), 5);

            // But anchor still represents the original length
            assert_eq!(anchor.get(), 3);
        });
        assert_eq!(vec, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_range() {
        let vec = vec![0; 10];
        with_slice(&vec, |_slice, len| {
            if let Some(left) = LessThan::check(&len, 3) {
                // Create an anchor for the right bound
                Anchor::scope(7, |right| {
                    if let Some(range) = Range::new(left, right) {
                        assert_eq!(range.left().get(), 3);
                        assert_eq!(range.right().get(), 7);
                        assert_eq!(range.len(), 4);
                    }
                });
            }
        });
    }
}
