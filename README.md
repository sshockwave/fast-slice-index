# fast-slice-index

A sound way to eliminate bounds checking in Rust using ghost tokens and higher-rank trait bounds (HRTB).

## Overview

This crate provides a type-safe method to perform unchecked slice indexing by proving at compile time that indices are within bounds. Unlike lifetime-based approaches, this implementation uses branded types with HRTB to ensure soundness.

## How It Works

The key insight is to use a branded lifetime `'id` that:
1. Cannot be named or created by user code
2. Ties together a `Slice<'id, T>` and `Anchor<'id>` within a scope
3. Ensures indices proven valid remain valid for that scope

The `LessThan<'id>` type acts as a proof token that an index is less than a particular length, and can only be used with slices bearing the same brand.

## Usage

### Basic Indexing

```rust
use fast_slice_index::*;

// Get an anchor and slice from a Vec
let vec = vec![1, 2, 3, 4, 5];
with_slice(&vec, |slice, anchor| {
    // Check bounds once to get a LessThan proof
    if let Some(idx) = LessThan::check(&anchor, 2) {
        // Use standard indexing syntax for unchecked access
        let value = slice[idx];
        assert_eq!(value, 3);
    }

    // Out of bounds returns None
    assert!(LessThan::check(&anchor, 10).is_none());
});
```

### Mutable Slices

```rust
let mut vec = vec![1, 2, 3, 4, 5];
with_slice_mut(&mut vec, |slice, anchor| {
    for i in 0..anchor.get() {
        if let Some(idx) = LessThan::check(&anchor, i) {
            slice[idx] *= 2;  // Mutable access
        }
    }
});
```

### Append-Only Vec

```rust
let mut vec = vec![1, 2, 3];
with_vec(&mut vec, |mut vec_append, anchor| {
    // anchor represents the initial length (3)
    assert_eq!(anchor.get(), 3);
    
    // Can only push, not pop or modify existing elements
    vec_append.push(4);
    vec_append.push(5);
    
    // Vec has grown, but anchor is still valid
    assert_eq!(vec_append.len(), 5);
    assert_eq!(anchor.get(), 3);  // Anchor unchanged
});
```

### Range Type

```rust
with_slice(&vec, |slice, anchor| {
    if let Some(left) = LessThan::check(&anchor, 3) {
        Anchor::scope(7, |right| {
            if let Some(range) = Range::new(left, right) {
                // Proven: 3 < 7
                assert_eq!(range.len(), 4);  // 7 - 3
            }
        });
    }
});
```

## Loop Example

```rust
let vec = vec![1, 2, 3, 4, 5];
with_slice(&vec, |slice, anchor| {
    // Check bounds once per iteration
    for i in 0..anchor.get() {
        if let Some(idx) = LessThan::check(&anchor, i) {
            // Unchecked access inside the loop
            let value = slice[idx];
            // ... use value ...
        }
    }
});
```

## Arithmetic Operations

`LessThan` supports various arithmetic operations with compile-time guarantees:

### Floor Division

```rust
with_slice(&vec, |slice, anchor| {
    if let Some(idx) = LessThan::check(&anchor, 8) {
        // Division by a value > 1 produces another LessThan
        // Use new_const() for compile-time known divisors
        let divisor = GreaterThan::<1>::new_const::<3>();
        let result = idx.floor_div_gt_one(divisor); // Returns LessThan
        let value = slice[result];
    }
});
```

### Checked Arithmetic

```rust
with_slice(&vec, |slice, anchor| {
    if let Some(idx) = LessThan::check(&anchor, 5) {
        // Add with overflow checking
        if let Some(sum) = idx.add(3) {
            // Check the result against the bound if needed
            if let Some(new_idx) = LessThan::check(&anchor, sum) {
                let value = slice[new_idx]; // 5 + 3 = 8
            }
        }

        // Multiply with overflow checking
        if let Some(product) = idx.mul(2) {
            if let Some(new_idx) = LessThan::check(&anchor, product) {
                let value = slice[new_idx]; // 5 * 2 = 10
            }
        }
    }
});
```

### Type Conversions

```rust
with_slice(&vec, |slice, anchor| {
    if let Some(idx) = LessThan::check(&anchor, 5) {
        // LessThan can convert to NoMoreThan
        let no_more: NoMoreThan<usize> = idx.into();
    }
});
```

## Proof Types

The crate uses const generics for compile-time guarantees:

- `Bound<'id, false>` (alias `LessThan<'id>`) - proves `index < length`
- `Bound<'id, true>` (alias `NoMoreThan<'id>`) - proves `index <= length`
- `Range<'id>` - proves `left < right` with left bound proven valid
- `GreaterThan<N>` - proves `value > N`
- `GreaterThanOne` (alias for `GreaterThan<1>`) - proves `value > 1`

## API Overview

- `with_slice(&[T], fn)` - immutable slice with anchor
- `with_slice_mut(&mut [T], fn)` - mutable slice with anchor
- `with_vec(&mut Vec<T>, fn)` - append-only vec with initial length anchor
- `Anchor::scope(value, fn)` - create a custom anchor for any numeric value

## Why This Is Sound

Previous lifetime-based approaches were unsound because:
- Lifetimes alone don't prevent the underlying data from changing
- A `Len<'a>` could outlive modifications to the vector

This implementation is sound because:
- The branded lifetime `'id` is created fresh for each `with_slice`/`with_slice_mut`/`with_vec` call
- It cannot escape the closure due to HRTB (`for<'id>`)
- The `Slice<'id, T>` and `SliceMut<'id, T>` only store raw pointers (no length to get out of sync)
- The `Anchor<'id>` stores the length and is tied to the slice via the brand
- No operations within the scope can invalidate the anchor
- `VecAppend` only allows push operations, preserving the validity of indices < initial length

## Performance

The indexing operation compiles down to a simple pointer offset with no bounds checking, identical to using `get_unchecked`.

## Safety

All unsafe code is encapsulated within the library. User code cannot:
- Create invalid `LessThan` tokens
- Mix tokens from different scopes
- Escape the branded lifetime

## License

MIT OR Apache-2.0
