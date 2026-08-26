# fast-slice-index

A sound way to eliminate bounds checking in Rust using ghost tokens and higher-rank trait bounds (HRTB).

## Overview

This crate provides a type-safe method to perform unchecked slice indexing by proving at compile time that indices are within bounds. Unlike lifetime-based approaches, this implementation uses branded types with HRTB to ensure soundness.

## How It Works

The key insight is to use a branded lifetime `'id` that:
1. Cannot be named or created by user code
2. Ties together a `Slice<'id, T>` and `Len<'id>` within a scope
3. Ensures indices proven valid remain valid for that scope

The `LessThan<'id>` type acts as a proof token that an index is less than a particular length, and can only be used with slices bearing the same brand.

## Usage

```rust
use fast_slice_index::*;

// Get a length token and slice from a Vec
let vec = vec![1, 2, 3, 4, 5];
with_slice(&vec, |slice, len| {
    // Check bounds once to get a LessThan proof
    if let Some(idx) = len.check::<false>(2) {
        // Use standard indexing syntax for unchecked access
        let value = slice[idx];
        assert_eq!(value, 3);
    }

    // Out of bounds returns None
    assert!(len.check::<false>(10).is_none());
});
```

## Loop Example

```rust
let vec = vec![1, 2, 3, 4, 5];
with_slice(&vec, |slice, len| {
    // Check bounds once per iteration
    for i in 0..len.get() {
        if let Some(idx) = len.check::<false>(i) {
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
with_slice(&vec, |slice, len| {
    if let Some(idx) = len.check::<false>(8) {
        // Division by a value > 1 produces another LessThan
        // Use new_const() for compile-time known divisors
        let divisor = GreaterThan::<1>::new_const(3);
        let result = idx.floor_div_gt_one(divisor); // Returns LessThan
        let value = slice[result];
    }
});
```

### Checked Arithmetic

```rust
with_slice(&vec, |slice, len| {
    if let Some(idx) = len.check::<false>(5) {
        // Add with overflow checking
        if let Some(sum) = idx.add(3) {
            // Check the result against the bound if needed
            if let Some(new_idx) = len.check::<false>(sum) {
                let value = slice[new_idx]; // 5 + 3 = 8
            }
        }

        // Multiply with overflow checking
        if let Some(product) = idx.mul(2) {
            if let Some(new_idx) = len.check::<false>(product) {
                let value = slice[new_idx]; // 5 * 2 = 10
            }
        }
    }
});
```

### Type Conversions

```rust
with_slice(&vec, |slice, len| {
    if let Some(idx) = len.check::<false>(5) {
        // LessThan can convert to NoMoreThan
        let no_more: NoMoreThan<usize> = idx.into();
    }
});
```

### Proof Types

The crate uses const generics for compile-time guarantees:

- `Bound<'id, false>` (alias `LessThan<'id>`) - proves `index < length`
- `Bound<'id, true>` (alias `NoMoreThan<'id>`) - proves `index <= length`
- `GreaterThan<N>` - proves `value > N`
- `GreaterThanZero` (alias for `GreaterThan<0>`) - proves `value > 0`
- `GreaterThanOne` (alias for `GreaterThan<1>`) - proves `value > 1`

## Why This Is Sound

Previous lifetime-based approaches were unsound because:
- Lifetimes alone don't prevent the underlying data from changing
- A `Len<'a>` could outlive modifications to the vector

This implementation is sound because:
- The branded lifetime `'id` is created fresh for each `with_slice`/`with_vec` call
- It cannot escape the closure due to HRTB (`for<'id>`)
- The `Slice<'id, T>` only stores a raw pointer (no length to get out of sync)
- The `Len<'id>` stores the length and is tied to the slice via the brand
- No operations within the scope can invalidate the length

## Performance

The indexing operation compiles down to a simple pointer offset with no bounds checking, identical to using `get_unchecked`.

## Safety

All unsafe code is encapsulated within the library. User code cannot:
- Create invalid `LessThan` tokens
- Mix tokens from different scopes
- Escape the branded lifetime

## License

MIT OR Apache-2.0
