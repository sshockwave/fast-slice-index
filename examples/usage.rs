use fast_slice_index::*;

fn main() {
    println!("=== Basic Usage ===\n");

    // Example 1: Basic safe indexing
    let vec = vec![10, 20, 30, 40, 50];

    with_slice(&vec, |slice, len| {
        println!("Vector: {:?}", vec);
        println!("Length: {}", len.get());

        if let Some(idx) = LessThan::check(&len, 2) {
            println!("Element at index 2: {}", slice[idx]);
        }
    });

    // Example 2: Loop with checked bounds
    println!("\n=== Loop Example ===\n");
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    with_slice(&data, |slice, len| {
        println!("Accessing every other element:");
        for i in (0..len.get()).step_by(2) {
            if let Some(idx) = LessThan::check(&len, i) {
                print!("{} ", slice[idx]);
            }
        }
        println!();
    });

    // Example 3: Bounds checking
    println!("\n=== Bounds Checking ===\n");
    let vec = vec![1, 2, 3];

    with_slice(&vec, |_slice, len| {
        match LessThan::check(&len, 5) {
            Some(_) => println!("Index 5 is valid"),
            None => println!("Index 5 is out of bounds (length is {})", len.get()),
        }
    });

    // Example 4: Empty slice
    println!("\n=== Empty Slice ===\n");
    let empty: Vec<i32> = vec![];

    with_slice(&empty, |_slice, len| {
        println!("Empty slice length: {}", len.get());
    });

    // Example 5: Sum all elements
    println!("\n=== Sum Example ===\n");
    let numbers = vec![1, 2, 3, 4, 5];

    let sum = with_slice(&numbers, |slice, len| {
        let mut total = 0;
        for i in 0..len.get() {
            if let Some(idx) = LessThan::check(&len, i) {
                total += slice[idx];
            }
        }
        total
    });

    println!("Sum of {:?} = {}", numbers, sum);

    println!("\n=== Complete ===");
}
