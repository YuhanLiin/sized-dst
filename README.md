# sized-dst

This crate provides `Dst`, an owned container for dynamically-sized types (DSTs) that's backed by *inline* memory. The main use-case is *owned trait objects without heap allocation*. You can think of it as a stack-only version of `Box<dyn Trait>`.

This crate currently requires **nightly**, since it relies on `Unsize` and pointer metadata.

The layout of `sized_dst::Dst` consists of the DST metadata (for trait objects, this is the vtable pointer) and a fixed block of memory storing the actual object. This allows it to live entirely on the stack or even a static variable. The size and alignment of its memory block are specified by generic parameters, so a `sized_dst::Dst` can only store objects that fit in its memory block. If the object does not fulfill the size or alignment requirements, the constructor of `sized_dst::Dst` will emit a **compile-time** error.

```rust
use sized_dst::{Dst, max_size};

trait Draw {
    fn draw(&self);
}

struct Button {
    height: u32,
    width: u32,
    name: &'static str,
}
impl Draw for Button {
    fn draw(&self) { /* draw the button */ }
}

struct Checkbox {
    on: bool,
}
impl Draw for Checkbox {
    fn draw(&self) { /* draw the checkbox */ }
}

struct Text(&'static str);
impl Draw for Text {
    fn draw(&self) { /* draw the text */ }
}

struct Blob([u8; 100]);
impl Draw for Blob {
    fn draw(&self) { /* draw the blob */ }
}

impl Draw for u32 {
    fn draw(&self) { /* draw the u32 */ }
}

fn main() {
    // Each Dst stores a `dyn Draw` up to a fixed capacity, which is set via `max_size` to
    // the size of the biggest trait object we're using.
    let drawables: &[Dst<dyn Draw, { max_size!(Checkbox, Text, Button) }>] = &[
        Dst::new(Checkbox { on: true }),
        Dst::new(Text("lorem ipsum")),
        Dst::new(Button {
            height: 20,
            width: 20,
            name: "PANIC BUTTON",
        }),
        Dst::new(1u32),   // u32 is smaller than the fixed capacity we specified, so we can use it
        // Dst::new(Blob([0; 100]))    This would not compile, because Blob doesn't fit in Dst
    ];

    // Perform dynamic dispatch over the Draw trait
    for d in drawables {
        d.draw();
    }
}
```

Compared to `Box<dyn Trait>`, `Dst` requires no indirection or allocation, making it more cache-friendly and usable in environments with no allocator. In exchange, `Dst` can only store objects up to a fixed size, making it less flexible than `Box<dyn Trait>`. In a way, `Dst` offers a compromise between enums and boxed trait objects.

## Optional Features

- `std`: Enable implementations of `std` traits.
