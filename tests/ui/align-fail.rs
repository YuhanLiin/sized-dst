use sized_dst::*;

#[repr(align(32))]
#[derive(Debug)]
struct Align32(u32);

fn main() {
    SizedDstA8::<dyn std::fmt::Debug, 32>::new(Align32(1));
}
