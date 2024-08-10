use sized_dst::*;

fn main() {
    DstA8::<dyn std::fmt::Debug, 4>::new([0u8; 17]);
}
