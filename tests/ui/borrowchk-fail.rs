use sized_dst::*;

fn main() {
    {
        let n = 32;
        SizedDstNative::<dyn std::fmt::Debug, 16>::new(&n)
    };
}