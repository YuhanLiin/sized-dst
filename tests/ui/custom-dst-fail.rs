use sized_dst::*;

struct CustomDyn<T: ?Sized> {
    label: u32,
    data: T,
}

fn main() {
    let val = CustomDyn {
        label: 1,
        data: 12u32,
    };
    // Can fit the data field, but not the whole struct
    DstA4::<CustomDyn<dyn ToString>, 4>::new(val);
}
