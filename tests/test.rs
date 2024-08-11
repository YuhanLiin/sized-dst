#[test]
#[cfg_attr(miri, ignore)]
fn ui() {
    let t = trybuild::TestCases::new();
    // Need this passing case to make sure `cargo build` is used for the other tests, so that const
    // evaluation is triggered and the other tests actually fail compilation
    t.pass("tests/ui/empty-pass.rs");

    t.compile_fail("tests/ui/align-fail.rs");
    t.compile_fail("tests/ui/size-fail.rs");
    t.compile_fail("tests/ui/borrowchk-fail.rs");
    t.compile_fail("tests/ui/custom-dst-fail.rs");
}
