#[rustversion::nightly]
fn main() {
    println!("cargo:rustc-cfg=is_nightly");
}

#[rustversion::not(nightly)]
fn main() {}
