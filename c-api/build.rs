use std::{env, path::PathBuf};

use cbindgen::Language;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");

    let manifest_dir = env::var("CARGO_MANIFEST_DIR").unwrap();
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());

    let config = cbindgen::Config {
        enumeration: cbindgen::EnumConfig {
            prefix_with_name: true,
            ..Default::default()
        },
        ..Default::default()
    };

    cbindgen::Builder::new()
        .with_config(config)
        .with_crate(manifest_dir)
        .with_language(Language::C)
        .with_parse_deps(true)
        .with_parse_include(&["steamid"])
        .generate()
        .expect("failed to generate C bindings")
        .write_to_file(out_dir.join("steamid.h"));

    let target_dir = out_dir
        .parent()
        .unwrap_or(out_dir.as_path())
        .parent()
        .unwrap_or(out_dir.as_path())
        .parent()
        .unwrap_or(out_dir.as_path());

    println!(
        "cargo:rustc-env=INLINE_C_RS_CFLAGS=-I{I} -L{L} -D_DEBUG -D_CRT_SECURE_NO_WARNINGS",
        I = out_dir.display(),
        L = target_dir.display(),
    );

    println!(
        "cargo:rustc-env=INLINE_C_RS_LDFLAGS={shared_object_dir}/libsteamid.so",
        shared_object_dir = target_dir.display(),
    );
}
