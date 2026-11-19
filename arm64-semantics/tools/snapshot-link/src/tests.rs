// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unit tests for `snapshot-link` (`[TEST ONLY]`).

use crate::link::{
    musl_inputs, run, rust_encoded_rustflags, sha256, stage_runtime_inputs, tool, tool_from_env,
};
use crate::{Cli, stock, verify};
use clap::Parser;
use object::{Architecture, BinaryFormat, Endianness, Object, SectionKind};
use rust_obj2lean::untrusted_driver;
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;

fn engine_repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf()
}

fn find_test_objcopy() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("LLVM_OBJCOPY").filter(|v| !v.is_empty()) {
        let pb = PathBuf::from(p);
        if pb.is_file() || which::which(&pb).is_ok() {
            return Some(pb);
        }
    }
    if let Ok(pb) = which::which("llvm-objcopy") {
        return Some(pb);
    }
    if let Ok(out) = std::process::Command::new("rustc")
        .args(["--print", "target-libdir"])
        .output()
        && out.status.success()
    {
        let libdir = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
        if let Some(parent) = libdir.parent() {
            let candidate = parent.join("bin").join("llvm-objcopy");
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    for name in [
        "llvm-objcopy-22",
        "llvm-objcopy-21",
        "llvm-objcopy-20",
        "llvm-objcopy-19",
        "llvm-objcopy-18",
    ] {
        if let Ok(pb) = which::which(name) {
            return Some(pb);
        }
    }
    None
}

pub(crate) fn find_test_lld() -> Option<PathBuf> {
    if let Ok(pb) = tool("LLD", "ld.lld") {
        return Some(pb);
    }
    if let Ok(out) = std::process::Command::new("rustc")
        .args(["--print", "target-libdir"])
        .output()
        && out.status.success()
    {
        let libdir = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
        if let Some(parent) = libdir.parent() {
            for rel in ["bin/gcc-ld/ld.lld", "bin/ld.lld"] {
                let candidate = parent.join(rel);
                if candidate.is_file() {
                    return Some(candidate);
                }
            }
        }
    }
    None
}

fn synthetic_aarch64_obj_with_debug_str() -> Vec<u8> {
    let mut obj =
        object::write::Object::new(BinaryFormat::Elf, Architecture::Aarch64, Endianness::Little);
    let text = obj.section_id(object::write::StandardSection::Text);
    obj.append_section_data(text, &[0xc0, 0x03, 0x5f, 0xd6], 4); // ret
    obj.add_symbol(object::write::Symbol {
        name: b"__synthetic_runtime_sym".to_vec(),
        value: 0,
        size: 4,
        kind: object::SymbolKind::Text,
        scope: object::SymbolScope::Linkage,
        weak: false,
        section: object::write::SymbolSection::Section(text),
        flags: object::SymbolFlags::None,
    });
    let dbg_str = obj.add_section(Vec::new(), b".debug_str".to_vec(), SectionKind::Debug);
    obj.append_section_data(dbg_str, b"/host/specific/comp/dir\0crt1.c\0", 1);
    obj.write().expect("must emit valid AArch64 ELF object")
}

#[test]
fn stage_runtime_inputs_rejects_duplicate_file_names() {
    let Some(objcopy) = find_test_objcopy() else {
        eprintln!("skipping duplicate-name test: LLVM_OBJCOPY / llvm-objcopy unavailable");
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let a = dir.path().join("a").join("crt1.o");
    let b = dir.path().join("b").join("crt1.o");
    let stage = dir.path().join("stage");
    std::fs::create_dir_all(a.parent().unwrap()).unwrap();
    std::fs::create_dir_all(b.parent().unwrap()).unwrap();
    let bytes = synthetic_aarch64_obj_with_debug_str();
    std::fs::write(&a, &bytes).unwrap();
    std::fs::write(&b, &bytes).unwrap();

    let err = stage_runtime_inputs(&objcopy, &[a, b], &stage).unwrap_err();
    assert!(
        err.to_string()
            .contains("duplicate runtime input file name"),
        "{err}"
    );
}

#[test]
fn stage_runtime_inputs_strips_debug_str_and_keeps_file_names() {
    let Some(objcopy) = find_test_objcopy() else {
        eprintln!("skipping stage_runtime_inputs test: LLVM_OBJCOPY / llvm-objcopy unavailable");
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let src_dir = dir.path().join("src");
    let stage_dir = dir.path().join("stage");
    std::fs::create_dir_all(&src_dir).unwrap();

    let crt1_src = src_dir.join("crt1.o");
    let crtn_src = src_dir.join("crtn.o");
    let obj_bytes = synthetic_aarch64_obj_with_debug_str();
    std::fs::write(&crt1_src, &obj_bytes).unwrap();
    std::fs::write(&crtn_src, &obj_bytes).unwrap();

    let parsed_before = object::File::parse(obj_bytes.as_slice()).unwrap();
    assert!(parsed_before.section_by_name(".debug_str").is_some());
    assert!(parsed_before.section_by_name(".text").is_some());

    let staged = stage_runtime_inputs(&objcopy, &[crt1_src, crtn_src], &stage_dir)
        .expect("staging succeeds");
    assert_eq!(
        staged,
        vec![stage_dir.join("crt1.o"), stage_dir.join("crtn.o")]
    );

    let stripped_bytes = std::fs::read(&staged[0]).unwrap();
    let parsed_after = object::File::parse(stripped_bytes.as_slice()).unwrap();
    assert!(
        parsed_after.section_by_name(".debug_str").is_none(),
        "expected .debug_str to be stripped"
    );
    assert!(
        parsed_after.section_by_name(".text").is_some(),
        "expected .text to remain intact"
    );

    let dup_err = stage_runtime_inputs(
        &objcopy,
        &[dir.path().join("other").join("crt1.o")],
        &stage_dir,
    )
    .unwrap_err();
    assert!(
        dup_err
            .to_string()
            .contains("duplicate runtime input file name"),
        "{dup_err}"
    );

    // Build two GNU archives whose member paths have distinct directory prefixes (covering both
    // `<= 15`-byte and `> 15`-byte basenames plus `/` symbol-index offset rebasing) and verify
    // `stage_runtime_inputs` produces valid, byte-identical `.a` files.
    let make_gnu_archive = |members: &[(&str, &[u8])]| -> Vec<u8> {
        let mut strtab = Vec::new();
        let mut hdr_names = Vec::new();
        for (name, _) in members {
            if name.len() <= 15 && !name.contains('/') {
                let mut f = [b' '; 16];
                f[..name.len()].copy_from_slice(name.as_bytes());
                f[name.len()] = b'/';
                hdr_names.push(f);
            } else {
                let off = strtab.len();
                strtab.extend_from_slice(name.as_bytes());
                strtab.extend_from_slice(b"/\n");
                let mut f = [b' '; 16];
                f.copy_from_slice(format!("/{off:<15}").as_bytes());
                hdr_names.push(f);
            }
        }
        let mut sym_names = Vec::new();
        for _ in members {
            sym_names.extend_from_slice(b"__synthetic_runtime_sym\0");
        }
        let sym_size = 4 + 4 * members.len() + sym_names.len();
        let sym_sec_len = 60 + sym_size + (sym_size % 2);
        let str_sec_len = if strtab.is_empty() {
            0
        } else {
            60 + strtab.len() + (strtab.len() % 2)
        };
        let mut member_pos = 8 + sym_sec_len + str_sec_len;
        let mut sym_data = Vec::with_capacity(sym_size);
        sym_data.extend_from_slice(&(members.len() as u32).to_be_bytes());
        for (_, payload) in members {
            sym_data.extend_from_slice(&(member_pos as u32).to_be_bytes());
            member_pos += 60 + payload.len() + (payload.len() % 2);
        }
        sym_data.extend_from_slice(&sym_names);

        let mut ar = Vec::from(&b"!<arch>\n"[..]);
        let mut sym_hdr = [b' '; 60];
        sym_hdr[0] = b'/';
        sym_hdr[48..58].copy_from_slice(format!("{:<10}", sym_data.len()).as_bytes());
        sym_hdr[58..60].copy_from_slice(b"`\n");
        ar.extend_from_slice(&sym_hdr);
        ar.extend_from_slice(&sym_data);
        if ar.len() % 2 == 1 {
            ar.push(b'\n');
        }
        if !strtab.is_empty() {
            let mut st_hdr = [b' '; 60];
            st_hdr[..2].copy_from_slice(b"//");
            st_hdr[48..58].copy_from_slice(format!("{:<10}", strtab.len()).as_bytes());
            st_hdr[58..60].copy_from_slice(b"`\n");
            ar.extend_from_slice(&st_hdr);
            ar.extend_from_slice(&strtab);
            if ar.len() % 2 == 1 {
                ar.push(b'\n');
            }
        }
        for ((_, payload), f) in members.iter().zip(hdr_names) {
            let mut m_hdr = [b' '; 60];
            m_hdr[..16].copy_from_slice(&f);
            m_hdr[16..28].copy_from_slice(b"0           ");
            m_hdr[28..34].copy_from_slice(b"0     ");
            m_hdr[34..40].copy_from_slice(b"0     ");
            m_hdr[40..48].copy_from_slice(b"644     ");
            m_hdr[48..58].copy_from_slice(format!("{:<10}", payload.len()).as_bytes());
            m_hdr[58..60].copy_from_slice(b"`\n");
            ar.extend_from_slice(&m_hdr);
            ar.extend_from_slice(payload);
            if ar.len() % 2 == 1 {
                ar.push(b'\n');
            }
        }
        ar
    };

    let ar_a = dir.path().join("cache_a").join("libzigc.a");
    let ar_b = dir.path().join("cache_b").join("libzigc.a");
    std::fs::create_dir_all(ar_a.parent().unwrap()).unwrap();
    std::fs::create_dir_all(ar_b.parent().unwrap()).unwrap();
    std::fs::write(
        &ar_a,
        make_gnu_archive(&[
            ("d/libzigc_zcu.o", &obj_bytes),
            (
                "/home/alice/.cache/zig/o/cafe/compiler_rt_long_member.o",
                &obj_bytes,
            ),
        ]),
    )
    .unwrap();
    std::fs::write(
        &ar_b,
        make_gnu_archive(&[
            (
                "/tmp/very/different/global/zig/cache/o/deadbeef/libzigc_zcu.o",
                &obj_bytes,
            ),
            (
                "/tmp/very/different/global/zig/cache/o/cafe/compiler_rt_long_member.o",
                &obj_bytes,
            ),
        ]),
    )
    .unwrap();

    let stage_a = dir.path().join("stage_ar_a");
    let stage_b = dir.path().join("stage_ar_b");
    let out_a = stage_runtime_inputs(&objcopy, &[ar_a], &stage_a).unwrap();
    let out_b = stage_runtime_inputs(&objcopy, &[ar_b], &stage_b).unwrap();
    assert_eq!(out_a, vec![stage_a.join("libzigc.a")]);
    assert_eq!(out_b, vec![stage_b.join("libzigc.a")]);
    let bytes_a = std::fs::read(&out_a[0]).unwrap();
    let bytes_b = std::fs::read(&out_b[0]).unwrap();
    assert_eq!(
        bytes_a, bytes_b,
        "staged archives from distinct cache dirs must match byte-for-byte"
    );
    assert!(!String::from_utf8_lossy(&bytes_a).contains("alice"));
    let parsed_ar = object::read::archive::ArchiveFile::parse(bytes_a.as_slice()).unwrap();
    let member_names: Vec<String> = parsed_ar
        .members()
        .map(|m| String::from_utf8(m.unwrap().name().to_vec()).unwrap())
        .collect();
    assert_eq!(
        member_names,
        vec!["libzigc_zcu.o", "compiler_rt_long_member.o"]
    );
    let sym_targets: Vec<Vec<u8>> = parsed_ar
        .symbols()
        .unwrap()
        .unwrap()
        .map(|s| {
            let s = s.unwrap();
            let member = parsed_ar.member(s.offset()).unwrap();
            member.data(bytes_a.as_slice()).unwrap().to_vec()
        })
        .collect();
    assert_eq!(sym_targets.len(), 2);
    for mbytes in &sym_targets {
        let mf = object::File::parse(mbytes.as_slice()).unwrap();
        assert!(mf.section_by_name(".debug_str").is_none());
    }
}

#[test]
fn tool_missing_fails_loudly_without_rustup_fallback() {
    // Explicit env override wins even when `PATH` is empty.
    let explicit = tool_from_env(
        "LLVM_OBJCOPY",
        Some(OsStr::new("/custom/bin/llvm-objcopy")),
        "llvm-objcopy",
        Some(OsStr::new("/nonexistent")),
    )
    .unwrap();
    assert_eq!(explicit, PathBuf::from("/custom/bin/llvm-objcopy"));

    // Without `$LLVM_OBJCOPY` and with `/nonexistent` `PATH`, `tool_from_env` must fail loudly
    // even when `rustup` toolchains have `llvm-tools` installed on disk.
    let err = tool_from_env(
        "LLVM_OBJCOPY",
        None,
        "llvm-objcopy",
        Some(OsStr::new("/nonexistent")),
    )
    .expect_err("missing tool must fail rather than falling back to rustup toolchains");
    let msg = format!("{err:#}");
    assert!(msg.contains("llvm-objcopy"), "missing tool name: {msg}");
    assert!(msg.contains("$LLVM_OBJCOPY"), "missing env var hint: {msg}");
    assert!(
        msg.contains("rustup component add llvm-tools"),
        "missing llvm-tools installation hint: {msg}"
    );
    assert!(
        msg.contains("rustc --print target-libdir"),
        "missing target-libdir bin path hint: {msg}"
    );
}

#[test]
fn musl_inputs_splits_link_line() {
    let v = "info\n/z/ld.lld -o libc.so /c/x.o /c/y.a\n/z/ld.lld -o probe /c/crt1.o /c/crti.o /w/main.o --start-group /c/libc.a \
             /c/libcompiler_rt.a --end-group /c/crtn.o\n";
    let (pre, libs, post) = musl_inputs(v, Path::new("/w/main.o")).unwrap();
    assert_eq!(
        pre,
        [PathBuf::from("/c/crt1.o"), PathBuf::from("/c/crti.o")]
    );
    assert_eq!(libs.len(), 2);
    assert_eq!(post, [PathBuf::from("/c/crtn.o")]);
    assert!(musl_inputs(v, Path::new("/x/main.o")).is_err());
}

#[test]
fn rust_encoded_rustflags_pins_static_model_and_path_remaps() {
    let flags = rust_encoded_rustflags(
        Path::new("/host/repo"),
        Path::new("/tmp/work"),
        Some(Path::new("/home/u/.cargo")),
        Some(Path::new("/home/u/.rustup")),
        Some((
            Path::new("/home/u/.rustup/toolchains/stable-x86_64-unknown-linux-gnu"),
            "0123456789abcdef",
        )),
    );
    let parts: Vec<&str> = flags.split('\x1f').collect();
    assert!(
        parts
            .windows(2)
            .any(|w| w == ["-C", "relocation-model=static"])
    );
    assert!(parts.windows(2).any(|w| w == ["-C", "strip=debuginfo"]));
    assert!(parts.windows(2).any(|w| w == ["-C", "no-vectorize-loops"]));
    assert!(parts.windows(2).any(|w| w == ["-C", "no-vectorize-slp"]));
    assert!(parts.windows(2).any(|w| w == ["-C", "target-cpu=generic"]));
    assert!(parts.contains(&"--remap-path-prefix=/tmp/work=/work"));
    assert!(parts.contains(&"--remap-path-prefix=/host/repo=/src"));
    assert!(parts.contains(&"--remap-path-prefix=/home/u/.cargo=/cargo"));
    let rustup_pos = parts
        .iter()
        .position(|&p| p == "--remap-path-prefix=/home/u/.rustup=/rustup")
        .unwrap();
    let sysroot_pos = parts
        .iter()
        .position(|&p| {
            p == "--remap-path-prefix=/home/u/.rustup/toolchains/stable-x86_64-unknown-linux-gnu/lib/rustlib/src/rust=/rustc/0123456789abcdef"
        })
        .unwrap();
    assert!(
        rustup_pos < sysroot_pos,
        "nested sysroot rust-src remap must follow rustup_home remap so last match wins"
    );
}

fn std_test_tempdir(prefix: &str) -> tempfile::TempDir {
    if let Some(ctd) = std::env::var_os("CARGO_TARGET_DIR").filter(|v| !v.is_empty()) {
        let base = PathBuf::from(ctd).join("test-scratch");
        std::fs::create_dir_all(&base).unwrap();
        return tempfile::Builder::new()
            .prefix(prefix)
            .tempdir_in(base)
            .unwrap();
    }
    tempfile::Builder::new().prefix(prefix).tempdir().unwrap()
}

fn write_std_bin_fixture(root: &Path, cargo_toml: &str, main_rs: &str) -> PathBuf {
    let crate_dir = root.join("my_app");
    std::fs::create_dir_all(crate_dir.join("src")).unwrap();
    let manifest = crate_dir.join("Cargo.toml");
    std::fs::write(&manifest, cargo_toml).unwrap();
    std::fs::write(crate_dir.join("src").join("main.rs"), main_rs).unwrap();
    manifest
}

const VALID_STD_CARGO_TOML: &str = r#"[package]
name = "my-app"
version = "0.1.0"
edition = "2024"

[profile.release]
opt-level = 2
codegen-units = 1
lto = "fat"
"#;

const VALID_STD_MAIN_RS: &str = "#![forbid(unsafe_code)]\nfn main() {\n    println!(\"ok\");\n}\n";

#[test]
fn check_std_toolchain_flag_succeeds_without_config_or_out_dir() {
    <Cli as clap::CommandFactory>::command().debug_assert();
    let cli = Cli::parse_from(["snapshot-link", "--check-std-toolchain"]);
    assert!(cli.check_std_toolchain);
    assert!(cli.config.is_empty());
    let msg = crate::std_profile::check_std_toolchain()
        .expect("pinned Rust 1.98.1 std toolchain check must succeed");
    assert_eq!(
        msg,
        "OK: rustc 1.98.1 (48a229cea, LLVM 22.1.8), bundled musl crt1.o + libc.a checksums verified"
    );
    run(cli).expect("`snapshot-link --check-std-toolchain` must succeed");

    let missing_out = Cli::parse_from(["snapshot-link", "--config", "a.toml"]);
    let err = run(missing_out).unwrap_err().to_string();
    assert!(err.contains("--out-dir"), "unexpected error: {err}");

    let d_out = std_test_tempdir("snap_missing_stock_");
    let missing_stock = Cli::parse_from([
        "snapshot-link",
        "--config",
        "a.toml",
        "--out-dir",
        d_out.path().to_str().unwrap(),
    ]);
    let err = run(missing_stock).unwrap_err().to_string();
    assert!(err.contains("--stock"), "unexpected error: {err}");
}

#[test]
fn std_manifest_and_source_guards_reject_invalid_crates() {
    use crate::std_profile::{RustMainKind, classify_rust_manifest};

    // 1. Staticlib crate is classified as `Staticlib` without std binary guards.
    let d_stat = std_test_tempdir("snap_stat_");
    std::fs::create_dir_all(d_stat.path().join("src")).unwrap();
    let stat_toml = d_stat.path().join("Cargo.toml");
    std::fs::write(
        &stat_toml,
        "[package]\nname = \"my-driver\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[lib]\ncrate-type = [\"staticlib\"]\n",
    )
    .unwrap();
    std::fs::write(d_stat.path().join("src/lib.rs"), "#![no_std]\n").unwrap();
    assert!(matches!(
        classify_rust_manifest(&stat_toml, d_stat.path()).unwrap(),
        RustMainKind::Staticlib
    ));

    // 2. Valid `std` crate (with `lto = true`, comments mentioning `#![no_std]`, and a `vendor/`
    //    directory containing `.c` files) succeeds.
    let d_ok = std_test_tempdir("snap_ok_");
    let ok_manifest = write_std_bin_fixture(
        d_ok.path(),
        "[package]\nname = \"my-app\"\nversion = \"0.1.0\"\nedition = \"2024\"\n[profile.release]\nopt-level = 2\ncodegen-units = 1\nlto = true\n",
        "// #![no_std] in comment is fine\n#![forbid(unsafe_code)]\nfn main() { let _ = \"#![no_std]\"; }\n",
    );
    let vendor_sub = d_ok.path().join("my_app/vendor/widget");
    std::fs::create_dir_all(&vendor_sub).unwrap();
    std::fs::write(vendor_sub.join("helper.c"), "int x;\n").unwrap();
    match classify_rust_manifest(&ok_manifest, d_ok.path()).unwrap() {
        RustMainKind::StdBin(info) => assert_eq!(info.bin_stem, "my_app"),
        RustMainKind::Staticlib => panic!("expected StdBin"),
    }

    // 3. Reject `[patch]` table.
    let d_patch = std_test_tempdir("snap_patch_");
    let m_patch = write_std_bin_fixture(
        d_patch.path(),
        &format!(
            "{VALID_STD_CARGO_TOML}\n[patch.crates-io]\nwidget = {{ path = \"../widget\" }}\n"
        ),
        VALID_STD_MAIN_RS,
    );
    let err = classify_rust_manifest(&m_patch, d_patch.path()).unwrap_err();
    assert!(err.to_string().contains("[patch]"), "{err}");

    // 4. Reject `.cargo/config.toml` in ancestor up to `repo_root`.
    let d_cfg = std_test_tempdir("snap_cargocfg_");
    let m_cfg = write_std_bin_fixture(d_cfg.path(), VALID_STD_CARGO_TOML, VALID_STD_MAIN_RS);
    std::fs::create_dir_all(d_cfg.path().join(".cargo")).unwrap();
    std::fs::write(d_cfg.path().join(".cargo/config.toml"), "[build]\n").unwrap();
    let err = classify_rust_manifest(&m_cfg, d_cfg.path()).unwrap_err();
    assert!(err.to_string().contains(".cargo/config.toml"), "{err}");
}

#[test]
fn std_source_and_profile_guards_reject_invalid_cases() {
    use crate::std_profile::classify_rust_manifest;

    // 1. Reject `build.rs` and `.c` / `.s` files outside `vendor/`.
    let d_build = std_test_tempdir("snap_buildrs_");
    let m_build = write_std_bin_fixture(d_build.path(), VALID_STD_CARGO_TOML, VALID_STD_MAIN_RS);
    std::fs::write(d_build.path().join("my_app/build.rs"), "fn main() {}\n").unwrap();
    let err = classify_rust_manifest(&m_build, d_build.path()).unwrap_err();
    assert!(err.to_string().contains("build.rs"), "{err}");

    let d_c = std_test_tempdir("snap_cfile_");
    let m_c = write_std_bin_fixture(d_c.path(), VALID_STD_CARGO_TOML, VALID_STD_MAIN_RS);
    std::fs::write(
        d_c.path().join("my_app/src/shim.c"),
        "int f(void) { return 0; }\n",
    )
    .unwrap();
    let err = classify_rust_manifest(&m_c, d_c.path()).unwrap_err();
    assert!(err.to_string().contains("shim.c"), "{err}");

    // 2. Reject `#![no_std]` and missing / commented-out `#![forbid(unsafe_code)]`.
    for (main_src, expected) in [
        (
            "#![no_std]\n#![forbid(unsafe_code)]\nfn main() {}\n",
            "#![no_std]",
        ),
        ("fn main() {}\n", "#![forbid(unsafe_code)]"),
        (
            "// #![forbid(unsafe_code)]\nfn main() {}\n",
            "#![forbid(unsafe_code)]",
        ),
        (
            "fn main() { let _ = \"#![forbid(unsafe_code)]\"; }\n",
            "#![forbid(unsafe_code)]",
        ),
    ] {
        let d = std_test_tempdir("snap_attr_");
        let m = write_std_bin_fixture(d.path(), VALID_STD_CARGO_TOML, main_src);
        let err = classify_rust_manifest(&m, d.path()).unwrap_err();
        assert!(err.to_string().contains(expected), "{err}");
    }

    // 3. Reject wrong `[profile.release]` settings (`opt-level`, `codegen-units`, `lto`).
    for (bad_profile, expected) in [
        ("", "[profile.release]"),
        (
            "[profile.release]\nopt-level = 3\ncodegen-units = 1\nlto = \"fat\"\n",
            "opt-level = 2",
        ),
        (
            "[profile.release]\nopt-level = 2\ncodegen-units = 4\nlto = \"fat\"\n",
            "codegen-units = 1",
        ),
        (
            "[profile.release]\nopt-level = 2\ncodegen-units = 1\nlto = \"thin\"\n",
            "lto = \"fat\"",
        ),
        (
            "[profile.release]\nopt-level = 2\ncodegen-units = 1\nlto = false\n",
            "lto = \"fat\"",
        ),
    ] {
        let d = std_test_tempdir("snap_prof_");
        let toml = format!(
            "[package]\nname = \"my-app\"\nversion = \"0.1.0\"\nedition = \"2024\"\n{bad_profile}"
        );
        let m = write_std_bin_fixture(d.path(), &toml, VALID_STD_MAIN_RS);
        let err = classify_rust_manifest(&m, d.path()).unwrap_err();
        assert!(err.to_string().contains(expected), "{err}");
    }

    // 4. Non-std invocation with 0 `--config` still requires `--config` (with `--stock`) or `--main-rust`.
    let d_out = std_test_tempdir("snap_noconfig_");
    let cli = Cli::parse_from(["snapshot-link", "--out-dir", d_out.path().to_str().unwrap()]);
    let err = run(cli).unwrap_err();
    assert!(err.to_string().contains("at least one --config"), "{err}");
}

#[test]
fn stock_cli_flag_links_config_and_stages_inputs_with_custom_lld_arg() {
    let parsed = Cli::parse_from([
        "snapshot-link",
        "--stock",
        "--stock-keep-library",
        "--repo-root",
        "/repo",
        "--config",
        "translation.toml",
        "--main-c",
        "main.c",
        "--out-dir",
        "/out",
        "--name",
        "stage-probe.elf",
        "--stock-lld-arg=--unresolved-symbols=ignore-all",
    ]);
    assert!(parsed.stock);
    assert!(parsed.stock_keep_library);
    assert_eq!(parsed.config, vec![PathBuf::from("translation.toml")]);
    assert_eq!(parsed.main_c, Some(PathBuf::from("main.c")));
    assert_eq!(parsed.name, "stage-probe.elf");
    assert_eq!(
        parsed.stock_lld_arg,
        vec!["--unresolved-symbols=ignore-all".to_string()]
    );

    if untrusted_driver::resolve_zig("0.16.0").is_err()
        || find_test_objcopy().is_none()
        || find_test_lld().is_none()
    {
        eprintln!("skipping end-to-end --stock link test: zig/llvm-objcopy/ld.lld unavailable");
        return;
    }

    let dir_a = std_test_tempdir("snap_stock_a_");
    let dir_b = std_test_tempdir("snap_stock_bravo_longer_path_");

    let build_one = |root: &Path| -> (PathBuf, Vec<u8>, String, String) {
        std::fs::write(
            root.join("lib.c"),
            "static const int BIAS = 7;\nint add_bias(int x) { return x + BIAS; }\nint unused_fn(int x) { return x * 3; }\n",
        )
        .unwrap();
        std::fs::write(
            root.join("main.c"),
            "extern int add_bias(int x);\nint main(void) { return add_bias(35) - 42; }\n",
        )
        .unwrap();
        std::fs::write(
            root.join("translation.toml"),
            "obj_name = \"widgetLib\"\ntitle = \"Widget lib\"\n[native_compiler]\nzig_version = \"0.16.0\"\n[[native_objects]]\nname = \"lib\"\nsource = \"lib.c\"\nc_flags = [\"-O2\", \"-fno-builtin\"]\n[[targets]]\nname = \"widget\"\nlean_file = \"Out.lean\"\nsub_namespace = \"Widget\"\nprog_name = \"widgetBin\"\ntitle = \"Widget\"\nlemma_allowlist = [\"add_bias\"]\n",
        )
        .unwrap();

        let out_dir = root.join("stage_raw");
        let cli = Cli::parse_from([
            "snapshot-link",
            "--stock",
            "--repo-root",
            root.to_str().unwrap(),
            "--config",
            "translation.toml",
            "--main-c",
            "main.c",
            "--out-dir",
            out_dir.to_str().unwrap(),
            "--name",
            "stage-probe.elf",
            "--stock-lld-arg=--unresolved-symbols=ignore-all",
        ]);
        // Ensure LLVM_OBJCOPY / LLD are available via env if not directly on PATH.
        let objcopy_ok = tool("LLVM_OBJCOPY", "llvm-objcopy").is_ok();
        let lld_ok = tool("LLD", "ld.lld").is_ok();
        assert!(
            objcopy_ok && lld_ok,
            "expected llvm-objcopy and ld.lld on PATH or via $LLVM_OBJCOPY / $LLD"
        );
        stock::run(&cli).expect("snapshot-link --stock must succeed");

        assert!(out_dir.join("work/lib0_0.o").is_file());
        assert!(out_dir.join("work/main.o").is_file());
        assert!(out_dir.join("work/runtime/crt1.o").is_file());
        assert!(out_dir.join("work/runtime/libc.a").is_file());

        let elf_path = out_dir.join("stage-probe.elf");
        let elf_bytes = std::fs::read(&elf_path).unwrap();
        let stock_json = std::fs::read_to_string(out_dir.join("stock-link.json")).unwrap();
        let census_json = std::fs::read_to_string(out_dir.join("census.json")).unwrap();
        (elf_path, elf_bytes, stock_json, census_json)
    };

    if tool("LLVM_OBJCOPY", "llvm-objcopy").is_err() || tool("LLD", "ld.lld").is_err() {
        eprintln!("skipping end-to-end --stock link test: llvm-objcopy or ld.lld not on PATH");
        return;
    }

    let (elf_path_a, elf_a, stock_a, census_a) = build_one(dir_a.path());
    let (_elf_path_b, elf_b, stock_b, census_b) = build_one(dir_b.path());

    assert_eq!(
        elf_a, elf_b,
        "stock ELF must be reproducible across tempdirs"
    );
    assert_eq!(
        stock_a, stock_b,
        "stock-link.json must be reproducible across tempdirs"
    );
    assert_eq!(
        census_a, census_b,
        "census.json must be reproducible across tempdirs"
    );

    verify::check_std_elf(&elf_a).expect("stock ELF must pass check_std_elf");

    let stock_val: serde_json::Value = serde_json::from_str(&stock_a).unwrap();
    assert_eq!(stock_val["tool"], "snapshot-link --stock");
    assert_eq!(stock_val["parserCheck"], "ok");
    assert!(
        stock_val["lld"]["args"]
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v.as_str() == Some("--unresolved-symbols=ignore-all"))
    );

    let census_val: serde_json::Value = serde_json::from_str(&census_a).unwrap();
    assert!(
        census_val["images"][0]
            .get("trustedLinkerTextLayout")
            .is_none(),
        "census.json must not carry trustedLinkerTextLayout"
    );
    assert_eq!(
        census_val["images"][0]["unmatchedSamples"],
        serde_json::json!([])
    );

    let fetch_qemu = engine_repo_root().join("scripts/fetch-qemu-aarch64");
    let qemu_out = Command::new(&fetch_qemu)
        .current_dir(engine_repo_root())
        .output()
        .expect("scripts/fetch-qemu-aarch64 must run");
    assert!(qemu_out.status.success());
    let qemu_bin = PathBuf::from(String::from_utf8_lossy(&qemu_out.stdout).trim());
    let run_out = Command::new(&qemu_bin)
        .arg(&elf_path_a)
        .output()
        .expect("qemu-aarch64 execution of stock ELF must succeed");
    assert_eq!(run_out.status.code(), Some(0));
}

#[test]
fn std_binary_reproducible_across_tempdirs_passes_checks_and_runs_in_qemu() {
    let std_lockfile = "# This file is automatically @generated by Cargo.\nversion = 4\n\n[[package]]\nname = \"my-app\"\nversion = \"0.1.0\"\n";

    let dir_a = std_test_tempdir("snap_std_a_");
    let dir_b = std_test_tempdir("snap_std_bravo_longer_path_");

    let build_one = |root: &Path| -> (PathBuf, Vec<u8>, String) {
        let manifest = write_std_bin_fixture(root, VALID_STD_CARGO_TOML, VALID_STD_MAIN_RS);
        std::fs::write(manifest.parent().unwrap().join("Cargo.lock"), std_lockfile).unwrap();
        let out_dir = root.join("out");
        let cli = Cli::parse_from([
            "snapshot-link",
            "--repo-root",
            root.to_str().unwrap(),
            "--main-rust",
            "my_app/Cargo.toml",
            "--out-dir",
            out_dir.to_str().unwrap(),
            "--name",
            "my_app.elf",
        ]);
        run(cli).expect("snapshot-link on std binary crate must succeed");
        let elf_path = out_dir.join("my_app.elf");
        let elf_bytes = std::fs::read(&elf_path).unwrap();
        let link_json = std::fs::read_to_string(out_dir.join("link.json")).unwrap();
        (elf_path, elf_bytes, link_json)
    };

    let (elf_path_a, elf_a, json_a) = build_one(dir_a.path());
    let (_elf_path_b, elf_b, json_b) = build_one(dir_b.path());

    assert_eq!(
        sha256(&elf_a),
        sha256(&elf_b),
        "std ELF binaries built in distinct directories must be byte-for-byte identical"
    );
    assert_eq!(elf_a, elf_b);
    assert_eq!(
        json_a, json_b,
        "link.json manifests built in distinct directories must be byte-for-byte identical"
    );

    verify::check_std_elf(&elf_a).expect("check_std_elf must accept linked std binary");

    let parsed_json: serde_json::Value = serde_json::from_str(&json_a).unwrap();
    assert_eq!(parsed_json["config"], serde_json::Value::Null);
    assert_eq!(parsed_json["base"], serde_json::json!(0x40_0000));
    assert_eq!(parsed_json["image"], serde_json::Value::Null);
    assert_eq!(parsed_json["stubs"], serde_json::json!([]));
    assert_eq!(parsed_json["stdProfile"]["rustc"], "1.98.1");
    assert_eq!(
        parsed_json["stdProfile"]["commit"],
        "48a229ceaefd4985c50990b14116b6d856af0985"
    );
    assert_eq!(parsed_json["stdProfile"]["llvm"], "22.1.8");
    assert!(parsed_json["tools"]["rust-lld"].as_str().is_some());

    // Negative checks on mutated copies of the linked ELF (`ET_DYN`, `PT_DYNAMIC`, W+X, symbol audit).
    let mut bad_dyn = elf_a.clone();
    bad_dyn[16..18].copy_from_slice(&3u16.to_le_bytes()); // ET_DYN
    assert!(
        verify::check_std_elf(&bad_dyn)
            .unwrap_err()
            .to_string()
            .contains("ET_EXEC")
    );

    let e_phoff = u64::from_le_bytes(elf_a[32..40].try_into().unwrap()) as usize;
    let mut bad_wx = elf_a.clone();
    let ph1 = e_phoff + 2 * 56; // `.text` PT_LOAD
    bad_wx[ph1 + 4..ph1 + 8].copy_from_slice(&7u32.to_le_bytes()); // PF_R | PF_W | PF_X
    assert!(
        verify::check_std_elf(&bad_wx)
            .unwrap_err()
            .to_string()
            .contains("W^X")
    );

    let mut bad_pt_dyn = elf_a.clone();
    bad_pt_dyn[e_phoff..e_phoff + 4].copy_from_slice(&object::elf::PT_DYNAMIC.to_le_bytes());
    assert!(
        verify::check_std_elf(&bad_pt_dyn)
            .unwrap_err()
            .to_string()
            .contains("PT_DYNAMIC")
    );

    let mut bad_sym = elf_a.clone();
    let needle = b"__do_init\0";
    let pos = bad_sym
        .windows(needle.len())
        .position(|w| w == needle)
        .expect("symbol in strtab");
    bad_sym[pos..pos + needle.len()].copy_from_slice(b"gimli_bad\0");
    assert!(
        verify::check_std_elf(&bad_sym)
            .unwrap_err()
            .to_string()
            .contains("gimli_bad")
    );

    // Execute under `qemu-aarch64` and verify exact stdout + exit status.
    let fetch_qemu = engine_repo_root().join("scripts/fetch-qemu-aarch64");
    let qemu_out = Command::new(&fetch_qemu)
        .current_dir(engine_repo_root())
        .output()
        .expect("scripts/fetch-qemu-aarch64 must run");
    assert!(
        qemu_out.status.success(),
        "fetch-qemu-aarch64 failed: {}",
        String::from_utf8_lossy(&qemu_out.stderr)
    );
    let qemu_bin = PathBuf::from(String::from_utf8_lossy(&qemu_out.stdout).trim());
    let run_out = Command::new(&qemu_bin)
        .arg(&elf_path_a)
        .output()
        .expect("qemu-aarch64 execution must succeed");
    assert_eq!(run_out.status.code(), Some(0));
    assert_eq!(String::from_utf8_lossy(&run_out.stdout), "ok\n");
}
