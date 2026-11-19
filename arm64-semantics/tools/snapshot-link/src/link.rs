// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Runtime staging and pinned Rust `std` executable link recipe (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` — stages deterministic C/musl runtime inputs and links safe
//!   Rust `std` executables (`--main-rust <Cargo.toml>`) into reproducible static AArch64 Linux
//!   `ET_EXEC` binaries. Soundness rests entirely on `Arm64.Process.ElfImage.parse` and the Lean
//!   proofs checked against the SHA-256-pinned ELF bytes.
//! - **Purpose:** Provides:
//!   - [`musl_inputs`], [`stage_runtime_inputs`], [`normalize_gnu_archive_member_names`],
//!     [`filter_gnu_archive_obj_members`], and [`build_rust_main_archive`], shared with
//!     [`crate::stock`] and [`crate::std_profile`];
//!   - [`run`] and [`link_std_bin`], which compile a safe Rust `std` binary crate under the pinned
//!     Rust `1.98.1` `-Zbuild-std=std,panic_abort` profile ([`crate::std_profile`]), link it with
//!     bundled `rust-lld` against the staged musl `self-contained` inputs using
//!     [`linker_script_std`], verify [`crate::verify::check_std_elf`], and write `link.json`.
//!
//! # Key Types & Functions
//! - [`run`], [`link_std_bin`], [`linker_script_std`]: pinned Rust `std` link recipe.
//! - [`musl_inputs`], [`stage_runtime_inputs`], [`normalize_gnu_archive_member_names`],
//!   [`filter_gnu_archive_obj_members`]: deterministic runtime `.o`/`.a` staging.
//! - [`rust_encoded_rustflags`], [`build_rust_main_archive`]: deterministic Rust `staticlib`
//!   driver build helpers for `--stock --main-rust`.
//!
//! # When to Read This File
//! - Read this file for runtime archive normalization or the `--main-rust` `std` link recipe.

use crate::{Cli, verify};
use anyhow::{Context, Result, bail, ensure};
use rust_obj2lean::untrusted_driver;
use sha2::{Digest, Sha256};
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::process::Command;

/// Page alignment required by `ld.lld -z max-page-size=4096`.
pub const PAGE: u64 = 0x1000;

/// Default base virtual address above the 4 KiB ELF header page (`0x3ff000`).
pub const DEFAULT_BASE: u64 = 0x40_0000;

/// Linker script for a pinned Rust `std` static AArch64 executable: places ELF headers at
/// `0x3ff000`, page-separates `text` (`r-x`), zero-filled `ro` (`r--`), and `data` (`rw-`,
/// including TLS and `__init_array_{start,end}` / `__fini_array_{start,end}`), and discards unwind
/// and compiler-note sections.
pub fn linker_script_std() -> String {
    let hdr = DEFAULT_BASE - PAGE;
    format!(
        "PHDRS {{\n  phdr PT_PHDR PHDRS;\n  hdr PT_LOAD FILEHDR PHDRS FLAGS(4);\n  \
         text PT_LOAD FLAGS(5);\n  ro PT_LOAD FLAGS(4);\n  \
         data PT_LOAD FLAGS(6);\n  tls PT_TLS;\n  stack PT_GNU_STACK FLAGS(6);\n}}\n\
         SECTIONS {{\n  . = {hdr:#x} + SIZEOF_HEADERS;\n  \
         . = ALIGN({PAGE:#x});\n  \
         .init : {{ KEEP(*(SORT_NONE(.init))) }} :text\n  \
         .text : {{ *(.text .text.*) }} :text\n  \
         .fini : {{ KEEP(*(SORT_NONE(.fini))) }} :text\n  \
         . = ALIGN({PAGE:#x});\n  \
         .rodata : {{ *(.rodata .rodata.*) }} :ro =0\n  \
         . = ALIGN({PAGE:#x});\n  \
         .tdata : {{ *(.tdata .tdata.*) }} :data :tls\n  \
         .tbss : {{ *(.tbss .tbss.*) }} :data :tls\n  \
         .init_array : {{\n    \
           PROVIDE_HIDDEN(__init_array_start = .);\n    \
           KEEP(*(SORT_BY_INIT_PRIORITY(.init_array.*) SORT_BY_INIT_PRIORITY(.ctors.*)))\n    \
           KEEP(*(.init_array .ctors))\n    \
           PROVIDE_HIDDEN(__init_array_end = .);\n  \
         }} :data\n  \
         .fini_array : {{\n    \
           PROVIDE_HIDDEN(__fini_array_start = .);\n    \
           KEEP(*(SORT_BY_INIT_PRIORITY(.fini_array.*) SORT_BY_INIT_PRIORITY(.dtors.*)))\n    \
           KEEP(*(.fini_array .dtors))\n    \
           PROVIDE_HIDDEN(__fini_array_end = .);\n  \
         }} :data\n  \
         .data : {{ *(.data .data.*) }} :data\n  \
         .bss : {{ *(.bss .bss.* COMMON) }} :data\n  \
         /DISCARD/ : {{ *(.eh_frame*) *(.gcc_except_table*) *(.comment) *(.note*) *(.llvm_addrsig) }}\n}}\n",
    )
}

/// The C runtime inputs `zig cc` passes to `ld.lld` for a static aarch64-linux-musl link of
/// `main_o`, from its `-v` output: `(startup objects before main, archives, objects after)`.
pub fn musl_inputs(
    verbose: &str,
    main_o: &Path,
) -> Result<(Vec<PathBuf>, Vec<PathBuf>, Vec<PathBuf>)> {
    // With a cold zig cache, `-v` also prints the links that build musl's own libraries; the
    // final link is the `ld.lld` line that names `main_o`.
    let main_s = main_o.to_string_lossy();
    let line = verbose
        .lines()
        .filter(|l| l.contains("ld.lld"))
        .find(|l| l.split_whitespace().any(|t| t == main_s))
        .with_context(|| {
            format!(
                "no `zig cc -v` ld.lld link line mentions {}",
                main_o.display()
            )
        })?;
    let (mut pre, mut libs, mut post) = (Vec::new(), Vec::new(), Vec::new());
    let mut seen_main = false;
    for tok in line.split_whitespace() {
        let p = PathBuf::from(tok);
        if p == main_o {
            seen_main = true;
        } else if tok.ends_with(".a") {
            libs.push(p);
        } else if tok.ends_with(".o") {
            if seen_main { &mut post } else { &mut pre }.push(p);
        }
    }
    ensure!(
        seen_main,
        "`zig cc -v` link line does not mention {}",
        main_o.display()
    );
    ensure!(
        pre.iter()
            .any(|p| p.file_name().is_some_and(|n| n == "crt1.o")),
        "no crt1.o in `zig cc -v` link line"
    );
    Ok((pre, libs, post))
}

/// Stage C runtime objects (`.o`) and archives (`.a`) into `stage_dir` with debug info stripped
/// via `objcopy`, keeping bare file names and failing if two staged inputs share a file name.
pub fn stage_runtime_inputs(
    objcopy: &Path,
    paths: &[PathBuf],
    stage_dir: &Path,
) -> Result<Vec<PathBuf>> {
    std::fs::create_dir_all(stage_dir)?;
    let mut seen = HashSet::new();
    let mut staged = Vec::with_capacity(paths.len());
    for src in paths {
        let name = src
            .file_name()
            .with_context(|| format!("runtime input {} has no file name", src.display()))?;
        let dst = stage_dir.join(name);
        ensure!(
            seen.insert(name.to_os_string()) && !dst.exists(),
            "duplicate runtime input file name {:?} while staging {}",
            name,
            src.display()
        );
        let mut c = Command::new(objcopy);
        match src.extension().and_then(|e| e.to_str()) {
            Some("o") => {
                c.arg("--strip-debug");
            }
            Some("a") => {
                c.args(["--enable-deterministic-archives", "--strip-debug"]);
            }
            other => bail!(
                "unsupported runtime input extension {:?} for {}",
                other,
                src.display()
            ),
        };
        run_cmd(c.arg(src).arg(&dst))?;
        if src.extension().and_then(|e| e.to_str()) == Some("a") {
            let normalized = normalize_gnu_archive_member_names(&std::fs::read(&dst)?)?;
            std::fs::write(&dst, normalized)?;
        }
        staged.push(dst);
    }
    Ok(staged)
}

/// Strip directory prefixes from member names in a deterministic GNU `!<arch>\n` archive emitted
/// by `llvm-objcopy --enable-deterministic-archives`: names of `<= 15` bytes are written inline as
/// `<base>/`, longer names go into a canonical `//` string table, and member file offsets in the
/// `/` or `/SYM64/` symbol index are updated to match.
///
/// With a cold cache, `zig` builds `libc.a`, `libzigc.a`, and `libcompiler_rt.a` from object files
/// under `<ZIG_GLOBAL_CACHE_DIR>/o/<hash>/...` and records those full cache paths in the archive
/// `//` string table, which `llvm-objcopy --enable-deterministic-archives --strip-debug` keeps.
pub fn normalize_gnu_archive_member_names(buf: &[u8]) -> Result<Vec<u8>> {
    rewrite_gnu_archive(buf, false)
}

/// Drop non-`.o` payload members (such as `lib.rmeta` and `lib.rmeta-link` inside a `.rlib`) and
/// normalize remaining member names to basenames while rebasing `/` and `/SYM64/` symbol offsets.
pub fn filter_gnu_archive_obj_members(buf: &[u8]) -> Result<Vec<u8>> {
    rewrite_gnu_archive(buf, true)
}

fn rewrite_gnu_archive(buf: &[u8], keep_only_obj: bool) -> Result<Vec<u8>> {
    ensure!(buf.starts_with(b"!<arch>\n"), "not a regular GNU archive");
    let mut pos = 8usize;
    let mut records: Vec<(usize, [u8; 60], Vec<u8>)> = Vec::new();
    while pos < buf.len() {
        if pos % 2 == 1 {
            pos += 1;
        }
        if pos == buf.len() {
            break;
        }
        ensure!(pos + 60 <= buf.len(), "truncated archive header at {pos}");
        let mut hdr = [0u8; 60];
        hdr.copy_from_slice(&buf[pos..pos + 60]);
        let size: usize = std::str::from_utf8(&hdr[48..58])
            .context("non-UTF8 archive member size")?
            .trim()
            .parse()
            .context("invalid archive member size")?;
        ensure!(
            pos + 60 + size <= buf.len(),
            "truncated archive member payload at {pos} (size {size})"
        );
        records.push((pos, hdr, buf[pos + 60..pos + 60 + size].to_vec()));
        pos += 60 + size;
    }

    let old_strtab: Vec<u8> = records
        .iter()
        .find(|(_, hdr, _)| hdr[..16].trim_ascii_end() == b"//")
        .map(|(_, _, data)| data.clone())
        .unwrap_or_default();
    records.retain(|(_, hdr, _)| hdr[..16].trim_ascii_end() != b"//");

    let mut new_strtab: Vec<u8> = Vec::new();
    let mut kept_records: Vec<(usize, [u8; 60], Vec<u8>)> = Vec::with_capacity(records.len());
    for (rec_pos, mut hdr, payload) in records {
        let trimmed = hdr[..16].trim_ascii_end();
        if trimmed == b"/" || trimmed == b"/SYM64/" {
            kept_records.push((rec_pos, hdr, payload));
            continue;
        }
        let raw_name: &[u8] = if hdr[0] == b'/'
            && !trimmed[1..].is_empty()
            && trimmed[1..].iter().all(|b| b.is_ascii_digit())
        {
            let off: usize = std::str::from_utf8(&trimmed[1..])?.parse()?;
            ensure!(
                off < old_strtab.len(),
                "archive string-table offset /{off} out of bounds ({})",
                old_strtab.len()
            );
            let tail = &old_strtab[off..];
            let end = tail.iter().position(|&b| b == b'\n').unwrap_or(tail.len());
            tail[..end].strip_suffix(b"/").unwrap_or(&tail[..end])
        } else {
            trimmed.strip_suffix(b"/").unwrap_or(trimmed)
        };
        let base = raw_name.rsplit(|&b| b == b'/').next().unwrap_or(raw_name);
        if keep_only_obj && !base.ends_with(b".o") {
            continue;
        }
        if base.len() <= 15 {
            let mut field = [b' '; 16];
            field[..base.len()].copy_from_slice(base);
            field[base.len()] = b'/';
            hdr[..16].copy_from_slice(&field);
        } else {
            let new_off = new_strtab.len();
            new_strtab.extend_from_slice(base);
            new_strtab.extend_from_slice(b"/\n");
            let field = format!("/{new_off:<15}");
            hdr[..16].copy_from_slice(field.as_bytes());
        }
        kept_records.push((rec_pos, hdr, payload));
    }
    let mut records = kept_records;

    if !new_strtab.is_empty() {
        let mut st_hdr = [b' '; 60];
        st_hdr[..2].copy_from_slice(b"//");
        st_hdr[48..58].copy_from_slice(format!("{:<10}", new_strtab.len()).as_bytes());
        st_hdr[58..60].copy_from_slice(b"`\n");
        let insert_idx = records
            .iter()
            .position(|(_, hdr, _)| {
                let t = hdr[..16].trim_ascii_end();
                t != b"/" && t != b"/SYM64/"
            })
            .unwrap_or(records.len());
        records.insert(insert_idx, (0, st_hdr, new_strtab));
    }

    let mut old_pos_to_new: HashMap<usize, usize> = HashMap::with_capacity(records.len());
    let mut out_pos = 8usize;
    for (old_pos, _, data) in &records {
        if out_pos % 2 == 1 {
            out_pos += 1;
        }
        if *old_pos > 0 {
            old_pos_to_new.insert(*old_pos, out_pos);
        }
        out_pos += 60 + data.len();
    }

    for (_, hdr, data) in &mut records {
        let tag = hdr[..16].trim_ascii_end();
        if tag == b"/" {
            ensure!(data.len() >= 4, "short archive symbol table");
            let n = u32::from_be_bytes(data[0..4].try_into().unwrap()) as usize;
            ensure!(
                data.len() >= 4usize.saturating_add(n.saturating_mul(4)),
                "truncated archive symbol offsets"
            );
            for k in 0..n {
                let o = 4 + 4 * k;
                let old_m = u32::from_be_bytes(data[o..o + 4].try_into().unwrap()) as usize;
                let &new_m = old_pos_to_new
                    .get(&old_m)
                    .with_context(|| format!("unknown member offset {old_m} in `/`"))?;
                let new_m_u32: u32 = new_m.try_into().context("archive exceeds 4 GiB")?;
                data[o..o + 4].copy_from_slice(&new_m_u32.to_be_bytes());
            }
        } else if tag == b"/SYM64/" {
            ensure!(data.len() >= 8, "short SYM64 archive symbol table");
            let n = u64::from_be_bytes(data[0..8].try_into().unwrap()) as usize;
            ensure!(
                data.len() >= 8usize.saturating_add(n.saturating_mul(8)),
                "truncated SYM64 symbol offsets"
            );
            for k in 0..n {
                let o = 8 + 8 * k;
                let old_m = u64::from_be_bytes(data[o..o + 8].try_into().unwrap()) as usize;
                let &new_m = old_pos_to_new
                    .get(&old_m)
                    .with_context(|| format!("unknown member offset {old_m} in `/SYM64/`"))?;
                data[o..o + 8].copy_from_slice(&(new_m as u64).to_be_bytes());
            }
        }
    }

    let mut out = Vec::with_capacity(out_pos);
    out.extend_from_slice(b"!<arch>\n");
    for (_, hdr, data) in records {
        if out.len() % 2 == 1 {
            out.push(b'\n');
        }
        out.extend_from_slice(&hdr);
        out.extend_from_slice(&data);
    }
    Ok(out)
}

pub fn tool(env: &str, name: &str) -> Result<PathBuf> {
    tool_from_env(
        env,
        std::env::var_os(env).as_deref(),
        name,
        std::env::var_os("PATH").as_deref(),
    )
}

pub fn tool_from_env(
    env: &str,
    env_val: Option<&std::ffi::OsStr>,
    name: &str,
    path_val: Option<&std::ffi::OsStr>,
) -> Result<PathBuf> {
    if let Some(p) = env_val.filter(|v| !v.is_empty()) {
        return Ok(PathBuf::from(p));
    }
    let cwd = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    which::which_in(name, path_val, cwd).with_context(|| {
        format!(
            "`{name}` not found on PATH; set `${env}=/path/to/{name}` or install \
             `rustup component add llvm-tools` and pass \
             `${env}=\"$(dirname \"$(rustc --print target-libdir)\")/bin/{name}\"` \
             (or add that `bin` directory to PATH)"
        )
    })
}

pub(crate) fn run_cmd(c: &mut Command) -> Result<String> {
    let out = c.output().with_context(|| format!("failed to run {c:?}"))?;
    ensure!(
        out.status.success(),
        "{c:?} failed:\n{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    Ok(String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr))
}

pub(crate) fn version(p: &Path, arg: &str) -> Result<String> {
    let s = run_cmd(Command::new(p).arg(arg))?;
    Ok(s.lines().next().unwrap_or("").trim().to_string())
}

pub fn sha256(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

/// Deterministic `CARGO_ENCODED_RUSTFLAGS` for `--stock --main-rust` `staticlib` driver builds:
/// forces a static relocation model, strips debug info, pins `metadata=snapmain`, and remaps work,
/// repo, cargo, rustup, and `rust-src` paths so host paths cannot leak into `.rodata`.
///
/// When `sysroot_and_commit` is provided, `<sysroot>/lib/rustlib/src/rust` (and its canonical path)
/// is remapped to `/rustc/<commit>` after `rustup_home`: when the `rust-src` component is
/// installed, `rustc` rewrites `/rustc/<commit>/library/...` in precompiled `core`/`alloc` metadata
/// to `<sysroot>/lib/rustlib/src/rust/library/...` before applying `--remap-path-prefix`, and
/// `rustc` applies the last matching prefix.
pub fn rust_encoded_rustflags(
    repo_root: &Path,
    work: &Path,
    cargo_home: Option<&Path>,
    rustup_home: Option<&Path>,
    sysroot_and_commit: Option<(&Path, &str)>,
) -> String {
    let mut flags = vec![
        "-C".to_string(),
        "relocation-model=static".to_string(),
        "-C".to_string(),
        "strip=debuginfo".to_string(),
        "-C".to_string(),
        "metadata=snapmain".to_string(),
        format!("--remap-path-prefix={}={}", work.display(), "/work"),
        format!("--remap-path-prefix={}={}", repo_root.display(), "/src"),
    ];
    flags.extend(
        untrusted_driver::config::DETERMINISTIC_CODEGEN_FLAGS
            .iter()
            .map(|s| s.to_string()),
    );
    if let Some(ch) = cargo_home {
        flags.push(format!("--remap-path-prefix={}={}", ch.display(), "/cargo"));
    }
    if let Some(rh) = rustup_home {
        flags.push(format!(
            "--remap-path-prefix={}={}",
            rh.display(),
            "/rustup"
        ));
    }
    if let Some((sysroot, commit)) = sysroot_and_commit {
        let rust_src = sysroot.join("lib").join("rustlib").join("src").join("rust");
        let to = format!("/rustc/{commit}");
        flags.push(format!("--remap-path-prefix={}={to}", rust_src.display()));
        if let Ok(canon) = std::fs::canonicalize(&rust_src)
            && canon != rust_src
        {
            flags.push(format!("--remap-path-prefix={}={to}", canon.display()));
        }
    }
    flags.join("\x1f")
}

pub(crate) fn build_rust_main_archive(
    repo_root: &Path,
    work: &Path,
    objcopy: &Path,
    manifest_rel: &Path,
    rustc_version: &str,
) -> Result<PathBuf> {
    let manifest_path = if manifest_rel.is_absolute() {
        manifest_rel.to_path_buf()
    } else {
        repo_root.join(manifest_rel)
    };
    let manifest_path = std::fs::canonicalize(&manifest_path)
        .with_context(|| format!("missing --main-rust manifest {}", manifest_path.display()))?;
    let cargo = tool("CARGO", "cargo")?;
    let target_dir = work.join("rust-target");
    let cargo_home = std::env::var_os("CARGO_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cargo")));
    let rustup_home = std::env::var_os("RUSTUP_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".rustup")));
    let sysroot = untrusted_driver::rustc_sysroot(repo_root)?;
    let rustc_commit = untrusted_driver::rustc_commit_hash(rustc_version)?;
    let encoded_flags = rust_encoded_rustflags(
        repo_root,
        work,
        cargo_home.as_deref(),
        rustup_home.as_deref(),
        Some((&sysroot, rustc_commit)),
    );
    let mut c = Command::new(&cargo);
    c.current_dir(repo_root)
        .env("CARGO_TARGET_DIR", &target_dir)
        .env("CARGO_ENCODED_RUSTFLAGS", encoded_flags)
        .env_remove("RUSTFLAGS")
        .args(["build", "--manifest-path"])
        .arg(&manifest_path)
        .args([
            "--target",
            "aarch64-unknown-linux-musl",
            "--release",
            "--locked",
        ]);
    run_cmd(&mut c)?;
    let release_dir = target_dir
        .join("aarch64-unknown-linux-musl")
        .join("release");
    let mut archives: Vec<PathBuf> = std::fs::read_dir(&release_dir)?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| {
            p.is_file()
                && p.extension().is_some_and(|ext| ext == "a")
                && p.file_name()
                    .and_then(|n| n.to_str())
                    .is_some_and(|n| n.starts_with("lib"))
        })
        .collect();
    archives.sort();
    ensure!(
        archives.len() == 1,
        "expected exactly 1 staticlib `lib*.a` in {}, found {:?}",
        release_dir.display(),
        archives
    );
    let out_archive = work.join("main_rust.a");
    run_cmd(
        Command::new(objcopy)
            .args(["--enable-deterministic-archives", "--strip-debug"])
            .arg(&archives[0])
            .arg(&out_archive),
    )?;
    Ok(out_archive)
}

/// Run the non-`--stock` CLI modes (`--check-std-toolchain` or `--main-rust <StdBin Cargo.toml>`).
pub fn run(cli: Cli) -> Result<()> {
    if cli.check_std_toolchain {
        let msg = crate::std_profile::check_std_toolchain()?;
        println!("{msg}");
        return Ok(());
    }
    ensure!(!cli.out_dir.as_os_str().is_empty(), "--out-dir is required");
    ensure!(
        cli.config.is_empty(),
        "--stock is required when linking --config objects"
    );
    ensure!(
        cli.main_c.is_none(),
        "--stock is required when linking --main-c"
    );
    let repo_root = std::fs::canonicalize(&cli.repo_root)?;
    let Some(manifest_rel) = &cli.main_rust else {
        bail!(
            "at least one --config (with --stock) or --main-rust <Cargo.toml> (for a Rust std \
             binary crate) is required"
        );
    };
    match crate::std_profile::classify_rust_manifest(manifest_rel, &repo_root)? {
        crate::std_profile::RustMainKind::Staticlib => {
            bail!("--stock is required when linking a staticlib --main-rust")
        }
        crate::std_profile::RustMainKind::StdBin(std_crate) => {
            link_std_bin(&cli, &repo_root, &std_crate)
        }
    }
}

fn write_std_link_manifest(
    cli: &Cli,
    out_dir: &Path,
    elf_bytes: &[u8],
    std_tc: &crate::std_profile::StdToolchain,
    objcopy: &Path,
    input_paths: &[PathBuf],
) -> Result<()> {
    let input_hash = |p: &Path| -> Result<serde_json::Value> {
        let shown = match p.strip_prefix(out_dir) {
            Ok(rel) => rel.display().to_string(),
            Err(_) => p.file_name().map_or_else(
                || p.display().to_string(),
                |n| n.to_string_lossy().into_owned(),
            ),
        };
        Ok(serde_json::json!({ "path": shown, "sha256": sha256(&std::fs::read(p)?) }))
    };
    let inputs: Vec<serde_json::Value> = input_paths
        .iter()
        .map(|p| input_hash(p))
        .collect::<Result<_>>()?;
    let tools_json = serde_json::json!({
        "rust-lld": std_tc.lld.version()?,
        "llvm-objcopy": version(objcopy, "--version")?,
    });
    let manifest = serde_json::json!({
        "schema": "snapshot-link/1",
        "config": serde_json::Value::Null,
        "base": DEFAULT_BASE,
        "stubMode": "branch",
        "elf": { "file": cli.name, "sha256": sha256(elf_bytes) },
        "image": serde_json::Value::Null,
        "stubs": [],
        "check": {
            "codeBytes": 0,
            "stubWords": 0,
            "dataBytes": 0,
            "relocs": 0,
            "symbols": 0,
            "errors": [],
        },
        "stdProfile": std_tc.std_profile_json(),
        "tools": tools_json,
        "inputs": inputs,
    });
    std::fs::write(
        out_dir.join("link.json"),
        serde_json::to_string_pretty(&manifest)? + "\n",
    )?;
    Ok(())
}

/// Compile `std_crate` under the pinned Rust 1.98.1 `-Zbuild-std=std,panic_abort` profile, link
/// it with the bundled musl `self-contained` runtime via `rust-lld`, run
/// [`verify::check_std_elf`], and write `link.json`.
pub fn link_std_bin(
    cli: &Cli,
    repo_root: &Path,
    std_crate: &crate::std_profile::StdBinCrate,
) -> Result<()> {
    let std_tc = crate::std_profile::StdToolchain::resolve()?;
    let objcopy = std_tc.resolve_objcopy()?;

    std::fs::create_dir_all(&cli.out_dir)?;
    let out_dir = std::fs::canonicalize(&cli.out_dir)?;
    let work = out_dir.join("work");
    std::fs::create_dir_all(&work)?;

    let (main_rust_o, compiler_builtins_a) =
        crate::std_profile::build_std_main_objects(&std_tc, std_crate, repo_root, &work, &objcopy)?;

    let runtime_dir = work.join("runtime");
    if runtime_dir.exists() {
        std::fs::remove_dir_all(&runtime_dir)?;
    }
    let staged_pre = stage_runtime_inputs(&objcopy, &std_tc.self_contained_pre(), &runtime_dir)?;
    let staged_libs = stage_runtime_inputs(
        &objcopy,
        &[std_tc.self_contained_libc(), std_tc.self_contained_unwind()],
        &runtime_dir,
    )?;
    let staged_post = stage_runtime_inputs(&objcopy, &std_tc.self_contained_post(), &runtime_dir)?;
    let (staged_libc, staged_unwind) = (&staged_libs[0], &staged_libs[1]);

    let script = work.join("link.ld");
    std::fs::write(&script, linker_script_std())?;
    let exe = out_dir.join(&cli.name);
    let mut c = std_tc.lld.command();
    c.args([
        "-static",
        "-no-pie",
        "--gc-sections",
        "--icf=none",
        "--no-relax",
        "-z",
        "norelro",
        "-z",
        "max-page-size=4096",
        "-z",
        "common-page-size=4096",
        "-z",
        "noexecstack",
        "-O0",
        "--build-id=none",
        "--strip-debug",
        "-e",
        "_start",
        "-T",
    ])
    .arg(&script)
    .arg("-o")
    .arg(&exe)
    .args(&staged_pre)
    .arg("--start-group")
    .arg(&main_rust_o)
    .arg(staged_libc)
    .arg(&compiler_builtins_a)
    .arg("--as-needed")
    .arg(staged_unwind)
    .arg("--no-as-needed")
    .arg("--end-group")
    .args(&staged_post);
    run_cmd(&mut c)?;

    let elf_bytes = std::fs::read(&exe)?;
    let mut input_paths: Vec<PathBuf> = Vec::new();
    input_paths.extend(staged_pre);
    input_paths.push(main_rust_o);
    input_paths.push(staged_libc.clone());
    input_paths.push(compiler_builtins_a);
    input_paths.push(staged_unwind.clone());
    input_paths.extend(staged_post);

    write_std_link_manifest(cli, &out_dir, &elf_bytes, &std_tc, &objcopy, &input_paths)?;
    verify::check_std_elf(&elf_bytes)?;
    println!(
        "{}: std ELF check ok ({} bytes)",
        exe.display(),
        elf_bytes.len()
    );
    Ok(())
}
