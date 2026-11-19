// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Export pipeline and CLI dispatch for `rust-obj2lean` (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]`. This module sequences the export pipeline and writes files
//!   to disk; placed-library outputs (`Obj.PlacedLib` / `Obj.MultiPlacedLib`) are produced by
//!   [`crate::untrusted_placed`] and optional `Obj.ExtractedObj` outputs are produced by
//!   [`crate::trusted_extractor::emit_extracted_obj_lean_module`].
//! - **Purpose:**
//!   1. [`generate_config`] / [`generate_config_with`]: run `untrusted_driver::extract` →
//!      [`emit_placed_and_extracted_files`] (`untrusted_placed::generate` plus optional
//!      `Obj.ExtractedObj`).
//!   2. [`write_or_check`]: write a generated file or (`--check`) diff it against the on-disk
//!      copy.
//!   3. [`cli_main`]: `clap` dispatch for `export`, `fetch-decode-lemmas`, `symexec`,
//!      `print-cflags`, and `layout`.
//!
//! # When to Read This File
//! - Read this file when changing CLI subcommands, `--check` diffing, shard-file cleanup, or the
//!   order in which artefacts are generated.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::{Context, Result, bail};
use clap::Parser;
use similar::TextDiff;

use crate::untrusted_driver::{
    self, Cli, CommandName, ExportConfig, Toolchain, apply_module_prefix_override,
    apply_overrides, apply_perturb_layout_override, default_config_paths, load_configs,
    native_cflags_string, resolve_cli_existing_or_repo_path, resolve_cli_output_path,
    select_configs,
};
use crate::{trusted_extractor, untrusted_lemmas};

/// One generated file: its path and contents.
pub struct GeneratedFile {
    pub path: PathBuf,
    pub contents: Vec<u8>,
    /// Whether `contents` is text (diffable in `--check` mode).
    pub text: bool,
}

/// Build all files generated for `cfg` (`Obj.PlacedLib` / `Obj.MultiPlacedLib` files plus
/// optional `Obj.ExtractedObj` module and binary sidecar).
pub fn generate_config(cfg: &ExportConfig, tc: &mut Toolchain) -> Result<Vec<GeneratedFile>> {
    generate_config_with(cfg, tc, true)
}

fn push_extracted_obj(
    files: &mut Vec<GeneratedFile>,
    cfg: &ExportConfig,
    ex: &crate::trusted_common::Extraction,
) {
    let ((lean_path, lean_src), (bin_path, bin_bytes)) =
        trusted_extractor::emit_extracted_obj_lean_module(&cfg.obj_meta(), ex);
    files.push(GeneratedFile {
        path: lean_path,
        contents: lean_src.into_bytes(),
        text: true,
    });
    files.push(GeneratedFile {
        path: bin_path,
        contents: bin_bytes,
        text: false,
    });
}

fn emit_placed_and_extracted_files(
    files: &mut Vec<GeneratedFile>,
    cfg: &ExportConfig,
    ex: &crate::trusted_common::Extraction,
) -> Result<()> {
    if cfg.placed.as_ref().is_some_and(|p| p.emit_extracted_obj) {
        push_extracted_obj(files, cfg, ex);
    }
    for (path, contents, text) in crate::untrusted_placed::generate(cfg, &ex.objects)? {
        files.push(GeneratedFile {
            path,
            contents,
            text,
        });
    }
    Ok(())
}

/// [`generate_config`], accepting a `with_dwarf` flag for caller compatibility.
pub fn generate_config_with(
    cfg: &ExportConfig,
    tc: &mut Toolchain,
    _with_dwarf: bool,
) -> Result<Vec<GeneratedFile>> {
    if cfg.placed.is_none() {
        bail!(
            "`{}` has no `[placed]` section; configure `[placed]` for `Obj.PlacedLib` / `Obj.MultiPlacedLib`",
            cfg.config_rel
        );
    }
    let ex = untrusted_driver::extract(cfg, tc)?;
    let trace = std::env::var("RUST_OBJ2LEAN_TRACE_PIPELINE").as_deref() == Ok("1");
    let emit_raw = cfg.placed.as_ref().is_some_and(|p| p.emit_extracted_obj);
    let mut files = Vec::new();
    emit_placed_and_extracted_files(&mut files, cfg, &ex)?;
    if trace {
        eprintln!(
            "[pipeline] config={} objects={} emit_extracted_obj={}",
            cfg.config_rel,
            ex.objects.len(),
            emit_raw
        );
    }
    Ok(files)
}

static NEXT_TMP_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Write `contents` to a temporary file in `path`'s parent directory, then rename it over `path`
/// so any existing hardlink at `path` is unlinked rather than truncated in place.
pub(crate) fn write_atomic(path: &Path, contents: &[u8]) -> Result<()> {
    let parent = path
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."));
    fs::create_dir_all(parent)
        .with_context(|| format!("failed to create {}", parent.display()))?;
    let file_name = path
        .file_name()
        .and_then(|n| n.to_str())
        .unwrap_or("generated");
    let pid = std::process::id();
    let seq = NEXT_TMP_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let tmp_path = parent.join(format!(".{file_name}.tmp.{pid}.{seq}"));
    let _ = fs::remove_file(&tmp_path);
    let write_res = (|| -> std::io::Result<()> {
        use std::io::Write;
        let mut f = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&tmp_path)?;
        f.write_all(contents)
    })();
    if let Err(e) = write_res {
        let _ = fs::remove_file(&tmp_path);
        return Err(e).with_context(|| format!("failed to write {}", tmp_path.display()));
    }
    if let Err(e) = fs::rename(&tmp_path, path) {
        let _ = fs::remove_file(&tmp_path);
        return Err(e).with_context(|| {
            format!(
                "failed to rename {} to {}",
                tmp_path.display(),
                path.display()
            )
        });
    }
    Ok(())
}

/// Write (or, with `check`, compare) `file`. Returns whether it was up to date.
pub(crate) fn write_or_check(
    file: &GeneratedFile,
    display_base: &Path,
    check: bool,
) -> Result<bool> {
    let rel = file
        .path
        .strip_prefix(display_base)
        .unwrap_or(&file.path)
        .display()
        .to_string();
    let existing = fs::read(&file.path).ok();
    let up_to_date = existing.as_deref() == Some(file.contents.as_slice());
    if check {
        if up_to_date {
            println!("[OK] {rel}");
        } else if file.text {
            let old = existing
                .as_deref()
                .map(String::from_utf8_lossy)
                .unwrap_or_default();
            let new = String::from_utf8_lossy(&file.contents);
            let diff = TextDiff::from_lines(old.as_ref(), new.as_ref());
            eprint!(
                "{}",
                diff.unified_diff()
                    .header(&rel, &format!("{rel} (expected)"))
            );
        } else {
            eprintln!("error: {rel} differs from the freshly built object");
        }
        return Ok(up_to_date);
    }
    if up_to_date {
        println!("Up to date {rel}");
    } else {
        write_atomic(&file.path, &file.contents)
            .with_context(|| format!("failed to write {}", file.path.display()))?;
        println!("Exported {rel}");
    }
    Ok(true)
}

fn run(cli: &Cli, check: bool, only: &[String]) -> Result<bool> {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("CARGO_MANIFEST_DIR must be at <repo>/tools/rust-obj2lean")
        .to_path_buf();

    let config_paths: Vec<PathBuf> = if cli.config.is_empty() {
        default_config_paths(&repo_root)
    } else {
        cli.config
            .iter()
            .map(|p| resolve_cli_existing_or_repo_path(&repo_root, p))
            .collect()
    };
    let out_dir = cli
        .out_dir
        .as_deref()
        .map(|d| resolve_cli_output_path(&repo_root, d));
    let output_file = cli
        .output
        .as_deref()
        .map(|f| resolve_cli_output_path(&repo_root, f));

    let configs = load_configs(&config_paths, &repo_root, out_dir.as_deref())?;
    let mut configs = select_configs(configs, only)?;
    apply_overrides(
        &mut configs,
        output_file.as_deref(),
        cli.namespace_prefix.as_deref(),
        cli.sub_namespace.as_deref(),
    )?;
    apply_module_prefix_override(&mut configs, cli.module_prefix.as_deref());
    apply_perturb_layout_override(&mut configs, cli.perturb_layout)?;
    if cli.emit_symbol_unique_lemmas {
        for cfg in &mut configs {
            cfg.emit_symbol_unique_lemmas = true;
        }
    }
    if cli.multi_placed {
        for cfg in &mut configs {
            if let Some(p) = &mut cfg.placed {
                p.multi = true;
            }
        }
    }
    if cli.placed_only {
        for cfg in &mut configs {
            if let Some(p) = &mut cfg.placed {
                p.placed_only = true;
            }
        }
    }
    if cli.extracted_obj {
        for cfg in &mut configs {
            if let Some(p) = &mut cfg.placed {
                p.emit_extracted_obj = true;
            }
        }
    }
    if cli.placed_witness || cli.placed_witness_out.is_some() {
        let out_override = cli
            .placed_witness_out
            .as_deref()
            .map(|f| resolve_cli_output_path(&repo_root, f));
        for cfg in &mut configs {
            if let Some(p) = &mut cfg.placed {
                p.emit_placeable_witness = true;
                if let Some(ref f) = out_override {
                    p.witness_file = f.clone();
                }
            }
        }
    }

    // A config whose witnesses import a facts module emitted by another config
    // (`elf_facts_module`) reads that module from disk, so generate it after every config that
    // emits facts modules (stable, so the given order is otherwise kept).
    configs.sort_by_key(|cfg| {
        cfg.placed.as_ref().is_some_and(|p| {
            p.elf_facts_module.is_some()
                || p.extra_witnesses.iter().any(|x| x.elf_facts_module.is_some())
        })
    });
    let mut tc = Toolchain::new(repo_root.clone())?;
    let display_base = out_dir.clone().unwrap_or(repo_root);
    let mut all_ok = true;
    for cfg in &configs {
        let files = generate_config(cfg, &mut tc)
            .with_context(|| format!("cannot export `{}`", cfg.config_rel))?;
        for file in &files {
            all_ok &= write_or_check(file, &display_base, check)?;
        }
        if !check {
            let emitted_paths: std::collections::BTreeSet<&Path> =
                files.iter().map(|f| f.path.as_path()).collect();
            for i in 0..32 {
                let (shard_path, _) = cfg.code_shard_file(i);
                if !emitted_paths.contains(shard_path.as_path()) && shard_path.exists() {
                    let _ = fs::remove_file(&shard_path);
                }
            }
            for target in &cfg.targets {
                for i in 0..32 {
                    let (shard_path, _) = target.shard_file(i);
                    if !emitted_paths.contains(shard_path.as_path()) && shard_path.exists() {
                        let _ = fs::remove_file(&shard_path);
                    }
                }
            }
        }
    }
    Ok(all_ok)
}

/// Top-level CLI entry point (`export`, `fetch-decode-lemmas`, `symexec`, `print-cflags`,
/// `layout`).
pub fn cli_main() -> ExitCode {
    let mut raw_args = std::env::args();
    if let (Some(_bin), Some(sub)) = (raw_args.next(), raw_args.next())
        && (sub == "symexec" || sub == "sym-exec")
    {
        let rest: Vec<String> = raw_args.collect();
        return untrusted_lemmas::symexec::run_symexec_cli(&rest);
    }
    let mut raw_args = std::env::args().skip(1);
    if let Some(sub) = raw_args.next() {
        let rest: Vec<String> = raw_args.collect();
        if sub.as_str() == "layout" {
            return untrusted_lemmas::dwarf::cli::run_layout_cli(&rest);
        }
    }

    let cli = Cli::parse();

    if cli.print_cflags || matches!(cli.command, Some(CommandName::PrintCflags)) {
        println!("{}", native_cflags_string(&[]));
        return ExitCode::SUCCESS;
    }

    let (check, only) = match &cli.command {
        Some(CommandName::PrintCflags) => unreachable!(),
        Some(CommandName::FetchDecodeLemmas {
            check,
            prog,
            base,
            inputs,
        }) => {
            return untrusted_lemmas::run_fetch_decode_lemmas(*check, prog.clone(), base, inputs);
        }
        Some(CommandName::Export { check, only }) => {
            let mut combined = cli.only.clone();
            combined.extend(only.iter().cloned());
            (cli.check || *check, combined)
        }
        None => (cli.check, cli.only.clone()),
    };

    match run(&cli, check, &only) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(e) => {
            eprintln!("error: {e:#}");
            ExitCode::FAILURE
        }
    }
}
