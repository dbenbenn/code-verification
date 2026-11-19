// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Unit and integration tests for the `rust-obj2lean` crate root (`Role::Test`, `[TEST ONLY]`).
//!
//! Covers `translation.toml` loading and resolution, CLI flag handling, `--check` diffing
//! (`write_or_check`), `print-cflags`, end-to-end C archive builds, DWARF index hints, and the
//! structural check that `[TCB]` modules never import `untrusted_lemmas`. Tests that need `zig`
//! or `cargo` toolchains are skipped (with a message) when unavailable.

use super::*;
use crate::untrusted_driver::pipeline::{
    GeneratedFile, generate_config, generate_config_with, write_or_check,
};
use crate::untrusted_driver::{
    Cli, CommandName, Toolchain, apply_overrides, load_config, load_configs,
    native_cflags_string, normalize_path, select_configs,
};
use clap::Parser;
use std::fs;
use std::path::{Path, PathBuf};

fn test_repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("CARGO_MANIFEST_DIR must be at <repo>/tools/rust-obj2lean")
        .to_path_buf()
}

/// Every `translation.toml` under the in-repo campaign roots that exists on disk, sorted.
///
/// Discovered instead of hardcoded so the tests keep passing in partial exports of this
/// repository that drop some `CaseStudies/<Campaign>` directories.
fn discover_repo_config_paths(roots: &[&str]) -> Vec<PathBuf> {
    fn walk(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name();
            let name = name.to_string_lossy();
            let Ok(ft) = entry.file_type() else { continue };
            if ft.is_dir() {
                if name.starts_with('.')
                    || matches!(
                        name.as_ref(),
                        "target" | "vendor" | "Generated" | "node_modules" | "build"
                    )
                {
                    continue;
                }
                walk(&path, out);
            } else if ft.is_file() && name == "translation.toml" {
                out.push(path);
            }
        }
    }
    let repo_root = test_repo_root();
    let mut out = Vec::new();
    for root in roots {
        walk(&repo_root.join(root), &mut out);
    }
    out.sort();
    out
}

/// Writes a Rust crate stub (`Cargo.toml`, `Cargo.lock`, `src/lib.rs`) plus `translation.toml`
/// at `<repo_root>/<crate_rel>/` and returns the config path.
fn write_fixture_crate(repo_root: &Path, crate_rel: &str, package: &str, toml: &str) -> PathBuf {
    let crate_dir = repo_root.join(crate_rel);
    fs::create_dir_all(crate_dir.join("src")).unwrap();
    fs::write(
        crate_dir.join("Cargo.toml"),
        format!("[package]\nname = \"{package}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n"),
    )
    .unwrap();
    fs::write(crate_dir.join("Cargo.lock"), "version = 4\n").unwrap();
    fs::write(crate_dir.join("src/lib.rs"), "").unwrap();
    let toml_path = crate_dir.join("translation.toml");
    fs::write(&toml_path, toml).unwrap();
    toml_path
}

/// Synthetic repository with three per-crate configs laid out like real campaigns:
///
/// - `CaseStudies/Alpha`: one crate, explicit `namespace_prefix`, crate- and target-level
///   `hashed_inputs`, `placed_only`;
/// - `CaseStudies/Beta`: one crate with a default (inferred) `namespace_prefix`;
/// - `CaseStudies/Gamma`: two crates (`widget-toy`, `widget`), `lemma_shards = 8`,
///   `placed_only`, no `namespace_prefix` (so `--out-dir GeneratedLean` infers it).
struct FixtureRepo {
    dir: tempfile::TempDir,
    alpha: PathBuf,
    beta: PathBuf,
    gamma: PathBuf,
}

impl FixtureRepo {
    fn new() -> Self {
        let dir = tempfile::tempdir().unwrap();
        let root = normalize_path(dir.path());
        let alpha = write_fixture_crate(
            &root,
            "CaseStudies/Alpha/Implementation",
            "alpha",
            r#"
crates = ["alpha"]
obj_name = "alpha"
namespace_prefix = "Examples"
hashed_inputs = ["Cargo.toml", "Cargo.lock", "src/lib.rs"]

[[targets]]
name = "alpha"
lean_file = "Generated/AlphaFns.lean"
prog_name = "alphaBin"
title = "Alpha"
hashed_inputs = ["src/alpha.rs"]
lemma_allowlist = ["alpha_encode", "alpha_decode"]

[placed]
placed_only = true
exports = ["alpha::alpha::alpha_encode", "alpha::alpha::alpha_decode"]
"#,
        );
        let beta = write_fixture_crate(
            &root,
            "CaseStudies/Beta/Implementation",
            "beta",
            r#"
crates = ["beta"]
obj_name = "beta"
hashed_inputs = ["Cargo.toml", "Cargo.lock", "src/lib.rs"]

[[targets]]
name = "beta_fns"
lean_file = "Generated/BetaFns.lean"
prog_name = "betaBin"
title = "Beta"
lemma_allowlist = ["beta_add"]
"#,
        );
        let gamma = write_fixture_crate(
            &root,
            "CaseStudies/Gamma/Implementation",
            "widget-toy",
            r#"
crates = ["widget-toy", "widget"]
obj_name = "widgetToy"
hashed_inputs = ["Cargo.toml", "Cargo.lock", "src/lib.rs"]

[[targets]]
name = "widget_toy"
lean_file = "Generated/WidgetToyFetch.lean"
prog_name = "widgetToyBin"
title = "Gamma"
lemma_shards = 8
lemma_allowlist = ["widget_toy_encode", "widget::encoding::.*"]

[placed]
placed_only = true
exports = []
"#,
        );
        Self {
            dir,
            alpha,
            beta,
            gamma,
        }
    }

    fn root(&self) -> PathBuf {
        normalize_path(self.dir.path())
    }

    fn config_paths(&self) -> Vec<PathBuf> {
        vec![self.alpha.clone(), self.beta.clone(), self.gamma.clone()]
    }
}

#[test]
fn placed_shards_resolves_sibling_shard_modules_and_requires_multi() {
    let dir = tempfile::tempdir().unwrap();
    let root = normalize_path(dir.path());
    let cfg = |shards: &str, multi: &str| {
        format!(
            "crates = [\"delta\"]\nobj_name = \"delta\"\n\n[placed]\nplaced_only = true\n{multi}{shards}exports = []\n"
        )
    };
    let path = write_fixture_crate(
        &root,
        "CaseStudies/Delta/Implementation",
        "delta",
        &cfg("placed_shards = 3\n", "multi = true\n"),
    );
    let configs = load_configs(std::slice::from_ref(&path), &root, None).unwrap();
    let p = configs[0].placed.as_ref().unwrap();
    assert_eq!(p.placed_shards, 3);
    assert!(p.lib_file.ends_with("Generated/DeltaPlacedObj.lean"));
    assert_eq!(
        p.shard_files(),
        (0..3)
            .map(|k| p.lib_file.with_file_name(format!("DeltaPlacedObjShard{k}.lean")))
            .collect::<Vec<_>>()
    );
    assert_eq!(p.shard_module(2), format!("{}Shard2", p.lib_module));
    assert!(p.lib_module.ends_with("Generated.DeltaPlacedObj"));

    // Omitted, `0` and `1` all mean a single module with no shard files.
    for shards in ["", "placed_shards = 0\n", "placed_shards = 1\n"] {
        fs::write(&path, cfg(shards, "multi = true\n")).unwrap();
        let configs = load_configs(std::slice::from_ref(&path), &root, None).unwrap();
        let p = configs[0].placed.as_ref().unwrap();
        assert_eq!(p.placed_shards, 1);
        assert!(p.shard_files().is_empty());
    }

    // Sharding applies only to the multi-block library.
    fs::write(&path, cfg("placed_shards = 2\n", "")).unwrap();
    let err = load_configs(std::slice::from_ref(&path), &root, None).unwrap_err();
    assert!(format!("{err:#}").contains("requires `multi = true`"), "{err:#}");
}

#[test]
fn extern_boundary_parses_and_requires_multi() {
    let dir = tempfile::tempdir().unwrap();
    let root = normalize_path(dir.path());
    let cfg = |multi: &str, boundary: &str| {
        format!(
            "crates = [\"delta\"]\nobj_name = \"delta\"\n\n[placed]\nplaced_only = true\n{multi}{boundary}exports = [\"alpha\"]\n"
        )
    };
    let path = write_fixture_crate(
        &root,
        "CaseStudies/Delta/Implementation",
        "delta",
        &cfg("multi = true\n", "extern_boundary = [\"beta\", \"gamma\"]\n"),
    );
    let configs = load_configs(std::slice::from_ref(&path), &root, None).unwrap();
    let p = configs[0].placed.as_ref().unwrap();
    assert_eq!(p.extern_boundary, vec!["beta".to_string(), "gamma".to_string()]);
    // Omitted: empty.
    fs::write(&path, cfg("multi = true\n", "")).unwrap();
    let configs = load_configs(std::slice::from_ref(&path), &root, None).unwrap();
    assert!(configs[0].placed.as_ref().unwrap().extern_boundary.is_empty());
    // The boundary prunes the multi-block reachability cone only.
    fs::write(&path, cfg("", "extern_boundary = [\"beta\"]\n")).unwrap();
    let err = load_configs(std::slice::from_ref(&path), &root, None).unwrap_err();
    assert!(format!("{err:#}").contains("`[placed] extern_boundary` requires `multi = true`"), "{err:#}");
}

#[test]
fn per_crate_configs_parse_and_resolve() {
    let fx = FixtureRepo::new();
    let repo_root = fx.root();

    let configs = load_configs(&fx.config_paths(), &repo_root, None)
        .expect("all per-crate translation.toml configs should parse cleanly");
    let names: Vec<&str> = configs
        .iter()
        .flat_map(|c| c.targets.iter().map(|t| t.name.as_str()))
        .collect();
    assert_eq!(names, vec!["alpha", "beta_fns", "widget_toy"]);

    let alpha = &configs[0];
    assert_eq!(alpha.crate_dir, repo_root.join("CaseStudies/Alpha/Implementation"));
    assert_eq!(alpha.crates, vec!["alpha".to_string()]);
    assert_eq!(alpha.config_rel, "CaseStudies/Alpha/Implementation/translation.toml");
    assert_eq!(
        alpha.obj_file,
        repo_root.join("CaseStudies/Alpha/Generated/AlphaObj.lean")
    );
    assert_eq!(alpha.obj_module, "CaseStudies.Alpha.Generated.AlphaObj");
    assert_eq!(alpha.namespace_prefix, "Examples");
    assert_eq!(
        alpha.code_bin_file(),
        repo_root.join("CaseStudies/Alpha/Generated/AlphaObj.code.bin")
    );
    assert_eq!(alpha.obj_def_name("alpha"), "alphaObj");
    assert_eq!(alpha.image_def_name(), "alphaImage");
    let placed = alpha.placed.as_ref().expect("alpha has [placed]");
    assert!(placed.placed_only);
    assert_eq!(
        placed.lib_file,
        repo_root.join("CaseStudies/Alpha/Generated/AlphaPlacedObj.lean")
    );
    assert_eq!(placed.lib_module, "CaseStudies.Alpha.Generated.AlphaPlacedObj");

    let beta = &configs[1];
    assert_eq!(beta.crate_dir, repo_root.join("CaseStudies/Beta/Implementation"));
    assert_eq!(beta.config_rel, "CaseStudies/Beta/Implementation/translation.toml");
    assert_eq!(beta.obj_def_name("beta"), "betaObj");
    assert_eq!(beta.namespace_prefix, "Examples");
    assert!(beta.placed.is_none());

    let gamma = &configs[2];
    assert_eq!(gamma.crate_dir, repo_root.join("CaseStudies/Gamma/Implementation"));
    assert_eq!(gamma.config_rel, "CaseStudies/Gamma/Implementation/translation.toml");
    assert_eq!(
        gamma.crates,
        vec!["widget_toy".to_string(), "widget".to_string()]
    );
    assert_eq!(gamma.object_names(), vec!["widget_toy", "widget"]);
    assert_eq!(gamma.obj_def_name("widget"), "widgetToyWidgetObj");
    assert_eq!(gamma.image_def_name(), "widgetToyImage");
    assert_eq!(
        gamma.code_bin_file(),
        repo_root.join("CaseStudies/Gamma/Generated/WidgetToyObj.code.bin")
    );
    assert_eq!(gamma.targets[0].lemma_shards, 8);
    assert_eq!(gamma.targets[0].explicit_lemma_shards, Some(8));

    let alpha_tgt = &alpha.targets[0];
    assert_eq!(
        alpha_tgt.lean_file,
        repo_root.join("CaseStudies/Alpha/Generated/AlphaFns.lean")
    );
    assert_eq!(alpha_tgt.lean_module, "CaseStudies.Alpha.Generated.AlphaFns");
    assert_eq!(
        alpha_tgt.hashed_inputs,
        vec!["Cargo.toml", "Cargo.lock", "src/lib.rs", "src/alpha.rs"]
    );
}

#[test]
fn all_in_repo_translation_configs_parse_and_resolve() {
    // Coverage check over whatever configs are present on disk (partial exports of this
    // repository drop some campaigns, so the list is discovered rather than hardcoded).
    let repo_root = test_repo_root();
    let cfg_paths =
        discover_repo_config_paths(&["CaseStudies", "VerifiedLibraries", "Arm64/Testing"]);
    for p in &cfg_paths {
        let cfg = load_config(p, &repo_root, None)
            .unwrap_or_else(|e| panic!("`{}` should parse: {e:#}", p.display()));
        if !cfg.crates.is_empty() {
            assert!(
                cfg.crate_dir.join("Cargo.toml").is_file(),
                "Rust config `{}` resolves crate_dir `{}` without a Cargo.toml",
                cfg.config_rel,
                cfg.crate_dir.display()
            );
        }
        assert!(
            !cfg.targets.is_empty() || cfg.placed.is_some(),
            "config `{}` defines neither targets nor [placed]",
            cfg.config_rel
        );
    }
}

#[test]
fn out_dir_resolves_generated_files_to_external_directory() {
    let fx = FixtureRepo::new();
    let repo_root = fx.root();
    let temp_out = tempfile::tempdir().unwrap();

    let configs = load_configs(&fx.config_paths(), &repo_root, Some(temp_out.path()))
        .expect("configs should load with custom --out-dir");
    let out = temp_out.path();
    assert_eq!(configs[0].obj_file, out.join("Generated/AlphaObj.lean"));
    assert_eq!(
        configs[0].targets[0].lean_file,
        out.join("Generated/AlphaFns.lean")
    );
    assert_eq!(configs[1].obj_file, out.join("Generated/BetaObj.lean"));
    assert_eq!(configs[2].obj_file, out.join("Generated/WidgetToyObj.lean"));
    // Crate sources still resolve against the repository, not the output directory.
    assert_eq!(
        configs[2].crate_dir,
        repo_root.join("CaseStudies/Gamma/Implementation")
    );
}

#[test]
fn out_dir_pointing_to_generated_subdir_places_file_directly_and_infers_namespace() {
    let fx = FixtureRepo::new();
    let repo_root = fx.root();
    let temp_out = tempfile::tempdir().unwrap();
    let gen_dir = temp_out.path().join("GeneratedLean");

    let cfg = load_config(&fx.gamma, &repo_root, Some(&gen_dir))
        .expect("gamma config should load with --out-dir GeneratedLean");
    assert_eq!(cfg.targets.len(), 1);
    assert_eq!(cfg.targets[0].lean_file, gen_dir.join("WidgetToyFetch.lean"));
    assert_eq!(cfg.obj_file, gen_dir.join("WidgetToyObj.lean"));
    assert_eq!(cfg.namespace_prefix, "GeneratedLean");
}

#[test]
fn lemma_shards_default_and_shard_file_naming() {
    let fx = FixtureRepo::new();
    let repo_root = fx.root();
    let cfg = load_config(&fx.alpha, &repo_root, None).unwrap();
    let functions = &cfg.targets[0];
    assert_eq!(functions.lemma_shards, 1);
    assert_eq!(functions.explicit_lemma_shards, None);
    let (path, module) = functions.shard_file(2);
    assert_eq!(
        path,
        repo_root.join("CaseStudies/Alpha/Generated/AlphaFnsShard2.lean")
    );
    assert_eq!(module, "CaseStudies.Alpha.Generated.AlphaFnsShard2");
}

#[test]
fn output_flag_and_namespace_overrides_work() {
    let fx = FixtureRepo::new();
    let repo_root = fx.root();
    let mut cfg = load_config(&fx.alpha, &repo_root, None).unwrap();
    cfg.targets.push(cfg.targets[0].clone());
    assert_eq!(cfg.targets.len(), 2);

    let custom_out = PathBuf::from("/tmp/custom/CustomOutput.lean");
    let mut multi = vec![cfg.clone()];
    let err = apply_overrides(&mut multi, Some(&custom_out), None, None)
        .expect_err("--output with several targets must fail");
    assert!(err.to_string().contains("single target"));

    let mut single = vec![cfg];
    single[0].targets.truncate(1);
    apply_overrides(
        &mut single,
        Some(&custom_out),
        Some("RootProject"),
        Some("Functions"),
    )
    .expect("--output on a single target should succeed");
    assert_eq!(single[0].targets[0].lean_file, custom_out);
    assert_eq!(
        single[0].obj_file,
        PathBuf::from("/tmp/custom/AlphaObj.lean")
    );
    assert_eq!(single[0].namespace_prefix, "RootProject");
    assert_eq!(
        single[0].targets[0].sub_namespace.as_deref(),
        Some("Functions")
    );
    assert_eq!(
        single[0].target_namespace(&single[0].targets[0]),
        "RootProject.Functions"
    );
}

#[test]
fn select_configs_filters_by_target_name() {
    let fx = FixtureRepo::new();
    let configs = load_configs(&fx.config_paths(), &fx.root(), None).unwrap();
    let selected = select_configs(configs.clone(), &["beta_fns".to_string()]).unwrap();
    assert_eq!(selected.len(), 1);
    assert_eq!(selected[0].obj_name, configs[1].obj_name);
    let selected = select_configs(
        configs.clone(),
        &["alpha".to_string(), "widget_toy".to_string()],
    )
    .unwrap();
    assert_eq!(
        selected.iter().map(|c| c.obj_name.as_str()).collect::<Vec<_>>(),
        vec!["alpha", "widgetToy"]
    );
    let err = select_configs(configs, &["nope".to_string()]).unwrap_err();
    assert!(err.to_string().contains("unknown target `nope`"));
}

fn write_tmp_crate(name: &str, toml: &str) -> (tempfile::TempDir, PathBuf) {
    let tmp_crate = tempfile::tempdir().unwrap();
    fs::write(
        tmp_crate.path().join("Cargo.toml"),
        format!("[package]\nname = \"{name}\"\nversion = \"0.1.0\"\nedition = \"2024\"\n"),
    )
    .unwrap();
    let toml_path = tmp_crate.path().join("translation.toml");
    fs::write(&toml_path, toml).unwrap();
    (tmp_crate, toml_path)
}

#[test]
fn self_contained_crate_config_defaults_crate_dir_and_infers_package_name() {
    let tmp_out = tempfile::tempdir().unwrap();
    let (tmp_crate, toml_path) = write_tmp_crate(
        "external-crypto-crate",
        r#"
obj_name = "extCrypto"

[[targets]]
name = "ext-target"
lean_file = "Generated/ExtCrypto.lean"
prog_name = "extCryptoBin"
title = "External Crypto Crate"
lemma_allowlist = ["ext_encrypt"]
"#,
    );
    let cfg = load_config(&toml_path, &test_repo_root(), Some(tmp_out.path()))
        .expect("self-contained translation.toml should parse and infer package name");
    assert_eq!(cfg.crate_dir, normalize_path(tmp_crate.path()));
    assert_eq!(cfg.crates, vec!["external_crypto_crate".to_string()]);
    assert_eq!(cfg.title, "External Crypto Crate");
    assert_eq!(
        cfg.targets[0].lean_file,
        normalize_path(&tmp_out.path().join("Generated/ExtCrypto.lean"))
    );
    assert_eq!(
        cfg.obj_file,
        normalize_path(&tmp_out.path().join("Generated/ExtCryptoObj.lean"))
    );
    assert_eq!(
        cfg.data_bin_file(),
        normalize_path(&tmp_out.path().join("Generated/ExtCryptoObj.data.bin"))
    );
}

#[test]
fn multi_crate_config_names_each_object() {
    let (_tmp, toml_path) = write_tmp_crate(
        "multi-crate-demo",
        r#"
crates = ["multi-crate-demo", "helper_crate"]
obj_name = "demo"

[[targets]]
name = "demo"
lean_file = "Generated/Demo.lean"
prog_name = "demoBin"
title = "Demo"
lemma_allowlist = ["demo_entry"]
"#,
    );
    let cfg = load_config(&toml_path, &test_repo_root(), None).unwrap();
    assert_eq!(
        cfg.crates,
        vec!["multi_crate_demo".to_string(), "helper_crate".to_string()]
    );
    assert_eq!(cfg.obj_def_name("helper_crate"), "demoHelperCrateObj");
    assert_eq!(cfg.image_def_name(), "demoImage");
}

#[test]
fn rejects_removed_config_fields() {
    for removed in [
        "symbol_allowlist = [\"x\"]",
        "stub_crates = [\"aes-gcm\"]",
        "stub_external_symbols = true",
        "link_workspace_crates = true",
        "link_crates = [\"helper\"]",
        "emit_obj_dump = true",
        "base_addr = \"0x0\"",
        "rodata_addr = \"0x0\"",
        "words_def = true",
        "target_crate = \"x\"",
    ] {
        let (_tmp, toml_path) = write_tmp_crate(
            "old-crate",
            &format!(
                r#"
obj_name = "old"

[[targets]]
name = "old"
lean_file = "Generated/Old.lean"
prog_name = "oldBin"
title = "Old"
lemma_allowlist = ["f"]
{removed}
"#
            ),
        );
        let err = load_config(&toml_path, &test_repo_root(), None)
            .expect_err("removed field must be rejected");
        assert!(
            format!("{err:#}").contains("unknown field"),
            "{removed}: {err:#}"
        );
    }
}

#[test]
fn rejects_bad_obj_name_and_duplicate_crates() {
    let (_tmp, bad_name) = write_tmp_crate(
        "c",
        r#"
obj_name = "1bad-name"
[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#,
    );
    let err = load_config(&bad_name, &test_repo_root(), None).unwrap_err();
    assert!(err.to_string().contains("not a simple Lean identifier"));

    let (_tmp2, dup) = write_tmp_crate(
        "c",
        r#"
obj_name = "ok"
crates = ["a-b", "a_b"]
[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#,
    );
    let err = load_config(&dup, &test_repo_root(), None).unwrap_err();
    assert!(err.to_string().contains("duplicate crate `a_b`"));
}

#[test]
fn rustflags_config() {
    const TARGET: &str = r#"
[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#;
    let cfg_with = |flags: &str| format!("obj_name = \"ok\"\nrustflags = {flags}\n{TARGET}");
    let (_t, ok) = write_tmp_crate("c", &cfg_with(r#"["--cfg", 'k="v"']"#));
    let cfg = load_config(&ok, &test_repo_root(), None).unwrap();
    assert_eq!(cfg.rustflags, ["--cfg", "k=\"v\""]);
    let (_t, none) = write_tmp_crate("c", &format!("obj_name = \"ok\"\n{TARGET}"));
    assert!(
        load_config(&none, &test_repo_root(), None)
            .unwrap()
            .rustflags
            .is_empty()
    );

    for (what, flags) in [
        ("flag with space", r#"["-C opt-level=3"]"#),
        ("empty flag", r#"[""]"#),
    ] {
        let (_t, path) = write_tmp_crate("c", &cfg_with(flags));
        let err = load_config(&path, &test_repo_root(), None).unwrap_err();
        assert!(
            format!("{err:#}").contains("without whitespace"),
            "{what}: {err:#}"
        );
    }
}

#[test]
fn reproducible_paths() {
    use crate::untrusted_driver::{
        check_no_host_paths, host_path_check_dirs, path_remaps, rustc_commit_hash,
    };
    let ver = "rustc 1.98.1 (48a229cea 2026-09-21)\nbinary: rustc\n\
                   commit-hash: 48a229ceaefd4985c50990b14116b6d856af0985\ncommit-date: 2026-09-21";
    let commit = rustc_commit_hash(ver).unwrap();
    assert_eq!(commit, "48a229ceaefd4985c50990b14116b6d856af0985");
    assert!(rustc_commit_hash("rustc 1.98.1\ncommit-hash: unknown\n").is_err());
    assert!(rustc_commit_hash("rustc 1.98.1\n").is_err());
    assert!(rustc_commit_hash("commit-hash: bad=hash\n").is_err());

    // A symlinked CARGO_HOME, target dir and sysroot: both spellings are remapped, each as given
    // then canonicalized, in a fixed order of kinds (not by length, which differs between hosts).
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path().canonicalize().unwrap();
    let real_home = root.join("real-cargo-home");
    // Leave `git/checkouts` and `lib/rustlib/src/rust` non-existent on disk to verify
    // canonicalization via existing ancestor (e.g. when `rust-src` is not installed).
    fs::create_dir_all(real_home.join("registry/src")).unwrap();
    let home = root.join("h");
    std::os::unix::fs::symlink(&real_home, &home).unwrap();
    let real_target = root.join("checkout-with-a-long-name/target");
    fs::create_dir_all(&real_target).unwrap();
    let target = root.join("t");
    std::os::unix::fs::symlink(&real_target, &target).unwrap();
    let real_sysroot = root.join("toolchains/1.98.1-x86_64-unknown-linux-gnu");
    fs::create_dir_all(real_sysroot.join("lib/rustlib")).unwrap();
    let sysroot = root.join("s");
    std::os::unix::fs::symlink(&real_sysroot, &sysroot).unwrap();
    let s = |p: &Path| p.to_str().unwrap().to_string();
    let remaps = path_remaps(&target, &home, &sysroot, commit, None).unwrap();
    let link_reg = s(&home.join("registry/src"));
    let real_reg = s(&real_home.join("registry/src"));
    let link_git = s(&home.join("git/checkouts"));
    let real_git = s(&real_home.join("git/checkouts"));
    let link_src = s(&sysroot.join("lib/rustlib/src/rust"));
    let real_src = s(&real_sysroot.join("lib/rustlib/src/rust"));
    let rustc_to = format!("/rustc/{commit}");
    let flag = |d: &str, to: &str| (d.to_string(), format!("--remap-path-prefix={d}={to}"));
    assert_eq!(
        remaps,
        [
            flag(&link_reg, "/cargo-registry"),
            flag(&real_reg, "/cargo-registry"),
            flag(&s(&target), "/cargo-target"),
            flag(&s(&real_target), "/cargo-target"),
            flag(&link_git, "/cargo-git"),
            flag(&real_git, "/cargo-git"),
            flag(&link_src, &rustc_to),
            flag(&real_src, &rustc_to),
        ]
    );
    // The order does not depend on the directories' lengths: the same kinds at other lengths.
    let other = root.join("another-much-longer-host-directory-name");
    let (o_home, o_target, o_sysroot) = (other.join("h"), root.join("t2"), other.join("s"));
    let kinds = |r: &[(String, String)]| -> Vec<String> {
        r.iter()
            .map(|(_, f)| f.rsplit_once('=').unwrap().1.to_string())
            .collect()
    };
    assert_eq!(
        kinds(&path_remaps(&o_target, &o_home, &o_sysroot, commit, None).unwrap()),
        [
            "/cargo-registry",
            "/cargo-target",
            "/cargo-git",
            rustc_to.as_str()
        ]
    );
    // Without symlinks, one spelling each.
    assert_eq!(
        path_remaps(&real_target, &real_home, &real_sysroot, commit, None)
            .unwrap()
            .len(),
        4
    );
    assert!(
        path_remaps(
            Path::new("/has space/target"),
            &home,
            &sysroot,
            commit,
            None
        )
        .is_err()
    );
    assert!(
        path_remaps(
            &target,
            Path::new("/has space/.cargo"),
            &sysroot,
            commit,
            None
        )
        .is_err()
    );
    assert!(
        path_remaps(
            &target,
            &home,
            Path::new("/has space/sysroot"),
            commit,
            None
        )
        .is_err()
    );
    assert!(path_remaps(Path::new("/has=eq/target"), &home, &sysroot, commit, None).is_err());
    assert!(path_remaps(&target, Path::new("/has=eq/.cargo"), &sysroot, commit, None).is_err());
    assert!(path_remaps(&target, &home, Path::new("/has=eq/sysroot"), commit, None).is_err());
    assert!(path_remaps(&target, &home, &sysroot, "", None).is_err());
    assert!(path_remaps(&target, &home, &sysroot, "bad=commit", None).is_err());

    // Nested directories: the longer (more specific) prefix comes last, so rustc applies it.
    let nested = path_remaps(
        &real_home.join("git"),
        &real_home,
        &real_sysroot,
        commit,
        None,
    )
    .unwrap();
    assert!(
        nested
            .iter()
            .position(|x| x == &flag(&s(&real_home.join("git")), "/cargo-target"))
            < nested
                .iter()
                .position(|x| x == &flag(&real_git, "/cargo-git"))
    );

    // The check covers the remapped dirs (including <sysroot>/lib/rustlib/src/rust), the
    // sysroot itself, the crate dir and the upstream source.
    let crate_dir = root.join("checkout-with-a-long-name");
    let upstream = root.join("upstream-src");
    fs::create_dir_all(&upstream).unwrap();
    let check = host_path_check_dirs(&remaps, &sysroot, &crate_dir, Some(&upstream));
    assert!(
        check.contains(&s(&sysroot))
            && check.contains(&s(&real_sysroot))
            && check.contains(&link_src)
            && check.contains(&real_src)
            && check.contains(&s(&crate_dir))
            && check.contains(&s(&upstream))
    );
    for leaked in [
        format!("xx{real_reg}/index.crates.io-x/hkdf-0.13.0/src/hmac_impl.rs\0"),
        format!("xx{}/out/signal.proto.wire.rs\0", s(&real_target)),
        format!("xx{real_git}/spqr-b58d/06959b4/src/lib.rs\0"),
        format!("xx{real_src}/library/core/src/slice/index.rs\0"),
        format!(
            "xx{}/lib/rustlib/aarch64-unknown-linux-gnu/lib/libcore.rlib\0",
            s(&real_sysroot)
        ),
        format!("xx{}/vendor/x/src/lib.rs\0", s(&crate_dir)),
        format!("xx{}/rust/protocol/src/lib.rs\0", s(&upstream)),
    ] {
        assert!(
            check_no_host_paths("o", leaked.as_bytes(), &check).is_err(),
            "{leaked}"
        );
    }
    let clean = format!(
        "xx/cargo-registry/index.crates.io-x/hkdf-0.13.0/src/hmac_impl.rs\0\
             /cargo-target/out/a.rs\0/cargo-git/spqr/src/lib.rs\0\
             {rustc_to}/library/core/src/slice/index.rs\0vendor/x/src/lib.rs\0"
    );
    assert!(check_no_host_paths("o", clean.as_bytes(), &check).is_ok());
    // Relative sysroot/crate dirs are only checked in their canonical (absolute) spelling.
    let rel = host_path_check_dirs(&[], Path::new("."), Path::new("."), None);
    assert_eq!(rel, [s(&Path::new(".").canonicalize().unwrap())]);
}

#[test]
fn upstream_source_remap() {
    use crate::untrusted_driver::{path_remaps, upstream_remap_target};
    let commit = "48a229ceaefd4985c50990b14116b6d856af0985";
    let up_a = "ba133bd3457f556fbf56db0a5ab985de0af79da6";
    let up_b = "0123456789abcdef0123456789abcdef01234567";
    let to_a = upstream_remap_target("widget", up_a).unwrap();
    let to_b = upstream_remap_target("widget", up_b).unwrap();
    assert_eq!(to_a, format!("/upstream/widget/{up_a}"));
    for (name, c) in [
        ("", up_a),
        ("a b", up_a),
        ("a=b", up_a),
        ("a/b", up_a),
        ("widget", ""),
        ("widget", "HEAD"),
        ("widget", "ab=cd"),
    ] {
        assert!(upstream_remap_target(name, c).is_err(), "`{name}` `{c}`");
    }

    // A crate whose `vendor/widget` symlink points to one of two upstream trees.
    let tmp = tempfile::tempdir().unwrap();
    let root = tmp.path().canonicalize().unwrap();
    let home = root.join("cargo-home");
    let target = root.join("crate/target");
    let sysroot = root.join("sysroot");
    let tree_a = root.join("trees/widget-a");
    let tree_b = root.join("trees/widget-b");
    fs::create_dir_all(&tree_a).unwrap();
    fs::create_dir_all(&tree_b).unwrap();
    fs::create_dir_all(root.join("crate/vendor")).unwrap();
    let link = root.join("crate/vendor/widget");
    std::os::unix::fs::symlink(&tree_a, &link).unwrap();
    let flags = |up: Option<(&Path, &str)>| -> Vec<String> {
        path_remaps(&target, &home, &sysroot, commit, up)
            .unwrap()
            .into_iter()
            .map(|(_, f)| f)
            .collect()
    };
    let flag = |d: &Path, to: &str| format!("--remap-path-prefix={}={to}", d.to_str().unwrap());

    // Both spellings of the upstream directory are added to the fixed remaps.
    let base = flags(None);
    let with_a = flags(Some((&link, &to_a)));
    assert_eq!(with_a.len(), base.len() + 2, "{with_a:?}");
    assert!(base.iter().all(|f| with_a.contains(f)));
    assert!(with_a.contains(&flag(&link, &to_a)), "{with_a:?}");
    assert!(with_a.contains(&flag(&tree_a, &to_a)), "{with_a:?}");

    // Retargeting the symlink, or another upstream commit in the same directory, changes
    // RUSTFLAGS, so cargo rebuilds every unit instead of trusting source mtimes.
    fs::remove_file(&link).unwrap();
    std::os::unix::fs::symlink(&tree_b, &link).unwrap();
    let retargeted = flags(Some((&link, &to_a)));
    assert_ne!(retargeted, with_a);
    assert!(retargeted.contains(&flag(&tree_b, &to_a)), "{retargeted:?}");
    assert_ne!(flags(Some((&link, &to_b))), retargeted);

    // An upstream checkout nested in a remapped directory: its own (longer) prefix comes last,
    // so rustc applies it.
    let nested = home.join("git/checkouts/widget-1234");
    fs::create_dir_all(&nested).unwrap();
    let nested_flags = flags(Some((&nested, &to_a)));
    let pos = |f: &str| nested_flags.iter().position(|x| x == f).unwrap();
    assert!(pos(&flag(&home.join("git/checkouts"), "/cargo-git")) < pos(&flag(&nested, &to_a)));

    // A relative spelling is not remapped: it could match the relative source paths of path
    // packages below the workspace root. Unusable paths are rejected.
    let rel = path_remaps(
        &target,
        &home,
        &sysroot,
        commit,
        Some((Path::new("no-such-dir/widget"), &to_a)),
    )
    .unwrap();
    assert!(
        rel.iter().all(|(d, _)| Path::new(d).is_absolute()),
        "{rel:?}"
    );
    assert_eq!(rel.len(), base.len());
    for bad in ["/has space/widget", "/has=eq/widget"] {
        assert!(
            path_remaps(
                &target,
                &home,
                &sysroot,
                commit,
                Some((Path::new(bad), &to_a))
            )
            .is_err(),
            "{bad}"
        );
    }

    // A target dir inside the upstream checkout, or the other way round: the nested directory
    // comes last whichever is longer, and unrelated directories keep their fixed order.
    let up = root.join("up");
    let kinds = |r: Vec<(String, String)>| -> Vec<String> {
        r.into_iter()
            .map(|(_, f)| f.rsplit_once('=').unwrap().1.to_string())
            .collect()
    };
    let rustc_to = format!("/rustc/{commit}");
    assert_eq!(
        kinds(
            path_remaps(
                &up.join("target"),
                &home,
                &sysroot,
                commit,
                Some((&up, &to_a))
            )
            .unwrap()
        ),
        [
            "/cargo-registry",
            "/cargo-git",
            rustc_to.as_str(),
            to_a.as_str(),
            "/cargo-target"
        ]
    );
    let t = root.join("t");
    assert_eq!(
        kinds(path_remaps(&t, &home, &sysroot, commit, Some((&t.join("up"), &to_a))).unwrap()),
        [
            "/cargo-registry",
            "/cargo-target",
            "/cargo-git",
            rustc_to.as_str(),
            to_a.as_str()
        ]
    );
}

#[test]
fn host_independent_provenance_paths() {
    use crate::untrusted_driver::{Toolchain, checkout_root, crate_dir_display};
    // Commands show the longest aliased host path first, whatever order the aliases were added
    // in: an upstream checkout below the crate's repository shows as its own alias.
    let argv = [
        "--remap-path-prefix=/w/super/c/vendor/up=/upstream/up/0123",
        "--remap-path-prefix=/w/super/c/target=/cargo-target",
    ];
    let expected = "--remap-path-prefix=$UP_SRC=/upstream/up/0123 \
                    --remap-path-prefix=$CRATE_REPO/c/target=/cargo-target";
    for aliases in [
        [
            ("/w/super", "$CRATE_REPO"),
            ("/w/super/c/vendor/up", "$UP_SRC"),
        ],
        [
            ("/w/super/c/vendor/up", "$UP_SRC"),
            ("/w/super", "$CRATE_REPO"),
        ],
    ] {
        let mut tc = Toolchain {
            repo_root: PathBuf::from("/w/super/engine"),
            rustc_version: String::new(),
            path_aliases: vec![],
        };
        for (real, alias) in aliases {
            tc.add_alias(Path::new(real), alias);
        }
        assert_eq!(tc.format_cmd(&argv, &[]), expected);
    }

    // The crate directory is shown relative to this repository, else to its own checkout.
    let tmp = tempfile::tempdir().unwrap();
    let sup = tmp.path().canonicalize().unwrap().join("super");
    let engine = sup.join("engine");
    fs::create_dir_all(sup.join(".git")).unwrap();
    fs::create_dir_all(engine.join("examples/demo")).unwrap();
    fs::write(engine.join(".git"), "gitdir: ../.git/modules/engine\n").unwrap();
    let outside = sup.join("third_party/lib/lib-session");
    fs::create_dir_all(&outside).unwrap();
    assert_eq!(checkout_root(&outside), Some(sup.as_path()));
    assert_eq!(
        checkout_root(&engine.join("examples/demo")),
        Some(engine.as_path())
    );
    assert_eq!(
        crate_dir_display(&engine, &engine.join("examples/demo")),
        "examples/demo"
    );
    assert_eq!(
        crate_dir_display(&engine, &outside),
        "third_party/lib/lib-session"
    );
    assert_eq!(crate_dir_display(&engine, &sup), ".");
    let no_git = tmp.path().canonicalize().unwrap().join("plain/crate");
    fs::create_dir_all(&no_git).unwrap();
    if checkout_root(&no_git).is_none() {
        assert_eq!(
            crate_dir_display(&engine, &no_git),
            no_git.to_str().unwrap()
        );
    }
}

#[test]
fn native_objects_config() {
    const TARGET: &str = r#"
[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#;
    let native = |compiler: &str, obj: &str| {
        format!("obj_name = \"ok\"\n{compiler}\n[[native_objects]]\n{obj}\n{TARGET}")
    };
    let good_obj = r#"name = "shim"
source = "csrc/shim.c"
include_dirs = ["csrc/include"]
defines = ["FOO", "BAR=1"]"#;
    let compiler = "[native_compiler]\nzig_version = \"0.16.0\"";
    let c_dir = tempfile::tempdir().unwrap();
    let ok = c_dir.path().join("translation.toml");
    fs::write(&ok, native(compiler, good_obj)).unwrap();
    let cfg = load_config(&ok, &test_repo_root(), None).unwrap();
    assert!(cfg.crates.is_empty());
    assert_eq!(cfg.object_names(), ["shim"]);
    assert_eq!(cfg.native_compiler.as_ref().unwrap().zig_version, "0.16.0");
    let args =
        crate::untrusted_driver::native_cc_args_with_flags(&cfg.native_objects[0], &[], "shim.o");
    assert_eq!(args[0], "cc");
    assert!(
        args.windows(2)
            .any(|w| w == ["-target", "aarch64-linux-musl"])
    );
    assert!(args.contains(&"-fno-pic".to_string()));
    assert_eq!(
        args[args.len() - 7..],
        [
            "-Icsrc/include",
            "-DFOO",
            "-DBAR=1",
            "-c",
            "csrc/shim.c",
            "-o",
            "shim.o"
        ]
    );

    let cases: &[(&str, String, &str)] = &[
        (
            "missing compiler",
            native("", good_obj),
            "[native_compiler]",
        ),
        (
            "compiler without objects",
            format!("obj_name = \"ok\"\n{compiler}\n{TARGET}"),
            "[native_compiler]",
        ),
        (
            "bad name",
            native(compiler, &good_obj.replace("\"shim\"", "\"a-b\"")),
            "not a C identifier",
        ),
        (
            "roots rejected",
            native(compiler, &format!("{good_obj}\nroots = [\"f\"]")),
            "unknown field `roots`",
        ),
        (
            "absolute source",
            native(
                compiler,
                &good_obj.replace("\"csrc/shim.c\"", "\"/etc/shim.c\""),
            ),
            "must be non-empty and relative",
        ),
        (
            "empty source",
            native(compiler, &good_obj.replace("\"csrc/shim.c\"", "\"\"")),
            "must be non-empty and relative",
        ),
        (
            "bad define",
            native(compiler, &good_obj.replace("\"FOO\"", "\"-O0\"")),
            "bad define",
        ),
        (
            "digit-leading define",
            native(compiler, &good_obj.replace("\"FOO\"", "\"0FOO=1\"")),
            "bad define",
        ),
        (
            "whitespace in define value",
            native(compiler, &good_obj.replace("\"BAR=1\"", "\"BAR=1 2\"")),
            "bad define",
        ),
        (
            "duplicate native object name",
            format!(
                "obj_name = \"ok\"\n{compiler}\n[[native_objects]]\n{good_obj}\n[[native_objects]]\n{good_obj}\n{TARGET}"
            ),
            "duplicate object name `shim`",
        ),
        (
            "empty crates in mixed Rust+C config",
            format!("crates = []\n{}", native(compiler, good_obj)),
            "defines no crates",
        ),
        (
            "empty crates in pure-Rust config",
            format!("crates = []\nobj_name = \"ok\"\n{TARGET}"),
            "defines no crates",
        ),
        (
            "bad sysroot object name",
            format!(
                "crates = [\"c\"]\nobj_name = \"ok\"\n[[sysroot_objects]]\ncrate = \"core\"\nname = \"bad-name\"\nroots = [\"f\"]\n{TARGET}"
            ),
            "not a C identifier",
        ),
        (
            "duplicate sysroot object names",
            format!(
                "crates = [\"c\"]\nobj_name = \"ok\"\n[[sysroot_objects]]\ncrate = \"core\"\nname = \"dup_s\"\nroots = [\"f\"]\n[[sysroot_objects]]\ncrate = \"alloc\"\nname = \"dup_s\"\nroots = [\"g\"]\n{TARGET}"
            ),
            "duplicate object name `dup_s`",
        ),
    ];
    for (what, toml, expect) in cases {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("translation.toml");
        fs::write(&path, toml).unwrap();
        let err = load_config(&path, &test_repo_root(), None).expect_err(what);
        assert!(format!("{err:#}").contains(expect), "{what}: {err:#}");
    }

    // Reject `[[native_objects]]` in a directory that contains a `Cargo.toml` unless `crates = [...]` is explicit.
    let (_t, mixed_cargo) = write_tmp_crate("c", &native(compiler, good_obj));
    let err = load_config(&mixed_cargo, &test_repo_root(), None).unwrap_err();
    assert!(
        format!("{err:#}").contains("cannot combine Rust crates"),
        "{err:#}"
    );

    // Explicit `crates = [...]` may be combined with C inputs and multi-entry `[[sysroot_objects]]`,
    // ordered `crates` -> C inputs -> `sysroot_objects`.
    let (_t2, explicit_mixed) = write_tmp_crate(
        "c",
        &format!(
            "crates = [\"c\"]\n{}\n[[sysroot_objects]]\ncrate = \"compiler_builtins\"\nname = \"cb_a\"\nroots = [\"__aarch64_cas4_acq\"]\n[[sysroot_objects]]\ncrate = \"compiler_builtins\"\nname = \"cb_b\"\nroots = [\"__aarch64_have_lse_atomics\"]\n",
            native(compiler, good_obj)
        ),
    );
    let mixed_cfg = load_config(&explicit_mixed, &test_repo_root(), None).unwrap();
    assert_eq!(mixed_cfg.crates, ["c"]);
    assert_eq!(mixed_cfg.object_names(), ["c", "shim", "cb_a", "cb_b"]);
}

#[test]
fn cli_accepts_multiple_configs_and_out_dir() {
    let cli = Cli::try_parse_from([
        "rust-obj2lean",
        "--config",
        "Implementation/examples/translation.toml",
        "--config",
        "Implementation/my_lib/translation.toml",
        "--out-dir",
        "/tmp/out",
        "--only",
        "functions",
        "--check",
    ])
    .expect("CLI flags should parse");
    assert_eq!(cli.config.len(), 2);
    assert_eq!(cli.out_dir, Some(PathBuf::from("/tmp/out")));
    assert_eq!(cli.only, vec!["functions".to_string()]);
    assert!(cli.check);
}

#[test]
fn write_or_check_reports_changes() {
    let tmp = tempfile::tempdir().unwrap();
    let file = GeneratedFile {
        path: tmp.path().join("sub/A.lean"),
        contents: b"hello\n".to_vec(),
        text: true,
    };
    assert!(!write_or_check(&file, tmp.path(), true).unwrap());
    assert!(write_or_check(&file, tmp.path(), false).unwrap());
    assert_eq!(fs::read(&file.path).unwrap(), b"hello\n");
    assert!(write_or_check(&file, tmp.path(), true).unwrap());
}

#[test]
fn write_or_check_unlinks_hardlink_instead_of_truncating_shared_inode() {
    use std::os::unix::fs::MetadataExt;

    let tmp = tempfile::tempdir().unwrap();
    let main_dir = tmp.path().join("main");
    let wt_dir = tmp.path().join("worktree");
    fs::create_dir_all(&main_dir).unwrap();
    fs::create_dir_all(&wt_dir).unwrap();

    let main_file = main_dir.join("AlphaFns.lean");
    let wt_file = wt_dir.join("AlphaFns.lean");
    fs::write(&main_file, b"original-v1\n").unwrap();
    fs::hard_link(&main_file, &wt_file).unwrap();
    assert_eq!(
        fs::metadata(&main_file).unwrap().ino(),
        fs::metadata(&wt_file).unwrap().ino()
    );
    assert_eq!(fs::metadata(&main_file).unwrap().nlink(), 2);

    let updated = GeneratedFile {
        path: wt_file.clone(),
        contents: b"updated-v2-in-worktree\n".to_vec(),
        text: true,
    };
    assert!(write_or_check(&updated, &wt_dir, false).unwrap());

    assert_eq!(fs::read(&wt_file).unwrap(), b"updated-v2-in-worktree\n");
    assert_eq!(fs::read(&main_file).unwrap(), b"original-v1\n");
    assert_ne!(
        fs::metadata(&main_file).unwrap().ino(),
        fs::metadata(&wt_file).unwrap().ino()
    );
    assert_eq!(fs::metadata(&main_file).unwrap().nlink(), 1);
    assert_eq!(fs::metadata(&wt_file).unwrap().nlink(), 1);
    for entry in fs::read_dir(&wt_dir).unwrap() {
        let name = entry.unwrap().file_name().into_string().unwrap();
        assert!(!name.contains(".tmp."), "stray temp file left behind: {name}");
    }
}

#[test]
fn lakefile_ensure_rust_exports_atomic_stamps_and_imported_outputs() {
    let repo_root = test_repo_root();
    let mut combined_lakefiles = fs::read_to_string(repo_root.join("lakefile.lean")).unwrap();
    let lake_exports_path = repo_root.join("scripts/LakeExports.lean");
    if lake_exports_path.is_file() {
        combined_lakefiles.push('\n');
        combined_lakefiles.push_str(&fs::read_to_string(&lake_exports_path).unwrap());
    }
    let vl_lf = repo_root.join("VerifiedLibraries/lakefile.lean");
    if vl_lf.is_file() {
        combined_lakefiles.push('\n');
        combined_lakefiles.push_str(&fs::read_to_string(&vl_lf).unwrap());
    }
    let cs_root = repo_root.join("CaseStudies");
    if let Ok(entries) = fs::read_dir(&cs_root) {
        for entry in entries.flatten() {
            let lf = entry.path().join("lakefile.lean");
            if lf.is_file() {
                combined_lakefiles.push('\n');
                combined_lakefiles.push_str(&fs::read_to_string(&lf).unwrap());
            }
        }
    }

    // 1. `writeFileAtomic` writes to a temp file and renames it over the target.
    let (_, after_atomic) = combined_lakefiles
        .split_once("def writeFileAtomic")
        .expect("lakefile.lean / scripts/LakeExports.lean must define writeFileAtomic");
    let (atomic_body, _) = after_atomic
        .split_once("def generatedImportsOfFile")
        .expect("lakefile.lean / scripts/LakeExports.lean must define generatedImportsOfFile after writeFileAtomic");
    assert!(
        atomic_body.contains(".tmp.") && atomic_body.contains("IO.FS.rename"),
        "writeFileAtomic must write to a .tmp. file and rename over target"
    );

    // 2. `ensureRustExports` never uses raw `IO.FS.writeFile` (which truncates hardlinked stamps
    //    in place) and checks `generatedImportsOfFile` so missing `*Shard*.lean` imports fail closed.
    let (_, after_ensure) = combined_lakefiles
        .split_once("def ensureRustExports")
        .expect("lakefile.lean / scripts/LakeExports.lean must define ensureRustExports");
    let (ensure_body, _) = after_ensure
        .split_once("partial def sanitizePackageBuildDir")
        .expect("sanitizePackageBuildDir must follow ensureRustExports");
    assert!(
        !ensure_body.contains("IO.FS.writeFile"),
        "ensureRustExports must use writeFileAtomic instead of IO.FS.writeFile"
    );
    assert!(
        ensure_body.contains("writeFileAtomic (buildDir /")
            && ensure_body.contains("writeFileAtomic (genDir /")
            && ensure_body.contains("writeFileAtomic buildStamp")
            && ensure_body.contains("writeFileAtomic genStamp")
            && ensure_body.contains("writeFileAtomic genInputsStamp"),
        "ensureRustExports must write all buildDir and genDir stamps via writeFileAtomic"
    );
    assert!(
        ensure_body.matches("generatedImportsOfFile").count() >= 3,
        "ensureRustExports must check generatedImportsOfFile in allExist, error cleanup, and post-export verification"
    );

    // 3. Every configured target's `placed.lib_file` (or `lean_file` when `[placed]` is absent)
    //    is covered in `exportTargetSpecs` (directly or via `shardOutputs`). Configs are
    //    discovered on disk so partial exports that drop campaigns still check what remains.
    let configs = load_configs(
        &discover_repo_config_paths(&["CaseStudies"]),
        &repo_root,
        None,
    )
    .unwrap();
    for cfg in &configs {
        if let Some(placed) = &cfg.placed {
            let rel = placed
                .lib_file
                .strip_prefix(&repo_root)
                .unwrap_or(&placed.lib_file)
                .to_string_lossy();
            let rel_norm = if let Some(rest) = rel.strip_prefix("CaseStudies/")
                && let Some((_lib, after_lib)) = rest.split_once('/')
            {
                after_lib.to_string()
            } else {
                rel.to_string()
            };
            if placed.placed_shards > 1 {
                // Sharded placed library: the barrel and every shard via `shardOutputs`.
                let stem = rel_norm.strip_suffix(".lean").unwrap_or(&rel_norm);
                assert!(
                    combined_lakefiles
                        .contains(&format!("shardOutputs \"{stem}\" {}", placed.placed_shards)),
                    "placed config `{}` with `placed_shards = {}` needs \
                     `shardOutputs \"{stem}\" {}` in lakefile.lean exportTargetSpecs",
                    cfg.config_rel,
                    placed.placed_shards,
                    placed.placed_shards
                );
                continue;
            }
            assert!(
                combined_lakefiles.contains(&format!("\"{rel_norm}\"")),
                "placed config `{}` output `{rel_norm}` is missing from lakefile.lean exportTargetSpecs",
                cfg.config_rel
            );
            continue;
        }
        for target in &cfg.targets {
            let rel = target
                .lean_file
                .strip_prefix(&repo_root)
                .unwrap_or(&target.lean_file)
                .to_string_lossy();
            let rel_norm = if let Some(rest) = rel.strip_prefix("CaseStudies/")
                && let Some((_lib, after_lib)) = rest.split_once('/')
            {
                after_lib.to_string()
            } else {
                rel.to_string()
            };
            let stem = rel_norm.strip_suffix(".lean").unwrap_or(&rel_norm);
            assert!(
                combined_lakefiles.contains(&format!("\"{rel_norm}\""))
                    || combined_lakefiles.contains(&format!("shardOutputs \"{stem}\"")),
                "target `{}` output `{rel_norm}` is missing from lakefile.lean exportTargetSpecs",
                target.name
            );
        }
    }
}

#[test]
fn print_cflags_cli_and_verification_flags() {
    let cli_sub = Cli::try_parse_from(["rust-obj2lean", "print-cflags"]).unwrap();
    assert!(matches!(cli_sub.command, Some(CommandName::PrintCflags)));

    let cli_alias = Cli::try_parse_from(["rust-obj2lean", "cflags"]).unwrap();
    assert!(matches!(cli_alias.command, Some(CommandName::PrintCflags)));

    let cli_flag = Cli::try_parse_from(["rust-obj2lean", "--print-cflags"]).unwrap();
    assert!(cli_flag.print_cflags);

    let flags = native_cflags_string(&["-Iinclude".into(), "-DHAVE_CONFIG_H".into()]);
    assert!(flags.contains("-O2"), "{flags}");
    assert!(flags.contains("-fno-jump-tables"), "{flags}");
    assert!(flags.contains("-fno-common"), "{flags}");
    assert!(flags.contains("-fno-vectorize"), "{flags}");
    assert!(flags.contains("-fno-slp-vectorize"), "{flags}");
    assert!(flags.ends_with("-Iinclude -DHAVE_CONFIG_H"), "{flags}");

    // Optimization-level overrides in `c_flags` / `[[native_objects]].c_flags` are rejected.
    const TARGET: &str = "[[targets]]\nname = \"t\"\nlean_file = \"G/T.lean\"\nprog_name = \"p\"\ntitle = \"T\"\nlemma_allowlist = []\n";
    let dir = tempfile::tempdir().unwrap();
    let cfg_path = dir.path().join("translation.toml");
    for bad in [
        "-O0",
        "-O1",
        "-Os",
        "-Oz",
        "-Og",
        "-Ofast",
        "-O",
        "--optimize",
        "--optimize=1",
        "-fno-inline -O0",
    ] {
        let top_toml = format!(
            "obj_name = \"ok\"\nc_flags = [{bad:?}]\n[native_compiler]\nzig_version = \"0.16.0\"\n\
             [[native_objects]]\nname = \"shim\"\nsource = \"csrc/shim.c\"\n{TARGET}"
        );
        fs::write(&cfg_path, &top_toml).unwrap();
        let err = load_config(&cfg_path, &test_repo_root(), None).unwrap_err();
        assert!(
            format!("{err:#}").contains("overrides `-O2` optimization level"),
            "top-level {bad}: {err:#}"
        );

        let obj_toml = format!(
            "obj_name = \"ok\"\n[native_compiler]\nzig_version = \"0.16.0\"\n\
             [[native_objects]]\nname = \"shim\"\nsource = \"csrc/shim.c\"\nc_flags = [{bad:?}]\n{TARGET}"
        );
        fs::write(&cfg_path, &obj_toml).unwrap();
        let err = load_config(&cfg_path, &test_repo_root(), None).unwrap_err();
        assert!(
            format!("{err:#}").contains("overrides `-O2` optimization level"),
            "native_objects {bad}: {err:#}"
        );
    }
    for good in ["-O2", "-O3"] {
        let ok_toml = format!(
            "obj_name = \"ok\"\nc_flags = [{good:?}, \"-fno-inline\"]\n[native_compiler]\n\
             zig_version = \"0.16.0\"\n[[native_objects]]\nname = \"shim\"\n\
             source = \"csrc/shim.c\"\nc_flags = [{good:?}]\n{TARGET}"
        );
        fs::write(&cfg_path, &ok_toml).unwrap();
        load_config(&cfg_path, &test_repo_root(), None).unwrap();
    }

    // `name_selected` does not truncate Rust slice/array types (`<impl [T]>`) and
    // matches unnamespaced leaf names on local-suffixed symbols.
    let pat_impl = [regex::Regex::new("^(?:core::slice::<impl)$").unwrap()];
    assert!(!crate::untrusted_lemmas::name_selected(
        "core::slice::<impl [T]>::len",
        &pat_impl
    ));
    let pat_helper = [regex::Regex::new("^(?:helper)$").unwrap()];
    assert!(crate::untrusted_lemmas::name_selected(
        "my_crate::helper#1 [obj]",
        &pat_helper
    ));

    // Zero-sized data/tls `[[externs]]` entries are rejected by `load_config`.
    let dir = tempfile::tempdir().unwrap();
    let zero_toml = dir.path().join("translation.toml");
    fs::write(
        &zero_toml,
        r#"
obj_name = "ok"
c_objects = ["a.o"]
[[externs]]
name = "zero_data"
kind = { data = 0 }
[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#,
    )
    .unwrap();
    let err = load_config(&zero_toml, &test_repo_root(), None).unwrap_err();
    assert!(
        format!("{err:#}").contains("data/tls externs cannot have size 0"),
        "{err:#}"
    );
}

#[test]
fn c_library_archive_build_script_and_local_disambiguation() {
    if crate::untrusted_driver::find_zig_binary("test").is_err() {
        eprintln!("skipping: zig not available");
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    fs::create_dir_all(root.join("include")).unwrap();
    fs::create_dir_all(root.join("src")).unwrap();

    fs::write(
        root.join("include/demo.h"),
        "#pragma once\n\
             extern void *malloc(unsigned long);\n\
             extern void free(void *);\n\
             extern int ext_counter;\n\
             extern long ext_explicit[2];\n\
             int alpha_entry(int x);\n\
             int beta_entry(int x);\n\
             int gamma_entry(int x);\n",
    )
    .unwrap();

    // alpha.c: defines `static const int k_table[4]`, `static int helper(int)`,
    // two function-scoped `static int acc` variables, a tentative global `int g_tentative;`
    // (requires `-fno-common`), a dense switch statement (requires `-fno-jump-tables`),
    // and takes the addresses of external `malloc` and `free`.
    fs::write(
        root.join("src/alpha.c"),
        "#include \"demo.h\"\n\
             int g_tentative;\n\
             static const int k_table[4] = {10, 20, 30, 40};\n\
             struct AllocHooks { void *(*alloc_fn)(unsigned long); void (*free_fn)(void *); };\n\
             static const struct AllocHooks k_hooks = { malloc, free };\n\
             static __attribute__((noinline)) int helper(int x) {\n\
                 static int acc = 1;\n\
                 acc += k_table[x & 3];\n\
                 switch (x & 7) {\n\
                     case 0: return acc + 3;\n\
                     case 1: return acc + 7;\n\
                     case 2: return acc + 11;\n\
                     case 3: return acc + 19;\n\
                     case 4: return acc + 23;\n\
                     case 5: return acc + 29;\n\
                     case 6: return acc + 31;\n\
                     default: return acc + 37;\n\
                 }\n\
             }\n\
             int alpha_entry(int x) {\n\
                 static int acc = 5;\n\
                 const struct AllocHooks * volatile hp = &k_hooks;\n\
                 void *p = hp->alloc_fn(16);\n\
                 if (p) hp->free_fn(p);\n\
                 g_tentative += acc;\n\
                 return helper(x) * DEMO_SCALE + ext_counter + (int)ext_explicit[0];\n\
             }\n",
    )
    .unwrap();

    // beta.c: ALSO defines `static const int k_table[4]` and `static int helper(int)`
    // with the exact same local names as `alpha.c`.
    fs::write(
        root.join("src/beta.c"),
        "#include \"demo.h\"\n\
             static const int k_table[4] = {1, 2, 3, 4};\n\
             static __attribute__((noinline)) int helper(int x) {\n\
                 return k_table[x & 3] + x;\n\
             }\n\
             int beta_entry(int x) {\n\
                 return helper(x) + alpha_entry(x);\n\
             }\n",
    )
    .unwrap();

    // gamma.c: compiled to a standalone `.o` and loaded via `c_objects`.
    fs::write(
        root.join("src/gamma.c"),
        "#include \"demo.h\"\n\
             static __attribute__((noinline)) int helper(int x) { return x ^ 0x55; }\n\
             int gamma_entry(int x) { return helper(x) + beta_entry(x); }\n",
    )
    .unwrap();

    fs::write(
        root.join("build.sh"),
        "#!/bin/sh\n\
             set -eu\n\
             mkdir -p build\n\
             $CC $CFLAGS -c src/alpha.c -o build/alpha.o\n\
             $CC $CFLAGS -c src/beta.c -o build/beta.o\n\
             rm -f build/libdemo.a\n\
             $AR rcs build/libdemo.a build/alpha.o build/beta.o\n\
             $CC $CFLAGS -c src/gamma.c -o build/gamma.o\n",
    )
    .unwrap();

    let toml = r#"
obj_name = "cDemo"
obj_file = "Generated/CDemoObj.lean"
code_file = "Generated/CDemoCode.lean"
namespace_prefix = "CDemo"
title = "C Demo Archive"
build_script = "build.sh"
c_flags = ["-Iinclude", "-DDEMO_SCALE=2"]
c_archives = ["build/libdemo.a"]
c_objects = ["build/gamma.o"]

[[externs]]
name = "ext_explicit"
kind = { data = 16 }

[placed]
placed_only = true
multi = true
emit_extracted_obj = true
exports = ["alpha_entry", "beta_entry", "gamma_entry"]
"#;
    let toml_path = root.join("translation.toml");
    fs::write(&toml_path, toml).unwrap();

    let out_dir = root.join("out");
    let cfg = load_config(&toml_path, root, Some(&out_dir)).unwrap();
    let mut tc = Toolchain::new(root.to_path_buf()).unwrap();
    let ex = crate::untrusted_driver::extract(&cfg, &mut tc).unwrap();
    assert_eq!(
        ex.objects.iter().map(|o| o.name.as_str()).collect::<Vec<_>>(),
        vec!["gamma", "alpha", "beta"]
    );
    let cflags_prov = ex
        .provenance
        .iter()
        .find(|(k, _)| k == "Compile flags (CFLAGS)")
        .map(|(_, v)| v.as_str())
        .expect("missing CFLAGS provenance");
    assert!(
        cflags_prov.contains("-target aarch64-linux-musl -mcpu=generic -O2")
            && cflags_prov.contains("-Iinclude -DDEMO_SCALE=2"),
        "{cflags_prov}"
    );
    // Address-taken external functions `malloc` and `free` resolve as functions;
    // `ext_counter` is inferred (8 bytes) and `ext_explicit` uses configured size (16 bytes).
    let find_ext = |name: &str| {
        ex.externs
            .iter()
            .find(|e| e.name == name)
            .unwrap_or_else(|| panic!("missing extern `{name}`"))
    };
    assert_eq!(find_ext("malloc").kind, crate::trusted_common::ExternKind::Func);
    assert_eq!(find_ext("free").kind, crate::trusted_common::ExternKind::Func);
    assert_eq!(find_ext("ext_counter").kind, crate::trusted_common::ExternKind::Object);
    assert_eq!(find_ext("ext_counter").size, 8);
    assert_eq!(find_ext("ext_explicit").kind, crate::trusted_common::ExternKind::Object);
    assert_eq!(find_ext("ext_explicit").size, 16);

    let files = generate_config(&cfg, &mut tc).unwrap();

    let find_text = |suffix: &str| -> String {
        let f = files
            .iter()
            .find(|f| f.path.to_string_lossy().ends_with(suffix))
            .unwrap_or_else(|| panic!("missing generated file `{suffix}`"));
        String::from_utf8(f.contents.clone()).unwrap()
    };

    let placed_lean = find_text("CDemoPlacedObj.lean");
    assert!(
        placed_lean.contains("def cDemoMultiLib : Obj.MultiPlacedLib where"),
        "{placed_lean}"
    );
    for expected in [
        "\"alpha_entry\"",
        "\"beta_entry\"",
        "\"gamma_entry\"",
        "\"helper [alpha]\"",
        "\"helper [beta]\"",
        "\"helper [gamma]\"",
        "\"malloc\"",
        "\"free\"",
        "\"ext_counter\"",
        "\"ext_explicit\"",
    ] {
        assert!(
            placed_lean.contains(expected),
            "missing {expected} in CDemoPlacedObj.lean:\n{placed_lean}"
        );
    }
    assert!(
        files
            .iter()
            .any(|f| f.path.to_string_lossy().ends_with("CDemoPlacedObj.bin") && !f.contents.is_empty()),
        "expected non-empty CDemoPlacedObj.bin"
    );

    let extracted_lean = find_text("CDemoExtractedObj.lean");
    assert!(
        extracted_lean.contains(
            "def cDemoExtractedObjs : List Obj.ExtractedObj := [cDemoExtractedObj0, cDemoExtractedObj1, cDemoExtractedObj2]"
        ),
        "{extracted_lean}"
    );
    assert!(extracted_lean.contains("\"helper [alpha]\""), "{extracted_lean}");
    assert!(extracted_lean.contains("\"helper [beta]\""), "{extracted_lean}");
    assert!(extracted_lean.contains("\"helper [gamma]\""), "{extracted_lean}");
    assert!(
        files
            .iter()
            .any(|f| f.path.to_string_lossy().ends_with("CDemoExtractedObj.bin") && !f.contents.is_empty()),
        "expected non-empty CDemoExtractedObj.bin"
    );
}

#[test]
fn tcb_modules_never_import_untrusted_lemmas() {
    let root_src = include_str!("lib.rs");
    let common_src = include_str!("trusted_common/mod.rs");
    let extractor_src = include_str!("trusted_extractor/mod.rs");
    let extracted_obj_src = include_str!("trusted_extractor/extracted_obj.rs");
    for (name, src) in [
        ("lib.rs", root_src),
        ("trusted_common/mod.rs", common_src),
        ("trusted_extractor/mod.rs", extractor_src),
        ("trusted_extractor/extracted_obj.rs", extracted_obj_src),
    ] {
        for line in src.lines() {
            let trimmed = line.trim();
            if trimmed.starts_with("//") {
                continue;
            }
            // The crate root may *declare* the untrusted modules, but not use them.
            if name == "lib.rs" && (trimmed.starts_with("pub mod ") || trimmed.starts_with("mod ")) {
                continue;
            }
            assert!(
                !trimmed.contains("untrusted_driver")
                    && !trimmed.contains("untrusted_lemmas")
                    && !trimmed.contains("untrusted_placed")
                    && !trimmed.contains("decode_word_to_lean")
                    && !trimmed.contains("objdump")
                    && !trimmed.contains("theorem ")
                    && !trimmed.contains("std::process::Command")
                    && !trimmed.contains("cargo_metadata")
                    && !trimmed.contains("ArchiveFile")
                    && !trimmed.contains("root_section_closure"),
                "TCB module {name} must not reference untrusted modules, subprocesses, archive unpacking, or reachability pruning: {trimmed}"
            );
        }
    }
}

/// Companion `-g` DWARF extraction attaches function signatures, struct layouts, and source
/// annotations to `TargetSymbolIndex` and `symexec` without altering `-g0` object extraction.
#[test]
fn dwarf_hints_attach_to_index_and_annotate_symexec() {
    if crate::untrusted_driver::find_zig_binary("test").is_err() {
        eprintln!("skipping: zig not available");
        return;
    }
    let dir = tempfile::tempdir().unwrap();
    let root = dir.path();
    fs::write(root.join("sample.c"), untrusted_lemmas::dwarf::SAMPLE_C).unwrap();
    let toml = r#"
obj_name = "dwSample"
obj_file = "Generated/DwSampleObj.lean"
code_file = "Generated/DwSampleCode.lean"
namespace_prefix = "DwSample"
title = "DWARF sample"
c_sources = ["sample.c"]

[placed]
placed_only = true
multi = true
exports = ["sum_list", "set_flags"]
"#;
    let toml_path = root.join("translation.toml");
    fs::write(&toml_path, toml).unwrap();
    let cfg = load_config(&toml_path, root, Some(&root.join("out"))).unwrap();
    let mut tc = Toolchain::new(root.to_path_buf()).unwrap();
    let ex = crate::untrusted_driver::extract(&cfg, &mut tc).unwrap();
    let dw = untrusted_lemmas::dwarf::companion::image_dwarf(&cfg, &ex.objects);
    assert!(dw.warnings.is_empty(), "unexpected DWARF warnings: {:?}", dw.warnings);

    let obj = &ex.objects[0];
    let sym = obj
        .symbols
        .iter()
        .find(|s| s.name == "sum_list")
        .expect("sum_list symbol");
    let crate::trusted_common::SymSection::Sec(sec_idx) = sym.sec else {
        panic!("expected defined sum_list symbol");
    };
    let sec = &obj.sections[sec_idx];
    let bytes = &sec.bytes[sym.value as usize..(sym.value + sym.size) as usize];

    let mut idx = crate::untrusted_lemmas::index::TargetSymbolIndex {
        schema_version: 1,
        target: None,
        obj_name: cfg.obj_name.clone(),
        code_def: cfg.code_def_name(),
        objs_expr: cfg.image_def_name(),
        namespace_prefix: cfg.namespace_prefix.clone(),
        sub_namespace: None,
        code_file: String::new(),
        lean_file: None,
        code_module: cfg.code_module.clone(),
        code_const: String::new(),
        target_module: None,
        prog_name: None,
        functions: vec![crate::untrusted_lemmas::index::FunctionIndexEntry {
            name: "sum_list".into(),
            offset: 0,
            offset_hex: "0x0".into(),
            size_bytes: sym.size,
            size_insns: sym.size / 4,
            fn_off_lemma: String::new(),
            fn_off_lemma_full: String::new(),
            fn_size_lemma: String::new(),
            frame_bytes_lemma: None,
            decode_prefix: None,
            decode_prefix_full: None,
            frame_bytes: crate::untrusted_lemmas::index::infer_prologue_frame(bytes),
            frame_unknown: false,
            callees: Vec::new(),
            dwarf: None,
        }],
        stubs: Vec::new(),
        dwarf_types: Vec::new(),
    };
    untrusted_lemmas::dwarf::companion::attach_to_index(&dw, &mut idx);

    let f = idx.functions.iter().find(|f| f.name == "sum_list").unwrap();
    let d = f.dwarf.as_ref().expect("DWARF for sum_list");
    assert_eq!(
        d.signature(),
        "int sum_list(node_t * p, int unused, uint32_t k)"
    );
    assert_eq!(d.decl_file, "/src/sample.c");
    assert!(idx.dwarf_types.iter().any(|l| l.name == "struct node"));

    let mut report = untrusted_lemmas::symexec::analyze_and_execute(
        &f.name,
        f.offset,
        bytes,
        Some(f),
        0,
        &Default::default(),
        &Default::default(),
        &[],
        256,
        16,
    )
    .unwrap();
    report.source = Some(untrusted_lemmas::symexec::source::annotate(
        d,
        &idx.dwarf_types,
        &report,
    ));
    let text = untrusted_lemmas::symexec::format_report_text(&report);
    assert!(text.contains("--- DWARF Source"), "{text}");
    assert!(text.contains("param p = x0 (node_t *)"), "{text}");
    assert!(text.contains("DWARF vars @ +0x0: p = x0"), "{text}");
    assert!(text.contains("p->in.b : uint16_t"), "{text}");
    assert!(text.contains("p->buf[1] : uint32_t"), "{text}");
    assert!(text.contains("p->next : struct node *"), "{text}");
    assert!(text.contains("sample.c:"), "{text}");
}

#[test]
fn perturb_layout_cli_and_config_validation() {
    use crate::untrusted_driver::{
        PERTURB_LAYOUT_ENV, apply_perturb_layout_override, resolve_perturb_layout_bytes,
    };
    use clap::CommandFactory;

    // 1. `--help` documents `--perturb-layout` and `RUST_OBJ2LEAN_PERTURB_BYTES`.
    let mut help_buf = Vec::new();
    Cli::command().write_long_help(&mut help_buf).unwrap();
    let help_text = String::from_utf8(help_buf).unwrap();
    assert!(help_text.contains("--perturb-layout"), "{help_text}");
    assert!(help_text.contains(PERTURB_LAYOUT_ENV), "{help_text}");

    // 2. CLI parsing accepts multiples of 4 and rejects non-multiples of 4.
    let cli_ok = Cli::try_parse_from(["rust-obj2lean", "--perturb-layout", "64"]).unwrap();
    assert_eq!(cli_ok.perturb_layout, Some(64));
    let cli_bad = Cli::try_parse_from(["rust-obj2lean", "--perturb-layout", "62"]);
    assert!(cli_bad.is_err(), "non-multiple-of-4 CLI --perturb-layout must fail");

    // 3. Precedence: CLI > env > 0.
    assert_eq!(
        resolve_perturb_layout_bytes(Some(64), Some("4096")).unwrap(),
        64
    );
    assert_eq!(
        resolve_perturb_layout_bytes(None, Some("4096")).unwrap(),
        4096
    );
    assert_eq!(
        resolve_perturb_layout_bytes(None, Some("")).unwrap(),
        0
    );
    assert_eq!(
        resolve_perturb_layout_bytes(None, None).unwrap(),
        0
    );
    assert!(resolve_perturb_layout_bytes(None, Some("13")).is_err());

    // 4. `translation.toml` rejects persistent `perturb_layout_bytes` knob (CLI/env opt-in only).
    let (_tmp_bad, bad_toml) = write_tmp_crate(
        "bad-perturb",
        r#"
obj_name = "badPerturb"
perturb_layout_bytes = 64

[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#,
    );
    let err = load_config(&bad_toml, &test_repo_root(), None)
        .expect_err("persistent perturb_layout_bytes in translation.toml must be rejected");
    assert!(
        format!("{err:#}").contains("unknown field `perturb_layout_bytes`"),
        "{err:#}"
    );

    let (_tmp_ok, ok_toml) = write_tmp_crate(
        "ok-perturb",
        r#"
obj_name = "okPerturb"

[[targets]]
name = "t"
lean_file = "G/T.lean"
prog_name = "p"
title = "T"
lemma_allowlist = []
"#,
    );
    let cfg = load_config(&ok_toml, &test_repo_root(), None).unwrap();
    assert_eq!(cfg.perturb_layout_bytes, 0);
    let mut cfgs = vec![cfg];
    apply_perturb_layout_override(&mut cfgs, Some(4096)).unwrap();
    assert_eq!(cfgs[0].perturb_layout_bytes, 4096);
}

#[test]
fn placed_only_multi_config_emits_only_placed_obj() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("alpha.c"), "int alpha(int x) { return x + 1; }\n").unwrap();
    let cfg_path = dir.path().join("translation.toml");
    fs::write(
        &cfg_path,
        r#"
obj_name = "alpha"
title = "`alpha`"
c_sources = ["alpha.c"]

[native_compiler]
zig_version = "0.16.0"

[placed]
placed_only = true
multi = true
exports = ["alpha"]
"#,
    )
    .unwrap();
    let out_dir = dir.path().join("out");
    let cfg = load_config(&cfg_path, &test_repo_root(), Some(&out_dir)).unwrap();
    assert!(cfg.targets.is_empty());
    let mut tc = Toolchain::new(test_repo_root()).unwrap();
    let files = generate_config_with(&cfg, &mut tc, false).unwrap();
    let names: Vec<String> = files
        .iter()
        .map(|f| f.path.file_name().unwrap().to_string_lossy().into_owned())
        .collect();
    assert!(names.contains(&"AlphaPlacedObj.lean".to_string()));
    assert!(!names.contains(&"AlphaObj.lean".to_string()));
    assert!(!names.contains(&"AlphaCode.lean".to_string()));
    assert!(!names.contains(&"AlphaIndex.json".to_string()));
}

#[test]
fn placed_section_required_and_legacy_linked_image_rejected() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("alpha.c"), "int alpha(int x) { return x + 1; }\n").unwrap();
    let cfg_path = dir.path().join("translation.toml");
    fs::write(
        &cfg_path,
        r#"
obj_name = "alpha"
title = "`alpha`"
c_sources = ["alpha.c"]
legacy_linked_image = false

[native_compiler]
zig_version = "0.16.0"

[[targets]]
name = "alpha"
lean_file = "Generated/Alpha.lean"
sub_namespace = "Alpha"
prog_name = "alphaProg"
title = "Alpha"
lemma_allowlist = ["alpha"]
"#,
    )
    .unwrap();
    let out_dir = dir.path().join("out");
    let cfg = load_config(&cfg_path, &test_repo_root(), Some(&out_dir)).unwrap();
    let mut tc = Toolchain::new(test_repo_root()).unwrap();
    let err = match generate_config_with(&cfg, &mut tc, false) {
        Ok(_) => panic!("export target without `[placed]` must fail"),
        Err(e) => e,
    };
    let msg = format!("{err:#}");
    assert!(
        msg.contains("has no `[placed]` section"),
        "unexpected error for missing [placed]: {msg}"
    );

    assert!(
        Cli::try_parse_from(["rust-obj2lean", "--legacy-linked-image"]).is_err(),
        "`--legacy-linked-image` CLI flag must be rejected"
    );

    let bad_cfg_path = dir.path().join("bad_legacy.toml");
    fs::write(
        &bad_cfg_path,
        r#"
obj_name = "alpha"
title = "`alpha`"
c_sources = ["alpha.c"]
legacy_linked_image = true

[native_compiler]
zig_version = "0.16.0"

[placed]
placed_only = true
multi = true
exports = ["alpha"]
"#,
    )
    .unwrap();
    let err_load = load_config(&bad_cfg_path, &test_repo_root(), Some(&out_dir))
        .expect_err("`legacy_linked_image = true` in TOML must fail");
    assert!(
        format!("{err_load:#}").contains(
            "legacy_linked_image = true is no longer supported; configure [placed] for Obj.PlacedLib / Obj.MultiPlacedLib"
        ),
        "{err_load:#}"
    );
}

#[test]
fn placed_with_extracted_obj_emits_identical_outputs_with_or_without_placed_only() {
    if crate::untrusted_driver::find_zig_binary("test").is_err() {
        eprintln!("skipping end-to-end C placed extracted_obj test: zig not available");
        return;
    }
    let cli = Cli::try_parse_from(["rust-obj2lean", "--placed-only", "--extracted-obj"]).unwrap();
    assert!(cli.placed_only);
    assert!(cli.extracted_obj);

    let dir = tempfile::tempdir().unwrap();
    fs::write(
        dir.path().join("alpha.c"),
        "extern int ext_fn(int); static int slot = 7; int alpha(int x) { return ext_fn(x + slot); }\n",
    )
    .unwrap();
    let cfg_path = dir.path().join("translation.toml");
    fs::write(
        &cfg_path,
        r#"
obj_name = "alpha"
title = "`alpha`"
c_sources = ["alpha.c"]

[native_compiler]
zig_version = "0.16.0"

[[externs]]
name = "ext_fn"
kind = "func"

[placed]
placed_only = true
multi = true
emit_extracted_obj = true
exports = ["alpha"]
"#,
    )
    .unwrap();
    let out_dir = dir.path().join("out");
    let cfg = load_config(&cfg_path, &test_repo_root(), Some(&out_dir)).unwrap();
    let mut tc = Toolchain::new(test_repo_root()).unwrap();
    let files = generate_config_with(&cfg, &mut tc, false).unwrap();
    let names: Vec<String> = files
        .iter()
        .map(|f| f.path.file_name().unwrap().to_string_lossy().into_owned())
        .collect();
    assert!(names.contains(&"AlphaPlacedObj.lean".to_string()));
    assert!(names.contains(&"AlphaExtractedObj.lean".to_string()));
    assert!(names.contains(&"AlphaExtractedObj.bin".to_string()));
    assert!(!names.contains(&"AlphaObj.lean".to_string()));

    let placed_only_lean = files
        .iter()
        .find(|f| f.path.to_string_lossy().ends_with("AlphaExtractedObj.lean"))
        .unwrap()
        .contents
        .clone();
    let placed_only_bin = files
        .iter()
        .find(|f| f.path.to_string_lossy().ends_with("AlphaExtractedObj.bin"))
        .unwrap()
        .contents
        .clone();

    let mut default_placed_cfg = cfg.clone();
    default_placed_cfg.placed.as_mut().unwrap().placed_only = false;
    let default_files = generate_config_with(&default_placed_cfg, &mut tc, false).unwrap();
    assert_eq!(files.len(), default_files.len());
    for (a, b) in files.iter().zip(&default_files) {
        assert_eq!(a.path, b.path);
        assert_eq!(a.contents, b.contents);
    }
    let default_lean = default_files
        .iter()
        .find(|f| f.path.to_string_lossy().ends_with("AlphaExtractedObj.lean"))
        .unwrap()
        .contents
        .clone();
    let default_bin = default_files
        .iter()
        .find(|f| f.path.to_string_lossy().ends_with("AlphaExtractedObj.bin"))
        .unwrap()
        .contents
        .clone();
    assert_eq!(placed_only_lean, default_lean);
    assert_eq!(placed_only_bin, default_bin);
}

#[cfg(unix)]
#[test]
fn fetch_upstream_sources_musl_126_rejects_corrupt_sha256() {
    use std::process::Command;

    let repo_root = test_repo_root();
    let script_src = fs::read_to_string(repo_root.join("scripts/fetch-upstream-sources.sh"))
        .expect("scripts/fetch-upstream-sources.sh must exist");
    let musl_126_sha = script_src
        .lines()
        .find_map(|l| {
            l.strip_prefix("MUSL_126_SHA256=\"")
                .and_then(|r| r.strip_suffix('"'))
        })
        .expect("MUSL_126_SHA256 must be pinned in scripts/fetch-upstream-sources.sh");
    assert_eq!(musl_126_sha.len(), 64);

    let tmp = tempfile::tempdir().unwrap();
    let fake_root = tmp.path().join("repo");
    fs::create_dir_all(fake_root.join("scripts")).unwrap();
    let fake_script = fake_root.join("scripts/fetch-upstream-sources.sh");
    fs::write(&fake_script, &script_src).unwrap();
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&fake_script, fs::Permissions::from_mode(0o755)).unwrap();
    }

    // 1. Corrupt pre-cached archive is detected by SHA-256 verification and evicted.
    let cache_dir = tmp.path().join("cache");
    let archives_dir = cache_dir.join("archives");
    fs::create_dir_all(&archives_dir).unwrap();
    let cached_tar = archives_dir.join(format!("{musl_126_sha}-musl-1.2.6.tar.gz"));
    fs::write(&cached_tar, b"tampered-musl-1.2.6-archive").unwrap();

    let out = Command::new("bash")
        .arg(&fake_script)
        .args(["--print-env", "musl-1.2.6"])
        .current_dir(&fake_root)
        .env("ARM64_UPSTREAM_CACHE", &cache_dir)
        .output()
        .expect("bash must run fetch-upstream-sources.sh");
    assert!(
        !out.status.success(),
        "corrupt cached musl-1.2.6 tarball must fail verification"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("checksum mismatch"),
        "expected checksum mismatch diagnostic, got: {stderr}"
    );
    assert!(
        !cached_tar.exists(),
        "corrupt cached archive must be evicted on SHA-256 mismatch"
    );
    assert!(
        !fake_root.join("third_party/musl-1.2.6/upstream").exists(),
        "unverified archive must never be unpacked"
    );

    // 2. Corrupt downloaded archive from primary + mirror URLs is discarded without unpacking.
    if which::which("curl").is_ok() {
        let bad_src = tmp.path().join("bad-musl-1.2.6.tar.gz");
        fs::write(&bad_src, b"corrupt-download-bytes").unwrap();
        let bad_url = format!("file://{}", bad_src.display());
        let out_dl = Command::new("bash")
            .arg(&fake_script)
            .args(["--print-env", "musl-1.2.6"])
            .current_dir(&fake_root)
            .env("ARM64_UPSTREAM_CACHE", &cache_dir)
            .env("MUSL_126_URL", &bad_url)
            .env("MUSL_126_MIRROR_URL", &bad_url)
            .output()
            .expect("bash must run fetch-upstream-sources.sh");
        assert!(
            !out_dl.status.success(),
            "corrupt downloaded musl-1.2.6 tarball must fail verification"
        );
        let stderr_dl = String::from_utf8_lossy(&out_dl.stderr);
        assert!(
            stderr_dl.contains("checksum mismatch") || stderr_dl.contains("could not download"),
            "expected checksum/download failure diagnostic, got: {stderr_dl}"
        );
        assert!(!cached_tar.exists());
        assert!(!fake_root.join("third_party/musl-1.2.6/upstream").exists());
    }
}

#[cfg(unix)]
#[test]
fn ensure_rust_exports_cold_fetches_and_warm_forbids_subprocesses_and_writes() {
    use sha2::{Digest, Sha256};
    use std::os::unix::fs::PermissionsExt;
    use std::process::Command;

    struct ReadOnlyGuard(Vec<PathBuf>);
    impl ReadOnlyGuard {
        fn set_mode_recursive(path: &Path, writable: bool) {
            let Ok(meta) = fs::symlink_metadata(path) else {
                return;
            };
            if meta.file_type().is_symlink() {
                return;
            }
            if writable && meta.is_dir() {
                let mut mode = meta.permissions().mode();
                mode |= 0o700;
                let _ = fs::set_permissions(path, fs::Permissions::from_mode(mode));
            }
            if meta.is_dir()
                && let Ok(entries) = fs::read_dir(path)
            {
                for entry in entries.flatten() {
                    Self::set_mode_recursive(&entry.path(), writable);
                }
            }
            let mut mode = meta.permissions().mode();
            if writable {
                mode |= if meta.is_dir() { 0o700 } else { 0o600 };
            } else {
                mode &= !0o222;
            }
            let _ = fs::set_permissions(path, fs::Permissions::from_mode(mode));
        }

        fn lock(paths: Vec<PathBuf>, verify_unwritable_dir: &Path) -> Self {
            assert!(
                verify_unwritable_dir.is_dir(),
                "ReadOnlyGuard target `{}` must be an existing directory before write probe",
                verify_unwritable_dir.display()
            );
            for p in &paths {
                Self::set_mode_recursive(p, false);
            }
            let guard = Self(paths);
            assert!(
                fs::write(verify_unwritable_dir.join(".ro_probe"), b"x").is_err(),
                "ReadOnlyGuard must deny writes into `{}` (chmod is vacuous when running as root)",
                verify_unwritable_dir.display()
            );
            guard
        }
    }
    impl Drop for ReadOnlyGuard {
        fn drop(&mut self) {
            for p in &self.0 {
                Self::set_mode_recursive(p, true);
            }
        }
    }

    fn write_exec(path: &Path, body: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        fs::write(path, body).unwrap();
        fs::set_permissions(path, fs::Permissions::from_mode(0o755)).unwrap();
    }

    fn read_count(path: &Path) -> usize {
        fs::read_to_string(path)
            .ok()
            .map(|s| s.lines().filter(|l| !l.trim().is_empty()).count())
            .unwrap_or(0)
    }

    let in_ci = std::env::var("CI")
        .map(|v| !v.is_empty() && v != "0" && v != "false")
        .unwrap_or(false);
    let repo_root = test_repo_root();
    let lean_prefix_out = Command::new("lean")
        .arg("--print-prefix")
        .current_dir(&repo_root)
        .output();
    let Ok(lean_prefix_out) = lean_prefix_out else {
        assert!(
            !in_ci,
            "CI is set, so `lean` must be on PATH for LakeExports warm sandbox test"
        );
        eprintln!("skipping LakeExports warm sandbox test: `lean` not on PATH");
        return;
    };
    if !lean_prefix_out.status.success() {
        assert!(
            !in_ci,
            "CI is set, so `lean --print-prefix` must succeed for LakeExports warm sandbox test"
        );
        eprintln!("skipping LakeExports warm sandbox test: `lean --print-prefix` failed");
        return;
    }
    let lean_prefix = PathBuf::from(String::from_utf8_lossy(&lean_prefix_out.stdout).trim());
    let lean_bin_dir = lean_prefix.join("bin");
    let lake_bin = lean_bin_dir.join("lake");
    if !lake_bin.is_file() {
        assert!(
            !in_ci,
            "CI is set, so `{}` must exist for LakeExports warm sandbox test",
            lake_bin.display()
        );
        eprintln!(
            "skipping LakeExports warm sandbox test: `{}` not found",
            lake_bin.display()
        );
        return;
    }

    let tmp = tempfile::tempdir().unwrap();
    let ws = normalize_path(&tmp.path().join("ws"));
    let state_dir = normalize_path(&tmp.path().join("state"));
    let shims_dir = normalize_path(&tmp.path().join("shims"));
    let poison_dir = normalize_path(&tmp.path().join("poison"));
    fs::create_dir_all(&ws).unwrap();
    fs::create_dir_all(&state_dir).unwrap();
    fs::create_dir_all(&shims_dir).unwrap();
    fs::create_dir_all(&poison_dir).unwrap();

    // Copy `lean-toolchain` and the real `scripts/LakeExports.lean`, plus stubs for every file
    // referenced by `exportToolInputs`.
    let toolchain = fs::read_to_string(repo_root.join("lean-toolchain")).unwrap();
    fs::write(ws.join("lean-toolchain"), &toolchain).unwrap();
    let lake_exports_src = fs::read_to_string(repo_root.join("scripts/LakeExports.lean")).unwrap();
    fs::create_dir_all(ws.join("scripts")).unwrap();
    fs::write(ws.join("scripts/LakeExports.lean"), &lake_exports_src).unwrap();

    let (_, after_tool_inputs) = lake_exports_src
        .split_once("def exportToolInputs")
        .expect("scripts/LakeExports.lean must define exportToolInputs");
    let (tool_inputs_block, _) = after_tool_inputs
        .split_once(']')
        .expect("exportToolInputs array must close with `]`");
    for piece in tool_inputs_block.split('"').skip(1).step_by(2) {
        let p = ws.join(piece);
        if let Some(parent) = p.parent() {
            fs::create_dir_all(parent).unwrap();
        }
        if !p.exists() {
            fs::write(&p, "// stub\n").unwrap();
        }
    }

    let fetch_log = state_dir.join("fetch.log");
    let cargo_log = state_dir.join("cargo.log");
    let cargo_env_log = state_dir.join("cargo.env");
    let rustc_log = state_dir.join("rustc.log");
    let poison_log = state_dir.join("poison.log");
    let upstream_payload = state_dir.join("upstream_alpha.c");
    let expected_sha_file = state_dir.join("expected.sha256");

    // `scripts/fetch-upstream-sources.sh` verifies SHA-256 of `upstream_alpha.c`, takes a lock
    // under `.lake/`, unpacks `third_party/alpha-1.0/alpha.c`, and prints `ALPHA_UPSTREAM_SRC=...`.
    let fetch_script = format!(
        "#!/usr/bin/env bash\n\
         set -euo pipefail\n\
         echo \"fetch:$*\" >> \"{fetch_log}\"\n\
         ROOT=\"$(cd \"$(dirname \"${{BASH_SOURCE[0]}}\")/..\" && pwd)\"\n\
         mkdir -p \"$ROOT/.lake\"\n\
         echo lock > \"$ROOT/.lake/fetch-upstream-sources.lock\"\n\
         EXPECTED=\"$(cat \"{expected_sha}\")\"\n\
         GOT=\"$(sha256sum \"{payload}\" | awk '{{print $1}}')\"\n\
         if [ \"$GOT\" != \"$EXPECTED\" ]; then\n\
           echo \"checksum mismatch: expected $EXPECTED, got $GOT\" >&2\n\
           exit 1\n\
         fi\n\
         mkdir -p \"$ROOT/third_party/alpha-1.0\"\n\
         cp -f \"{payload}\" \"$ROOT/third_party/alpha-1.0/alpha.c\"\n\
         for arg in \"$@\"; do\n\
           if [ \"$arg\" = \"--print-env\" ]; then\n\
             echo \"ALPHA_UPSTREAM_SRC=$ROOT/third_party/alpha-1.0\"\n\
           fi\n\
         done\n",
        fetch_log = fetch_log.display(),
        expected_sha = expected_sha_file.display(),
        payload = upstream_payload.display(),
    );
    write_exec(&ws.join("scripts/fetch-upstream-sources.sh"), &fetch_script);

    // Mock `rustc` and `cargo` shims for cold/dirty export builds.
    write_exec(
        &shims_dir.join("rustc"),
        &format!(
            "#!/bin/sh\necho rustc >> \"{}\"\necho 'rustc 1.98.1 (mock)'\n",
            rustc_log.display()
        ),
    );
    write_exec(
        &shims_dir.join("cargo"),
        &format!(
            "#!/usr/bin/env bash\n\
             set -euo pipefail\n\
             echo \"cargo:$*\" >> \"{cargo_log}\"\n\
             {{\n\
               echo \"ZLIB_NO_CLONE=${{ZLIB_NO_CLONE:-}}\"\n\
               echo \"HASHBROWN_NO_CLONE=${{HASHBROWN_NO_CLONE:-}}\"\n\
               echo \"ALPHA_UPSTREAM_SRC=${{ALPHA_UPSTREAM_SRC:-}}\"\n\
             }} > \"{cargo_env}\"\n\
             OUT_DIR=\"\"\n\
             while [ $# -gt 0 ]; do\n\
               if [ \"$1\" = \"--out-dir\" ]; then OUT_DIR=\"$2\"; shift 2; else shift; fi\n\
             done\n\
             [ -n \"$OUT_DIR\" ]\n\
             [ -f \"${{ALPHA_UPSTREAM_SRC}}/alpha.c\" ]\n\
             MARKER=\"$(wc -c < \"${{ALPHA_UPSTREAM_SRC}}/alpha.c\" | tr -d ' ')\"\n\
             mkdir -p \"$OUT_DIR/Alpha/Generated\"\n\
             printf 'module\\npublic section\\ndef alphaMarker : Nat := %s\\n' \"$MARKER\" > \"$OUT_DIR/Alpha/Generated/AlphaPlacedObj.lean\"\n\
             printf 'BIN%s' \"$MARKER\" > \"$OUT_DIR/Alpha/Generated/AlphaPlacedObj.bin\"\n",
            cargo_log = cargo_log.display(),
            cargo_env = cargo_env_log.display(),
        ),
    );

    // Poison `bash` and `cargo` shims (+ working `rustc`) for verifying developer warm builds.
    for cmd in ["bash", "cargo"] {
        write_exec(
            &poison_dir.join(cmd),
            &format!(
                "#!/bin/sh\necho \"poison:{cmd}:$*\" >> \"{}\"\nexit 99\n",
                poison_log.display()
            ),
        );
    }
    write_exec(
        &poison_dir.join("rustc"),
        &format!(
            "#!/bin/sh\necho rustc >> \"{}\"\necho 'rustc 1.98.1 (mock)'\n",
            rustc_log.display()
        ),
    );

    // Subpackage `subpkg` (models `VerifiedLibraries` / `CaseStudies/<Lib>`) + root consumer.
    let subpkg = ws.join("subpkg");
    fs::create_dir_all(subpkg.join("Implementation")).unwrap();
    fs::write(subpkg.join("lean-toolchain"), &toolchain).unwrap();
    fs::write(
        subpkg.join("Implementation/translation.toml"),
        "obj_name = \"alpha\"\n",
    )
    .unwrap();
    fs::write(
        subpkg.join("Implementation/shim.c"),
        "int shim(void) { return 1; }\n",
    )
    .unwrap();
    fs::write(
        subpkg.join("lakefile.lean"),
        r#"import Lake
open Lake DSL
open System (FilePath)

open Lean Elab Command in
elab "include_lake_file " rel:str : command => do
  let curDir := (System.FilePath.mk (← read).fileName).parent.getD "."
  let path := curDir / rel.getString
  let src ← IO.FS.readFile path
  let env ← getEnv
  let ictx := Parser.mkInputContext src path.toString
  let mut pstate : Parser.ModuleParserState := {}
  let scope := (← get).scopes.head!
  while !ictx.atEnd pstate.pos do
    let (stx, pstate', msgs) := Parser.parseCommand ictx { env, options := scope.opts } pstate (← get).messages
    modify fun s => { s with messages := msgs }
    pstate := pstate'
    if Parser.isTerminalCommand stx then break
    withReader (fun ctx => { ctx with fileName := path.toString, fileMap := ictx.fileMap }) do
      elabCommandTopLevel stx

include_lake_file "../scripts/LakeExports.lean"

def alphaExportSpecs : Array ExportTargetSpec := #[
  { name := "alpha"
    config := "Implementation/translation.toml"
    inputs := #[
      "Implementation/translation.toml",
      "Implementation/shim.c",
      "../third_party/alpha-1.0/alpha.c"
    ]
    outputs := #[
      "Alpha/Generated/AlphaPlacedObj.lean",
      "Alpha/Generated/AlphaPlacedObj.bin"
    ] }
]

def alphaExportOutputs : Array String :=
  alphaExportSpecs.foldl (fun acc s => acc ++ s.outputs) #[]

package «alpha-subpkg» where
  version := v!"0.1.0"
  leanOptions := standardLeanOptions

target rustExports pkg : Array FilePath := Job.async do
  setTraceCaption "rustExports"
  let repoRoot := pkg.dir / ".."
  let (depTrace, outFiles) ←
    ensureRustExports pkg.dir alphaExportSpecs "rustExportsAlpha" #["alpha-1.0"]
      repoRoot "Alpha/Generated" "Alpha.Generated"
  addTrace depTrace
  cleanupStaleGeneratedFiles (pkg.dir / "Alpha" / "Generated")
    "Alpha/Generated" alphaExportOutputs
  let outTrace ← computeRelativeFilesTrace pkg.dir "outputs" alphaExportOutputs
  addTrace outTrace
  return outFiles

@[«module_facet»] def generatedInputFacet : ModuleFacetDecl :=
  mkGeneratedInputFacet `Alpha.Generated

lean_lib Alpha where
  roots := #[`Alpha.Generated.AlphaPlacedObj]
  globs := #[.one `Alpha.Generated.AlphaPlacedObj]
"#,
    )
    .unwrap();

    fs::write(
        ws.join("lakefile.lean"),
        r#"import Lake
open Lake DSL

package «alpha-root» where
  version := v!"0.1.0"

require «alpha-subpkg» from "subpkg"

@[default_target]
lean_lib Consumer where
  roots := #[`Consumer]
"#,
    )
    .unwrap();
    fs::write(
        ws.join("Consumer.lean"),
        "module\npublic import Alpha.Generated.AlphaPlacedObj\npublic section\ndef consumerVal : Nat := alphaMarker\n",
    )
    .unwrap();

    let host_path = std::env::var("PATH").unwrap_or_default();
    let cold_path = format!(
        "{}:{}:{host_path}",
        shims_dir.display(),
        lean_bin_dir.display()
    );
    let home_dir = std::env::var("HOME").unwrap_or_else(|_| tmp.path().display().to_string());

    // Stage A: Cold checkout with corrupt SHA-256 fails closed before invoking `cargo`.
    let v1_bytes = b"int alpha_val(void) { return 7; }\n";
    fs::write(&upstream_payload, v1_bytes).unwrap();
    fs::write(&expected_sha_file, "0".repeat(64)).unwrap();
    assert!(!ws.join("third_party/alpha-1.0/alpha.c").exists());

    let bad_cold = Command::new(&lake_bin)
        .args(["build", "--no-ansi", "Consumer"])
        .current_dir(&ws)
        .env_clear()
        .env("PATH", &cold_path)
        .env("HOME", &home_dir)
        .env("LEAN_NUM_THREADS", "2")
        .output()
        .unwrap();
    assert!(
        !bad_cold.status.success(),
        "cold build with mismatched upstream SHA-256 must fail"
    );
    assert_eq!(read_count(&fetch_log), 1);
    assert_eq!(read_count(&cargo_log), 0);
    assert!(!subpkg.join("Alpha/Generated/AlphaPlacedObj.lean").exists());

    // Stage B: Cold checkout with valid SHA-256 fetches upstream before hashing and builds cleanly.
    let v1_sha = hex::encode(Sha256::digest(v1_bytes));
    fs::write(&expected_sha_file, &v1_sha).unwrap();
    let _ = fs::remove_dir_all(ws.join("third_party"));

    let ok_cold = Command::new(&lake_bin)
        .args(["build", "--no-ansi", "Consumer"])
        .current_dir(&ws)
        .env_clear()
        .env("PATH", &cold_path)
        .env("HOME", &home_dir)
        .env("LEAN_NUM_THREADS", "2")
        .output()
        .unwrap();
    assert!(
        ok_cold.status.success(),
        "cold build failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&ok_cold.stdout),
        String::from_utf8_lossy(&ok_cold.stderr)
    );
    assert_eq!(read_count(&fetch_log), 2);
    assert_eq!(read_count(&cargo_log), 1);
    let cargo_env_text = fs::read_to_string(&cargo_env_log).unwrap();
    assert!(
        cargo_env_text.contains("ZLIB_NO_CLONE=1"),
        "{cargo_env_text}"
    );
    assert!(
        cargo_env_text.contains("HASHBROWN_NO_CLONE=1"),
        "{cargo_env_text}"
    );
    assert!(
        cargo_env_text.contains(&format!(
            "ALPHA_UPSTREAM_SRC={}",
            ws.join("third_party/alpha-1.0").display()
        )),
        "{cargo_env_text}"
    );
    assert!(
        subpkg
            .join("Alpha/Generated/.rustExportsAlpha.inputs.stamp")
            .is_file()
    );

    let subpkg_build_dir = subpkg.join(".lake/build");
    let dev_warm_path = format!("{}:{}", poison_dir.display(), lean_bin_dir.display());
    let expected_build_stamp =
        fs::read_to_string(subpkg_build_dir.join("rustExportsAlpha.stamp")).unwrap();
    let expected_gen_stamp =
        fs::read_to_string(subpkg.join("Alpha/Generated/.rustExportsAlpha.stamp")).unwrap();
    let expected_gen_inputs_stamp =
        fs::read_to_string(subpkg.join("Alpha/Generated/.rustExportsAlpha.inputs.stamp")).unwrap();
    assert!(!expected_build_stamp.trim().is_empty());
    assert_eq!(expected_build_stamp, expected_gen_stamp);
    assert!(!expected_gen_inputs_stamp.trim().is_empty());

    // Stage C1: Warm sandboxed build with subpackage & upstream trees read-only, missing
    // subpackage `.lake/build/rustExportsAlpha.trace`, and `PATH` restricted solely to
    // `<lean_prefix>/bin` (no `bash`, `sh`, `cargo`, or `rustc`; no `LAKE_TRUST_CACHED_RUST_EXPORTS`).
    let _ = fs::remove_file(subpkg_build_dir.join("rustExportsAlpha.trace"));
    let _ = fs::remove_file(ws.join(".lake/fetch-upstream-sources.lock"));
    {
        let _ro = ReadOnlyGuard::lock(
            vec![
                subpkg.clone(),
                ws.join("scripts"),
                ws.join("tools"),
                ws.join("third_party"),
            ],
            &subpkg_build_dir,
        );

        let warm_sandbox = Command::new(&lake_bin)
            .args(["build", "--no-ansi", "Consumer"])
            .current_dir(&ws)
            .env_clear()
            .env("PATH", &lean_bin_dir)
            .env("HOME", &home_dir)
            .env("LEAN_NUM_THREADS", "2")
            .output()
            .unwrap();
        assert!(
            warm_sandbox.status.success(),
            "warm sandboxed build failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&warm_sandbox.stdout),
            String::from_utf8_lossy(&warm_sandbox.stderr)
        );
        assert_eq!(
            read_count(&fetch_log),
            2,
            "warm build must not run fetch script"
        );
        assert_eq!(read_count(&cargo_log), 1, "warm build must not run cargo");
        assert!(
            !ws.join(".lake/fetch-upstream-sources.lock").exists(),
            "warm build must not create fetch lock file"
        );

        // Stage C2: Warm developer build (`rustc` on PATH, poison `bash` and `cargo` on PATH,
        // `LAKE_TRUST_CACHED_RUST_EXPORTS` unset, subpackage still read-only).
        let rustc_before = read_count(&rustc_log);
        let warm_dev = Command::new(&lake_bin)
            .args(["build", "--no-ansi", "Consumer"])
            .current_dir(&ws)
            .env_clear()
            .env("PATH", &dev_warm_path)
            .env("HOME", &home_dir)
            .env("LEAN_NUM_THREADS", "2")
            .output()
            .unwrap();
        assert!(
            warm_dev.status.success(),
            "warm dev build failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&warm_dev.stdout),
            String::from_utf8_lossy(&warm_dev.stderr)
        );
        assert!(
            read_count(&rustc_log) > rustc_before,
            "ensureRustExports must actually execute during warm Consumer build"
        );
        assert_eq!(
            read_count(&poison_log),
            0,
            "warm dev build must never spawn bash or cargo"
        );

        // Stage C3: If `landrun` is installed and supported by the host kernel, also run the
        // exact comparator `landrun` sandbox shape (`--ro <ws> --rwx <ws>/.lake --rox <lean_prefix>`).
        let landrun_bin = std::env::var_os("COMPARATOR_LANDRUN")
            .map(PathBuf::from)
            .filter(|p| p.is_file())
            .or_else(|| which::which("landrun").ok());
        if let Some(landrun) = landrun_bin {
            let probe = Command::new(&landrun)
                .args([
                    "--best-effort",
                    "--ro",
                    "/",
                    "--rw",
                    "/dev",
                    "-ldd",
                    "-add-exec",
                    "--rox",
                    &lean_prefix.to_string_lossy(),
                    "--",
                    &lean_bin_dir.join("lean").to_string_lossy(),
                    "--version",
                ])
                .output();
            if let Ok(p) = probe
                && p.status.success()
            {
                let warm_landrun = Command::new(&landrun)
                    .args([
                        "--best-effort",
                        "--ro",
                        "/",
                        "--rw",
                        "/dev",
                        "-ldd",
                        "-add-exec",
                        "--env",
                        "PATH",
                        "--env",
                        "HOME",
                        "--env",
                        "LEAN_NUM_THREADS",
                        "--ro",
                        &ws.to_string_lossy(),
                        "--rwx",
                        &ws.join(".lake").to_string_lossy(),
                        "--rox",
                        &lean_prefix.to_string_lossy(),
                        "--",
                        &lake_bin.to_string_lossy(),
                        "build",
                        "--no-ansi",
                        "Consumer",
                    ])
                    .current_dir(&ws)
                    .env_clear()
                    .env("PATH", &cold_path)
                    .env("HOME", &home_dir)
                    .env("LEAN_NUM_THREADS", "2")
                    .output()
                    .unwrap();
                assert!(
                    warm_landrun.status.success(),
                    "warm landrun build failed:\nstdout:\n{}\nstderr:\n{}",
                    String::from_utf8_lossy(&warm_landrun.stdout),
                    String::from_utf8_lossy(&warm_landrun.stderr)
                );
                assert_eq!(read_count(&fetch_log), 2);
                assert_eq!(read_count(&cargo_log), 1);
            }
        }
    }

    // Stage C4: Per-target trace backfill & empty-`dirtySpecs` path under a read-only subpackage
    // `.lake/build` (top-level trace/stamps stale or missing, per-target `.trace` missing,
    // per-target stamp still matching, `rustc` + poison `bash`/`cargo` on PATH). Verifies that
    // filesystem errors are caught in `IO` before `MonadLift IO JobM` can fail the Lake job.
    let _ = fs::remove_file(subpkg_build_dir.join("rustExportsAlpha.alpha.trace"));
    let _ = fs::remove_file(subpkg_build_dir.join("rustExportsAlpha.trace"));
    fs::write(subpkg_build_dir.join("rustExportsAlpha.stamp"), "stale\n").unwrap();
    fs::write(
        subpkg.join("Alpha/Generated/.rustExportsAlpha.stamp"),
        "stale\n",
    )
    .unwrap();
    fs::write(
        subpkg.join("Alpha/Generated/.rustExportsAlpha.inputs.stamp"),
        "stale\n",
    )
    .unwrap();
    {
        let _ro = ReadOnlyGuard::lock(
            vec![
                subpkg.clone(),
                ws.join("scripts"),
                ws.join("tools"),
                ws.join("third_party"),
            ],
            &subpkg_build_dir,
        );
        let probe = Command::new(&lake_bin)
            .args(["build", "--no-ansi", "Consumer"])
            .current_dir(&ws)
            .env_clear()
            .env("PATH", &dev_warm_path)
            .env("HOME", &home_dir)
            .env("LEAN_NUM_THREADS", "2")
            .output()
            .unwrap();
        assert!(
            probe.status.success(),
            "per-target backfill under read-only subpackage failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&probe.stdout),
            String::from_utf8_lossy(&probe.stderr)
        );
        assert_eq!(read_count(&fetch_log), 2);
        assert_eq!(read_count(&cargo_log), 1);
        assert_eq!(read_count(&poison_log), 0);
    }

    // Stage C5: When the subpackage is writable again, the same stale top-level stamps and missing
    // traces self-heal on a warm build without invoking `fetch` or `cargo`.
    let heal = Command::new(&lake_bin)
        .args(["build", "--no-ansi", "Consumer"])
        .current_dir(&ws)
        .env_clear()
        .env("PATH", &dev_warm_path)
        .env("HOME", &home_dir)
        .env("LEAN_NUM_THREADS", "2")
        .output()
        .unwrap();
    assert!(
        heal.status.success(),
        "writable self-heal warm build failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&heal.stdout),
        String::from_utf8_lossy(&heal.stderr)
    );
    assert_eq!(read_count(&fetch_log), 2);
    assert_eq!(read_count(&cargo_log), 1);
    assert_eq!(read_count(&poison_log), 0);
    assert!(
        subpkg_build_dir
            .join("rustExportsAlpha.alpha.trace")
            .is_file()
    );
    assert!(subpkg_build_dir.join("rustExportsAlpha.trace").is_file());
    assert_eq!(
        fs::read_to_string(subpkg_build_dir.join("rustExportsAlpha.stamp")).unwrap(),
        expected_build_stamp
    );
    assert_eq!(
        fs::read_to_string(subpkg.join("Alpha/Generated/.rustExportsAlpha.stamp")).unwrap(),
        expected_gen_stamp
    );
    assert_eq!(
        fs::read_to_string(subpkg.join("Alpha/Generated/.rustExportsAlpha.inputs.stamp")).unwrap(),
        expected_gen_inputs_stamp
    );

    // Stage D: Dirty rebuild when upstream source + fetch script update (all prior outputs and
    // inputs already exist on disk, exercising lazy `fetchUpstreamSources` + post-fetch trace
    // recomputation), followed by another warm sandboxed build that must stay a no-op.
    let v2_bytes = b"int alpha_val(void) { return 123456; }\n";
    let v2_sha = hex::encode(Sha256::digest(v2_bytes));
    fs::write(&upstream_payload, v2_bytes).unwrap();
    fs::write(&expected_sha_file, &v2_sha).unwrap();
    let updated_fetch = format!("{fetch_script}# upstream bump\n");
    write_exec(
        &ws.join("scripts/fetch-upstream-sources.sh"),
        &updated_fetch,
    );

    let dirty_rebuild = Command::new(&lake_bin)
        .args(["build", "--no-ansi", "Consumer"])
        .current_dir(&ws)
        .env_clear()
        .env("PATH", &cold_path)
        .env("HOME", &home_dir)
        .env("LEAN_NUM_THREADS", "2")
        .output()
        .unwrap();
    assert!(
        dirty_rebuild.status.success(),
        "dirty rebuild failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&dirty_rebuild.stdout),
        String::from_utf8_lossy(&dirty_rebuild.stderr)
    );
    assert_eq!(read_count(&fetch_log), 3);
    assert_eq!(read_count(&cargo_log), 2);
    let generated_lean =
        fs::read_to_string(subpkg.join("Alpha/Generated/AlphaPlacedObj.lean")).unwrap();
    assert!(
        generated_lean.contains(&format!("alphaMarker : Nat := {}", v2_bytes.len())),
        "{generated_lean}"
    );

    {
        let _ro = ReadOnlyGuard::lock(
            vec![
                subpkg.clone(),
                ws.join("scripts"),
                ws.join("tools"),
                ws.join("third_party"),
            ],
            &subpkg_build_dir,
        );
        let warm_after_dirty = Command::new(&lake_bin)
            .args(["build", "--no-ansi", "Consumer"])
            .current_dir(&ws)
            .env_clear()
            .env("PATH", &lean_bin_dir)
            .env("HOME", &home_dir)
            .env("LEAN_NUM_THREADS", "2")
            .output()
            .unwrap();
        assert!(
            warm_after_dirty.status.success(),
            "post-dirty warm sandboxed build failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&warm_after_dirty.stdout),
            String::from_utf8_lossy(&warm_after_dirty.stderr)
        );
        assert_eq!(read_count(&fetch_log), 3);
        assert_eq!(read_count(&cargo_log), 2);
    }
}
