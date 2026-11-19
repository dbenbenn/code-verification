// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! CLI entry point for `snapshot-link` (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` — builds static AArch64 Linux `ET_EXEC` executables for
//!   whole-binary Lean verification and `proc-snapshot`. Nothing it produces is trusted: Lean
//!   proofs verify `Arm64.Process.ElfImage.parse` and `LinkedIn` / `MultiPlacedLib` witnesses
//!   directly against the SHA-256-pinned ELF bytes.
//! - **Purpose:** Supports two link recipes:
//!   1. `snapshot-link --stock --config <translation.toml>... --out-dir <dir>` extracts the
//!      relocatable `.o` objects of one or more `translation.toml` files via `rust-obj2lean`
//!      (linking trimmed `[[sysroot_objects]]` as real objects of their trims, see [`trimmed`]),
//!      links them with stock `ld.lld` defaults (relaxation on, `--gc-sections`, no linker
//!      script) against the staged musl runtime or rustc's pinned `self-contained` runtime for a
//!      Rust `std` binary `--main-rust` (see [`stock`], [`stock_std`], [`stock_hooks`], and
//!      [`stock_std_audit`]), checks the static-ELF loader invariants (see
//!      [`verify::check_std_elf`]), and writes `<name>`, `stock-link.json`, and the
//!      relocation-site census `census.json` (see [`census`]).
//!   2. `snapshot-link --main-rust <Cargo.toml> --out-dir <dir>` compiles a safe Rust `std`
//!      binary crate under the pinned Rust `1.98.1` `-Zbuild-std=std,panic_abort` profile and
//!      links it deterministically with bundled `rust-lld` and musl `self-contained` inputs
//!      (`--check-std-toolchain` verifies those toolchain pins standalone; see [`link`] and
//!      [`std_profile`]).
//!
//! # Key Types & Functions
//! - [`Cli`]: command-line flags.
//! - [`stock::run`]: stock `ld.lld` link + `census.json` recipe (`--stock`).
//! - [`link::run`]: pinned Rust `std` executable link recipe (`--main-rust`) and
//!   `--check-std-toolchain`.
//! - [`std_profile::StdToolchain`]: pinned `std` toolchain and sysroot SHA-256 checks.
//! - [`verify::check_std_elf`]: static-ELF loader invariant and symbol-bloat checks.
//!
//! # When to Read This File
//! - Read this file for the CLI flags and top-level dispatch.

mod census;
mod link;
mod std_profile;
mod stock;
mod stock_hooks;
#[cfg(test)]
mod stock_hooks_tests;
mod stock_std;
mod stock_std_audit;
#[cfg(test)]
mod stock_std_audit_tests;
#[cfg(test)]
mod stock_std_tests;
#[cfg(test)]
mod tests;
mod trimmed;
#[cfg(test)]
mod trimmed_tests;
mod verify;

use clap::Parser;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(
    name = "snapshot-link",
    about = "Link translation.toml objects with stock ld.lld (--stock) or build a pinned \
             static AArch64 Rust std executable (--main-rust)",
    after_help = "Examples:\n  snapshot-link --stock --config Implementation/translation.toml \\\n    \
                  --main-c Implementation/main.c --out-dir out --name my_cli.elf\n  \
                  snapshot-link --check-std-toolchain\n  \
                  snapshot-link --main-rust Implementation/my_app/Cargo.toml --out-dir out --name my_app.elf"
)]
pub struct Cli {
    /// `translation.toml` whose extracted objects are linked under `--stock` (repeatable).
    #[arg(long)]
    pub config: Vec<PathBuf>,
    /// Repository root (default: current directory).
    #[arg(long, default_value = ".")]
    pub repo_root: PathBuf,
    /// Output directory (gets the executable, manifest JSON, and `work/` intermediates).
    #[arg(long, default_value = "", hide_default_value = true, value_parser = parse_out_dir)]
    pub out_dir: PathBuf,
    /// File name of the executable inside `--out-dir`.
    #[arg(long, default_value = "prog")]
    pub name: String,
    /// C source of `main` under `--stock` (default: `int main(void) { return 0; }`).
    #[arg(long, conflicts_with = "main_rust")]
    pub main_c: Option<PathBuf>,
    /// Cargo `Cargo.toml` building either a Rust `staticlib` driver (with `--stock`) or a safe
    /// Rust `std` binary crate (`aarch64-unknown-linux-musl`). Both forms also work with `--stock`.
    #[arg(long, conflicts_with = "main_c")]
    pub main_rust: Option<PathBuf>,
    /// Verify the pinned Rust 1.98.1 compiler, `rust-src`, bundled `rust-lld`, and musl
    /// `self-contained` SHA-256 digests, print confirmation, and exit 0.
    #[arg(long)]
    pub check_std_toolchain: bool,
    /// Stock link: pass the unmodified extracted objects of every `--config`, `main`, and the
    /// musl runtime to `ld.lld` with its default layout (no linker script, relaxation on, no
    /// pinned bases), then write `<name>`, `stock-link.json`, and the relocation-site census
    /// `census.json` (see [`census`]).
    #[arg(long)]
    pub stock: bool,
    /// Extra argument appended to the `--stock` `ld.lld` command line (repeatable), e.g.
    /// `--stock-lld-arg=--icf=all`. Files it names (`-T<f>`, `-T <f>`, `--script <f>`,
    /// `--opt=<f>`, `<f>`) are hashed into `stock-link.json`; `@<f>`, `-L`, `-l` are rejected.
    #[arg(long, requires = "stock", allow_hyphen_values = true)]
    pub stock_lld_arg: Vec<String>,
    /// With `--stock`: make every global function or object the library objects define a
    /// `--gc-sections` root (`--undefined=<sym>`), so the whole library survives (with its layout
    /// as a contiguous block) while the runtime is still garbage-collected.
    #[arg(long, requires = "stock")]
    pub stock_keep_library: bool,
    /// With `--stock`: a native relocatable AArch64 object (e.g. a `.S` shim assembled to `.o`)
    /// linked as is (repeatable). Each is copied to `work/native/<file name>` and recorded with
    /// its SHA-256 and `"kind": "nativeObject"` in `stock-link.json` `inputs[]`.
    #[arg(long, requires = "stock")]
    pub stock_native_object: Vec<PathBuf>,
    /// With `--stock` and a Rust `std` binary `--main-rust`: take rustc's musl `self-contained`
    /// runtime (`crt1.o`, `crti.o`, `crtbegin.o`, `libc.a`, `libunwind.a`, `crtend.o`,
    /// `crtn.o`) from this directory instead of the pinned sysroot's
    /// `lib/rustlib/aarch64-unknown-linux-musl/lib/self-contained/`. Every file must still have
    /// its pinned SHA-256.
    #[arg(long, requires = "stock")]
    pub stock_self_contained_dir: Option<PathBuf>,
}

fn parse_out_dir(s: &str) -> Result<PathBuf, std::convert::Infallible> {
    Ok(PathBuf::from(s))
}

fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();
    if cli.stock {
        return stock::run(&cli);
    }
    link::run(cli)
}
