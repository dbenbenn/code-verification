# `snapshot-link`: reproducible static AArch64 ELF linker (`[OUTSIDE TCB]`)

`snapshot-link` builds deterministic static AArch64 Linux `ET_EXEC` executables for whole-binary Lean verification and [`proc-snapshot`](../proc-snapshot/README.md). Nothing it produces is trusted: Lean proofs verify `Arm64.Process.ElfImage.parse` and `LinkedIn` / `MultiPlacedLib` placement witnesses directly against the SHA-256-pinned ELF bytes.

It provides two link recipes:

1. **Stock `ld.lld` link & relocation-site census (`--stock`)** — links the unmodified relocatable `.o` objects extracted by `rust-obj2lean` for one or more `translation.toml` configs with stock `ld.lld` defaults (`--gc-sections`, relaxation on, no linker script).
2. **Pinned Rust `std` binary link (`--main-rust <Cargo.toml>`)** — compiles and links a safe Rust `std` binary crate deterministically under the pinned Rust `1.98.1` `-Zbuild-std=std,panic_abort` profile and bundled `aarch64-unknown-linux-musl` `self-contained` runtime.

## Stock link and relocation-site census

`--stock` links extracted library objects with plain `ld.lld` defaults, producing the static executable that a placement-generic `Obj.PlacedLib` / `Obj.MultiPlacedLib` proof checks via `LinkedIn`:

```bash
snapshot-link --stock [--stock-keep-library] [--stock-lld-arg=<arg>]... \
  [--stock-native-object <obj.o>]... \
  --config <translation.toml>... \
  (--main-c <main.c> | --main-rust <staticlib Cargo.toml> \
   | --main-rust <std binary Cargo.toml> [--stock-self-contained-dir <dir>]) \
  --out-dir <dir> --name <exe>
```

- **Inputs.** The library objects are the exact relocatable objects `rust-obj2lean` extracts for
  each `--config`, unrenamed and with no stubs, linked in `--config` order. With `--main-c` or a
  `staticlib` `--main-rust`, they are combined with `main` and the musl runtime of a `zig cc`
  link.
- **Rust `std` binary `--main-rust`.** An ordinary safe Rust `std` binary crate is compiled to
  `work/main_rust.o` + `work/compiler_builtins.a`. The crate guards and the pinned
  `-Zbuild-std=std,panic_abort` profile are the same as in
  [Ordinary Rust `std` binary crates](#ordinary-rust-std-binary-crates). It is linked against
  **rustc's own musl `self-contained` runtime**, not `zig`'s musl. That runtime is `crt1.o`,
  `crti.o`, `crtbegin.o`, `libc.a`, `libunwind.a`, `crtend.o` and `crtn.o`, taken from the pinned
  sysroot's `lib/rustlib/aarch64-unknown-linux-musl/lib/self-contained/` or from
  `--stock-self-contained-dir <dir>`.
  - Before anything is built, each file must match its pinned SHA-256
    (`std_profile::SELF_CONTAINED_CHECKSUMS`). It is then copied unmodified to
    `work/self-contained/`.
  - Globals that `main_rust.o` and a `--config` object both define are weakened in `main_rust.o`,
    so the extracted definitions are the ones linked. The set is computed from the objects as
    emitted into `work/` (a trimmed sysroot object as its trim, not the whole member).
    `stock-link.json` lists them under `stdBin.weakenedInMain`.
  - `ld.lld` also writes `work/why-extract.tsv` (`--why-extract=`) and `work/link.map` (`-Map=`),
    and reports removed sections (`--print-gc-sections`). From them `stock-link.json` records
    `stdBin.archiveMembers`: every archive member lld extracted, the reference and symbol that
    extracted it, its input sections that survive `--gc-sections` with their sizes (`retained`),
    and those `--gc-sections` removed (`removed`).
  - The parser fails closed (`stock_std_audit::parse_members`). Both headers must match exactly,
    every map line must be an output-section, input-section or symbol line, at least one member
    must be extracted and at least one archive section retained, and every extracted member must
    retain or have removed at least one section. A changed `ld.lld` output format is an error,
    never an empty (vacuously passing) retained set.
  - **Unwind audit (fails closed).** `libunwind.a` members may be extracted (`rust_eh_personality`
    references `_Unwind_*`), but none of their sections may survive `--gc-sections`, and every
    `.symtab` name other than `STT_FILE` source names matching `stock_std_audit::UNWIND_DENY`
    (`_Unwind_*`, `__register_frame*`, `__deregister_frame*`, `unw_*`, `libunwind`) must be an
    entry of `UNWIND_ALLOW` in its allowed form. The only allowed entries are `crtbegin.o`'s weak
    undefined `__register_frame_info` / `__deregister_frame_info`, which link no code.
    `stdBin.unwindAudit.allowed` lists those present, with the reason.
  - For the hooked-extern check of trimmed sysroot objects, `compiler_builtins.a` counts as a Rust
    archive, not as part of the C runtime.
  - Link order:
    1. `crt1.o crti.o crtbegin.o`;
    2. native objects;
    3. library objects;
    4. `--start-group main_rust.o libc.a compiler_builtins.a libunwind.a --end-group`;
    5. `crtend.o crtn.o`.
- **`--stock-native-object <obj.o>` (repeatable).** A relocatable little-endian AArch64 ELF64
  object, for example an assembled `.S` shim. It is checked and copied to
  `work/native/<file name>`; file names must be distinct. It is linked after the startup objects
  and a C `main`, before the library objects. A strong symbol that collides with `main` or a
  library object is a link error. For the hooked-extern check of trimmed sysroot objects, a native
  object is a stub object: it may define a hooked extern (for example a hand-written shim).
- **Hooked externs of trimmed sysroot objects** (`stock_hooks.rs`). These are the externs of a
  `--config` that has a trimmed `[[sysroot_objects]]` entry.
  - Before the link, no non-runtime archive may define one. The single exception is an
    `STB_WEAK` archive definition of a name that a stub object defines `STB_GLOBAL`: an object's
    global definition always wins over a weak one. A weak stub never qualifies.
    `trimmedSysrootObjects.weakArchiveShadowed` lists these archive definitions.
  - A sibling `--config` image may define a hooked extern only under two conditions. The defining
    symbol must be one of that image's declared exports (`[placed] exports` or
    `[[sysroot_objects]] roots`, raw or demangled). Each export must resolve to exactly one
    defined symbol of the image. And the image must not list the name as an extern itself.
  - After the link, the `--trace-symbol` output must have exactly one `definition of` line per
    hooked extern, and it must come from a stub object, the C runtime, or the allowed sibling
    object.
  - A sibling-defined extern's executable address must equal the sibling's placed export address,
    which is the `-Map` address of its input section plus the symbol's offset.
    `trimmedSysrootObjects.siblingDefinedExterns` lists each one with its export, its image and
    its address.
  - `--stock-lld-arg` may not allow multiple definitions (`--allow-multiple-definition`,
    `-z muldefs`).
- **Flags.** `ld.lld` gets the flags in `stock::LLD_FLAGS`:
  `-static -no-pie --entry _start --gc-sections --eh-frame-hdr -z now --build-id=none --strip-debug`.
  Each flag is documented there.
- **Defaults kept.** There is no linker script, relaxation stays on, `--icf=none`, the page size is
  64 KiB, and the optimization level is `-O1`. With `-O2`, lld enables `--branch-to-branch` (a
  `bl f` becomes `bl g` when `f` starts with `b g`) and string tail merging.
- **`--stock-keep-library`.** Adds `--undefined=<sym>` for every global function or object the
  library defines. The whole library survives `--gc-sections` as one contiguous block, while
  unused runtime code is still dropped.
- **Output check.** The output must satisfy the trusted loader's static-ELF constraints
  (`verify::check_std_elf`).

The command writes three files:
- `stock-link.json`: provenance, input hashes, the lld version, arguments, log (`lld.log`) and map
  (`link.map`), segments and sections. It is reproducible. Every linked file is an `inputs[]`
  entry with its `sha256`. Native objects add `"kind": "nativeObject"`. rustc's self-contained
  runtime files add `"kind": "selfContained"` and `"pinnedSha256"`. A `std` binary link also
  records `stdBin` (`rustc`, `commit`, `llvm`, `selfContainedDir`, `weakenedInMain`, `rebuildKey`,
  `archiveMembers`, `unwindAudit`).
- `timing.json`: the lld wall time.
- `census.json`: the census, built by `census.rs`. It places every library input section in the
  executable using `.symtab` anchors, masked content search and `SHF_MERGE` pieces. It then
  classifies every relocation site against `untrusted_placed::patch` templates and `ld.lld`
  relaxations:
  - `exact`: the unrelaxed patched word (`patch_reloc_word`) or data relocation;
  - `adrpAddToNopAdr`, `gotToAdrpAdd`, `gotToNopAdr`, `gotUnrelaxed`: lld relaxations of
    `adrp` + `add` / GOT `ldr` pairs;
  - `branchViaThunk`, `branchToBranch`, `weakUndefBranch`;
  - `unresolved`, `unsupported`, `unmatched`.

  It also reports function survival and symbol visibility, ICF folds, the contiguity of library
  text and data, GOT slots, thunks and `.eh_frame`.

`scripts/dev/stock-link-fixture [--check]` regenerates or drift-checks committed stock-link fixtures across `CaseStudies/<Campaign>/`.

## Ordinary Rust `std` binary crates

When `--main-rust <Cargo.toml>` points to an ordinary safe Rust `std` binary crate (`src/main.rs`
or `[[bin]]`, without `--stock`):

```bash
snapshot-link --check-std-toolchain
snapshot-link --main-rust Implementation/my_app/Cargo.toml --out-dir out --name my_app.elf
```

- **Pinned toolchain & runtime:** Verifies `rustc 1.98.1` (`48a229ceaefd4985c50990b14116b6d856af0985`,
  LLVM `22.1.8`), `rust-src`, bundled `rust-lld`, and exact SHA-256 digests of the bundled
  `aarch64-unknown-linux-musl` `self-contained` files (`crt1.o`, `crti.o`, `crtbegin.o`, `libc.a`,
  `libunwind.a`, `crtend.o`, `crtn.o`), then stages stripped deterministic copies into `work/runtime/`.
- **Manifest & source guards:** Rejects `[patch]`, `.cargo/config*`, `build.rs`, native `.c`/`.h`/`.s`/`.S`
  files (excluding `vendor/`), `#![no_std]`, and missing `#![forbid(unsafe_code)]`, and requires
  `[profile.release]` with `opt-level = 2`, `codegen-units = 1`, and `lto = "fat"` (or `true`).
- **Build & link:** Compiles a single LTO object under `-Zbuild-std=std,panic_abort`,
  `-Cpanic=immediate-abort`, `-Crelocation-model=static`, deterministic codegen flags, and host-path
  remaps; links page-disjoint `W^X` segments with `rust-lld`; verifies `verify::check_std_elf`; and
  writes `link.json` (`schema = "snapshot-link/1"`, including `"stdProfile"`).

`scripts/dev/elf-process-fixture [--cp | --rust-std] [--check]` regenerates or drift-checks committed `std` binary fixtures.

## Tests

```bash
cargo test --locked --manifest-path tools/Cargo.toml -p snapshot-link
```
