# `rust-obj2lean`

## 1. Introduction

`rust-obj2lean` is the host Rust CLI and library that bridges compiled AArch64 ELF relocatable object files (`.o`) and the Lean 4 verification engine. Given a [`translation.toml`](#translationtoml) configuration for a Rust crate workspace or C library, it:

1. **Orchestrates deterministic AArch64 compilation (`[UNTRUSTED]`)**: compiles Rust crates (`cargo rustc --target aarch64-unknown-linux-gnu -- --emit=obj`) or C translation units and static archives (`zig cc -target aarch64-linux-musl` with [`NATIVE_CFLAGS`](#sysroot-objects-sysroot_objects-and-pure-c-libraries-native_objects)) and selects reachable sections from sysroot `.rlib`s (`untrusted_driver/`).
2. **Parses ELF64 `.o` bytes (`[TCB]`) and emits placed libraries (`[OUTSIDE TCB]`)**: parses allocated ELF64 sections, symbol tables, and `RELA` relocations (`trusted_extractor/`, optionally emitting pre-link `<ObjName>ExtractedObj.lean` directly from `.o` bytes), resolves external symbols under the [Q1 rule](#external-symbols) (`untrusted_driver/externs.rs`), and emits `<ObjName>PlacedObj.lean` (`Obj.PlacedLib` / `Obj.MultiPlacedLib`), `<ObjName>ElfObj.lean`, and `<ObjName>PlacedWitness.lean` (via `untrusted_placed/`).
3. **Provides symbolic execution, DWARF layout, and decode-lemma tooling (`[UNTRUSTED]`)**: powers the sub-5ms `rust-obj2lean symexec` symbolic execution & CFG advisor (`untrusted_lemmas/symexec/`), DWARF layout inspection (`untrusted_lemmas/dwarf/`), prologue frame inference & `*Index.json` sidecar schema (`untrusted_lemmas/index.rs`, `untrusted_lemmas/index_schema.rs`), and standalone `fetch-decode-lemmas` (`untrusted_lemmas/mod.rs`).

Specifications (`Spec/Top.lean`) depend **only** on the generated `*PlacedObj.lean` / `*ExtractedObj.lean` / `*ElfObj.lean` module (`PlacedLib.Placeable`, `PlacedLib.subroutineOk`, `PlacedLib.LinkedIn`, `LabelsFromObjects`), never on `*PlacedWitness.lean` or `*ElfFacts.lean`.

### Module Architecture & Line Counts

By factoring build-driver orchestration, compiler/archive invocation, reachability pruning (`root_section_closure`), Q1 `ExternDecl` synthesis (`untrusted_driver/externs.rs`), and placed-library / placement-witness emission (`untrusted_placed/`) outside the TCB, the Trusted Computing Base (`trusted_common` + `trusted_extractor` + `lib.rs`) is restricted to pure in-memory ELF64 `.o` parsing, symbol disambiguation & collision checking, and pre-link `Obj.ExtractedObj` emission. Unit tests of the `[TCB]` modules live in separate `tests.rs` files, which `check-trust-guards` classifies as `testing` (it rejects inline `#[test]` / `#[cfg(test)] mod tests { ... }` code in `tcb` files):

| Module / File | Trust Role | Responsibility |
| :--- | :--- | :--- |
| [`src/main.rs`](./src/main.rs) | `[UNTRUSTED]` | Thin binary entry point delegating to `untrusted_driver::pipeline::cli_main`. |
| [`src/lib.rs`](./src/lib.rs) | `[TCB]` (module glue only) | Declares the module tree; contains no logic. |
| [`src/untrusted_driver/pipeline.rs`](./src/untrusted_driver/pipeline.rs) | `[UNTRUSTED]` | Top-level CLI dispatch (`export`, `fetch-decode-lemmas`, `symexec`, `print-cflags`, `layout`), `generate_config_with` pipeline sequencing (`[placed]` + optional `ExtractedObj`), and `--check` diffing. |
| [`src/tests.rs`](./src/tests.rs) | `[TEST ONLY]` | Crate-level tests: `translation.toml` loading, CLI flags, `--check` diffing, end-to-end C archive builds, and TCB import-isolation tests. |
| [`src/trusted_common/mod.rs`](./src/trusted_common/mod.rs) | **`[TCB]`** | Core relocatable ELF64 & relocation IR (`SecKind`, `RelocType`, `ObjReloc`, `ComdatGroup`, `ObjSection`, `SymSection`, `SymKind`, `SymBind`, `ObjSymbol`, `ObjObject`), `ExternKind`/`ExternDecl`/`Extraction`, `ObjModuleMeta`, `lean_string_lit`, and `sha256_hex`. |
| [`src/trusted_extractor/mod.rs`](./src/trusted_extractor/mod.rs) | **`[TCB]`** | Pure in-memory ELF64 AArch64 `.o` byte parser (`parse_elf_rel`, `parse_object_with`, `parse_c_object`, `Trim`) and symbol disambiguation & collision checks (`disambiguate_symbol_names`, `check_name_collisions`). |
| [`src/trusted_extractor/extracted_obj.rs`](./src/trusted_extractor/extracted_obj.rs) | **`[TCB]`** | Pre-link `<ObjName>ExtractedObj.lean` (`List Obj.ExtractedObj`) and `.bin` sidecar emitter directly from `Extraction::objects` without invoking a static linker (`--extracted-obj` / `[placed] emit_extracted_obj = true`). |
| [`src/trusted_extractor/tests.rs`](./src/trusted_extractor/tests.rs) | `[TEST ONLY]` | Unit tests for `trusted_extractor` and Q1 extern synthesis. |
| [`src/untrusted_placed/`](./src/untrusted_placed/mod.rs) | `[UNTRUSTED]` | Layout-generic `Obj.PlacedLib` / `Obj.MultiPlacedLib` extraction, `PlacedObj`/`ElfObj`/`PlacedWitness`/`ElfFacts` emission, and tests. |
| [`src/untrusted_driver/config.rs`](./src/untrusted_driver/config.rs) | `[UNTRUSTED]` | `clap` CLI (`Cli`, `CommandName`), `translation.toml` serde schema & validator (`load_config`, `load_configs`, `select_configs`, `apply_overrides`), and deterministic compiler flags (`DETERMINISTIC_CODEGEN_FLAGS`, `NATIVE_CFLAGS`). |
| [`src/untrusted_driver/mod.rs`](./src/untrusted_driver/mod.rs) | `[UNTRUSTED]` | Build driver (`Toolchain`, `build_crate_object`, `extract_native_object`), `[upstream]` git/symlink management, reproducible path remapping (`path_remaps`, `check_no_host_paths`), `.rlib`/`.a` archive unpacking (`scan_rlib_definitions`, `extract_c_archive_objects`), and `root_section_closure` reachability selector. |
| [`src/untrusted_driver/externs.rs`](./src/untrusted_driver/externs.rs) | `[UNTRUSTED]` | Untrusted Q1 `ExternDecl` synthesis (`needed_externs`, `resolve_externs_with_config`, `check_extern_collisions`) consumed by `untrusted_driver::extract` and `spec-oracle`. |
| [`src/untrusted_lemmas/mod.rs`](./src/untrusted_lemmas/mod.rs) | `[UNTRUSTED]` | `lemma_allowlist` regex matching (`lemma_patterns`, `name_selected`), bitfield/literal helpers, shard naming, and standalone `fetch-decode-lemmas` subcommand. |
| [`src/untrusted_lemmas/index.rs`](./src/untrusted_lemmas/index.rs) | `[UNTRUSTED]` | Infers function prologue stack frames (`infer_prologue_frame`) and re-exports the `*Index.json` sidecar schema & discovery helpers ([`src/untrusted_lemmas/index_schema.rs`](./src/untrusted_lemmas/index_schema.rs)). |
| [`src/untrusted_lemmas/symexec/`](./src/untrusted_lemmas/symexec/mod.rs) | `[UNTRUSTED]` | Sub-5ms multi-path AArch64 symbolic execution engine & CFG/loop advisor (`insn_semantics.rs`, `atomics.rs`, `expr.rs`, `state.rs`, `driver.rs`, `emit.rs`, `source.rs`, `mod.rs`). |
| [`src/untrusted_lemmas/dwarf/`](./src/untrusted_lemmas/dwarf/mod.rs) | `[UNTRUSTED]` | `gimli` DWARF reader (`mod.rs`), `-g2` companion C recompiler (`companion.rs`), `layout` subcommand (`cli.rs`), and tests (`tests.rs`). |
| [`src/test_infra/`](./src/test_infra/mod.rs) | `[TEST ONLY]` | `#[cfg(test)]` differential test harnesses comparing `Placed.lean` ([`placed_lld_diff.rs`](./src/test_infra/placed_lld_diff.rs)) against stock `ld.lld` & `placed_eval`, and `symexec` against Unicorn ([`symexec_diff.rs`](./src/test_infra/symexec_diff.rs)). |

---

## 2. Trusted Components (`[TCB]`)

The `[TCB]` modules (`trusted_common`, `trusted_extractor`, and `lib.rs`) parse in-memory ELF64 `.o` byte slices into `ObjObject` / `Extraction` records, verify defined-symbol collision invariants, and optionally emit pre-link `<ObjName>ExtractedObj.lean` modules (`List Obj.ExtractedObj`) directly from `.o` bytes without invoking a static linker. A unit test (`tcb_modules_never_import_untrusted_lemmas` in [`src/tests.rs`](./src/tests.rs)) statically verifies that `[TCB]` modules never reference `untrusted_*` modules, `std::process::Command`, `cargo_metadata`, `ArchiveFile`, `root_section_closure`, instruction decoding, or `theorem ` declarations.

### 2.1 `trusted_common` — Core ELF & Relocation IR ([`src/trusted_common/mod.rs`](./src/trusted_common/mod.rs))

`trusted_common` defines the pure data structures produced by `trusted_extractor`:

- **Section Classification (`SecKind`, `ALLOWED_SHF`, `is_relro_data`)**: Classifies allocated ELF sections (`SHF_ALLOC`, excluding `.eh_frame`) into `Text` (`SHT_PROGBITS`, `SHF_EXECINSTR`, non-writable, non-TLS), `Rodata` (read-only `SHT_PROGBITS`, `.data.rel.ro*`, and `SHT_INIT_ARRAY`/`SHT_FINI_ARRAY`/`SHT_PREINIT_ARRAY`), `Data` (writable `SHT_PROGBITS`), `Bss` (writable `SHT_NOBITS`), `Tdata` (`SHF_TLS` `SHT_PROGBITS`), and `Tbss` (`SHF_TLS` `SHT_NOBITS`). Sections with flags outside `ALLOWED_SHF` (e.g. `SHF_GROUP` COMDAT sections or `SHF_WRITE | SHF_EXECINSTR` W^X violations) fail closed during placement/linking.
- **AArch64 Relocation IR (`RelocType`, `ObjReloc`)**: Maps raw ELF `R_AARCH64_*` numbers to typed variants (`Call26`, `Jump26`, `Condbr19`, `Tstbr14`, `LdPrelLo19`, `AdrPrelLo21`, `AdrPrelPgHi21`, `AdrPrelPgHi21Nc`, `AddAbsLo12Nc`, `Ldst{8,16,32,64,128}AbsLo12Nc`, `Abs64`, `Abs32`, `Prel64`, `Prel32`, `Plt32`, `AdrGotPage`, `Ld64GotLo12Nc`, `Tlsie*`, `Tlsle*`, `Tlsdesc*`, etc.), with unknown numbers preserved as `RelocType::Other(u32)` so emitters fail closed if encountered.
- **Relocatable Object IR (`ObjSection`, `ObjSymbol`, `ComdatGroup`, `ObjObject`)**: Holds 1-to-1 extracted sections (with sorted `ObjReloc`s), symbol table entries (both raw mangled `.strtab` names and demangled names), `SHT_GROUP` COMDAT group headers, and raw `.o` bytes for SHA-256 provenance.
- **External Declarations & Module Metadata (`ExternKind`, `ExternDecl`, `ConfiguredExtern`, `Extraction`, `ObjModuleMeta`)**: Describes resolved external symbols (`Func`, `Object`, `Tls`) and target Lean module metadata.

### 2.2 `trusted_extractor` — Pure ELF64 `.o` Parser & Collision Checker ([`src/trusted_extractor/`](./src/trusted_extractor/mod.rs))

`trusted_extractor` accepts pre-loaded `.o` byte buffers (and optional section-index `Trim` masks) and performs three pure transformations:

1. **ELF64 Relocatable Object Parsing (`parse_elf_rel`, `parse_object`, `parse_object_with`, `parse_c_object`)**:
   - Enforces that the input is a little-endian 64-bit ELF (`ELFCLASS64`, `ELFDATA2LSB`) relocatable object (`ET_REL`) targeting `EM_AARCH64` with a non-empty `SHT_SYMTAB`.
   - Rejects `.gcc_except_table*` unwinding sections (requiring `panic=abort`), non-power-of-two or `> 4096`-byte section alignments (`check_align`), `SHT_NOBITS` sections carrying relocations, relocation tables not linked to `SHT_SYMTAB`, out-of-range symbol indices (`sym >= symbols.len()`), and out-of-range section offsets (`offset >= section.size`).
   - Sorts each section's relocations stably by ascending byte offset (`r.offset`).
   - When an optional `Trim` mask (`keep: BTreeSet<usize>`) is supplied for a sysroot `.rlib` object, `parse_object_with` retains only sections in `trim.keep` and re-indexes the symbol table. **Fail-closed trim invariant:** if any relocation in a kept section references a `STB_LOCAL` symbol defined in a dropped section, `parse_object_with` immediately returns an error; if it references a global/weak symbol in a dropped section, that symbol is rewritten to `SymSection::Undef` so it must be resolved by name like any other undefined symbol.
2. **Symbol Disambiguation & Collision Checks (`disambiguate_symbol_names`, `check_name_collisions`)**:
   - Groups non-local (`STB_GLOBAL`/`STB_WEAK`) symbols across all objects by demangled name; if distinct mangled `raw_name`s demangle to the same string (e.g. Rust v0 disambiguators or multiple crate versions), suffixes `#1`, `#2`, ... are assigned deterministically to each `raw_name` across both definitions and undefined references.
   - Suffixes `STB_LOCAL` C symbols with ` [<obj_name>]` (and `#1`, `#2`, ... for intra-object duplicates such as function-scoped `static` variables) and `STB_LOCAL` Rust symbols that collide with another symbol with ` [local#1]`, ` [local#2]`, ....
   - `check_name_collisions` then enforces that every defined function, object, or TLS entity across all objects has a strictly unique demangled name.
3. **Pre-Link `Obj.ExtractedObj` Emission (`extracted_obj.rs`: `render_extracted_obj_module`, `emit_extracted_obj_module`)**:
   - Emits `<ObjName>ExtractedObj.lean` (`List Obj.ExtractedObj`) and its `<ObjName>ExtractedObj.bin` sidecar directly from `Extraction::objects` without invoking any static linker, feeding the kernel-checked `LabelsFromObjects` relation in `Arm64.Trusted.Object.Labels`.

---

## 3. Untrusted Components (`[UNTRUSTED]`)

Everything outside `trusted_common`, `trusted_extractor`, and `lib.rs` is outside the TCB (`untrusted_driver/`, `untrusted_placed/`, and `untrusted_lemmas/`):

### 3.0 Placed-Library & Placement-Witness Emitter ([`src/untrusted_placed/`](./src/untrusted_placed/mod.rs))

`untrusted_placed` extracts layout-generic `Obj.PlacedLib` and `Obj.MultiPlacedLib` descriptions from `Extraction::objects` and emits `<ObjName>PlacedObj.lean`, `<ObjName>ElfObj.lean`, `<ObjName>PlacedWitness.lean`, and per-ELF `<Base>ElfFacts.lean` modules:

- **Layout-Generic Library Model (`model.rs`, `emit.rs`)**: Represents relocatable `.text` code blocks (`Obj.CodeBlock` with typed symbolic relocations) and per-symbol `.rodata` / `.data` / `.bss` / TLS data items (`Obj.SymDataInfo`), keeping `<ObjName>PlacedObj.lean` data-only (`Role::Spec`) with `.bin` byte sidecars spliced via `include_bytes%`.
- **Placement & Stock-ELF Linking Witnesses (`patch.rs`, `witness.rs`, `facts.rs`, `chunked.rs`)**: Synthesizes an `Obj.Placement` (either ELF-free via `Placeable` or anchored against a SHA-256-pinned stock-linked ELF via `LinkedIn`) and emits kernel-checked `Role::Proof` witness and ELF-facts modules (`decide +kernel` / `rfl_kernel`, optionally split into bounded-memory shard modules).

### 3.1 Build Driver, Config Loader, Extern Synthesis & Reachability Selector (`src/untrusted_driver/`)

[`src/untrusted_driver/config.rs`](./src/untrusted_driver/config.rs), [`src/untrusted_driver/mod.rs`](./src/untrusted_driver/mod.rs), and [`src/untrusted_driver/externs.rs`](./src/untrusted_driver/externs.rs) handle all filesystem I/O, CLI/TOML parsing, compiler execution, archive unpacking, section reachability selection, and Q1 `ExternDecl` synthesis around `trusted_extractor`:

- **CLI & `translation.toml` Config Loading (`config.rs`)**: Parses command-line flags (`Cli`, `CommandName`) and validates `translation.toml` files (`#[serde(deny_unknown_fields)]`), rejecting path escapes, duplicate object/target names, invalid flags, and zero-sized data/TLS externs, and projecting the 5-field `ObjModuleMeta` needed by the `Obj` renderer.
- **Compiler & Toolchain Orchestration (`mod.rs`)**:
  - Invokes `cargo rustc --release --lib --target aarch64-unknown-linux-gnu -- --emit=obj` with `DETERMINISTIC_CODEGEN_FLAGS` (`codegen-units=1`, `panic=abort`, `relocation-model=static`, `lto=off`, `-C no-vectorize-loops`, `-C no-vectorize-slp`, `--remap-path-prefix=...`) and verifies that no host filesystem paths leak into the `.o` (`check_no_host_paths`).
  - Invokes `zig cc` (checking the pinned `zig_version`) with `NATIVE_CFLAGS` or executes configured `build_script` / `build_command` recipes for pure-C libraries, and manages `[upstream]` git tag verification and `vendor/` symlinks.
- **Archive Unpacking & `root_section_closure` Reachability Pruning (`mod.rs`)**:
  - Unpacks `.a` static archives (`extract_c_archive_objects`), scans dependency and sysroot `.rlib` archives (`scan_rlib_definitions`) to collect candidate `RlibDef` metadata, and locates the sysroot `.rlib` member defining configured `[[sysroot_objects]]` root functions (`rlib_object_for_roots`).
  - Computes `root_section_closure(data, &roots) -> BTreeSet<usize>`: a breadth-first search over ELF sections starting from the sections that define `roots` and following relocations to sections that define referenced `STB_LOCAL` symbols (plus `.rodata`/`.data`/`.bss` sections referenced via `STT_SECTION` symbols).
- **Q1 External Symbol Resolution (`externs.rs`: `needed_externs`, `resolve_externs_with_config`, `check_extern_collisions`)**:
  - Scans relocations targeting `SymSection::Undef` symbols and synthesizes `ExternDecl` entries under the **Q1 rule** (see [External symbols](#external-symbols) below) against `.rlib` symbol metadata (`RlibDef`) and explicit `[[externs]]` overrides (`ConfiguredExtern`) for `untrusted_driver::extract` and `spec-oracle` (`untrusted_placed` and `trusted_extractor::extracted_obj` derive externs directly from `ObjObject` relocations without `Extraction::externs`).

#### External symbols

Undefined symbols of the objects become extern declarations (the "Q1 rule"):

- **functions** (`kind := .func`) — referenced only by `CALL26`/`JUMP26`, or also by address (`ADRP`/`ADD`, `ABS64`, GOT);
- **data objects** (`kind := .object`) — referenced by data relocations; size and alignment are taken from the defining object in the dependency / sysroot `.rlib`s, explicit `[[externs]]`, or inferred from the maximum relocation access width (`max_access_end.max(8)`);
- **TLS** (`kind := .tls`) — referenced by initial-exec TLS relocations (`R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21` / `R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC`).

Referencing a function with a load/store relocation or TLS relocation, or a data symbol with a branch, is an error. Defined and extern names (demangled) must be unique.

#### Why `untrusted_driver` Cannot Compromise Soundness (Fail-Closed Boundary)

1. **Compilers (`rustc`, `zig cc`) are outside the TCB**: Verification theorems are proved directly against the AArch64 machine code bytes embedded in `<ObjName>PlacedObj.bin` (and `<ObjName>ElfObj.lean`). A compiler bug or unexpected optimization changes the emitted machine code, which either still satisfies the Hoare specification or causes the Lean proof in `CaseStudies/` to fail during `lake build`.
2. **`root_section_closure` and archive selection fail closed in `[TCB]`** (dangling references only): `root_section_closure` only proposes a set of ELF section indices (`Trim::keep`) to `trusted_extractor::parse_object_with`. If `root_section_closure` ever omitted a section referenced by a kept section:
   - If the reference targets a `STB_LOCAL` symbol in the omitted section, `trusted_extractor::parse_object_with` rejects the object immediately (`a kept relocation refers to local symbol ... in a dropped section`).
   - If the reference targets a global/weak symbol in the omitted section, `trusted_extractor::parse_object_with` marks that symbol `SymSection::Undef`, and `untrusted_placed` either resolves it as an explicit external symbol or fails closed with an unresolved relocation error.
   - If a requested root symbol is missing (or defined more than once), `root_section_closure` itself bails. This check is a usability guard, not a soundness guard: the TCB does not check root coverage. A missing root only drops code from the library, so a public spec that names it (`PlacedLib.subroutineOk`, `MultiPlacedLib.LinkedIn`) fails to elaborate or prove instead of passing vacuously.

#### Reproducible paths

rustc embeds source paths in objects, e.g. in the panic `Location` of an `expect` in a
dependency or in an inlined `core`/`alloc`/`std` function. cargo passes absolute paths for
crates.io and git dependencies and for generated sources that a crate `include!`s from its
build script's `OUT_DIR` (e.g. code-generated `*.rs` modules). Moreover, when the `rust-src`
rustup component is installed at `<sysroot>/lib/rustlib/src/rust`, rustc rewrites
`/rustc/<commit-hash>/library/...` in precompiled `core`/`alloc`/`std` metadata to
`<sysroot>/lib/rustlib/src/rust/library/...` before applying `--remap-path-prefix`. Their length
shifts the rodata layout, and with it the relocated `adrp`/`add` immediates, so an image (and the
proofs about it) would depend on the build host and whether `rust-src` is installed. Path
packages below the workspace root are compiled with relative paths and are not affected.

Every Rust build therefore puts, before the configured `rustflags`:

| Host directory | Replaced by |
|---|---|
| `<CARGO_HOME>/registry/src` | `/cargo-registry` |
| cargo's target directory (from `cargo metadata`, so `CARGO_TARGET_DIR` and `build.target-dir` are honoured) | `/cargo-target` |
| `<CARGO_HOME>/git/checkouts` | `/cargo-git` |
| `<sysroot>/lib/rustlib/src/rust` (`<sysroot>` from `rustc --print sysroot`) | `/rustc/<commit-hash>` (`commit-hash:` from `rustc -vV`) |
| the `[upstream]` source directory, if any (absolute spellings only) | `/upstream/<name>/<commit>` (`<commit>` from `git rev-parse HEAD`) |

as `--remap-path-prefix=<dir>=<replacement>` in `RUSTFLAGS`, each directory as given and
canonicalized (if it goes through a symlink), in the order of the table, except that a directory
nested in another listed one comes after it (rustc applies the last matching prefix, so the
nested directory wins). The order does not depend on the directories' lengths, which differ
between hosts. `CARGO_HOME` is resolved as cargo does:
`$CARGO_HOME`, which must be absolute, else `$HOME/.cargo`; the provenance shows `CARGO_HOME` as
`$CARGO_HOME` and `<sysroot>` as `$SYSROOT`. The build fails if a remapped directory, the
sysroot, the crate directory or the upstream source directory (as given and canonicalized) still
occurs in a crate object. An object without such paths is unchanged by the remapping.

The generated provenance does not depend on where the repositories are checked out either. It
shows this repository as `$REPO`, the upstream source directory as `$<NAME>_SRC`, and, for a crate
outside this repository (e.g. in a superproject that has it as a submodule), the root of the
crate's own checkout (its nearest ancestor with a `.git`) as `$CRATE_REPO`; each host path is
replaced longest first, so a directory nested in another shows as its own placeholder. The crate
directory is shown relative to this repository, or else to its own checkout.

The upstream row also keeps cargo's cache honest. cargo treats a path dependency as fresh when
its source files are not newer than its last build, so retargeting a `vendor_symlink` (or
pointing `<NAME>_SRC`) at an older tree would reuse artifacts compiled from the previous tree;
generic functions instantiated in a downstream crate would then mix code from both. The flag
names the upstream directory and commit, and `RUSTFLAGS` are part of every unit's fingerprint,
so any change of upstream checkout rebuilds every unit.

#### `translation.toml`

```toml
crates = ["nsdemo"]            # default: the package in `crate_dir`
obj_name = "nsdemo0"           # Lean names: nsdemo0Lib, nsdemo0ExtractedObjs
namespace_prefix = "CryptoVerification"
hashed_inputs = ["Cargo.toml", "Cargo.lock", "src/lib.rs"]
# optional: crate_dir, obj_file, title, license_header, [upstream]

[placed]
multi = true
emit_extracted_obj = true
exports = ["encrypt_blob"]
```

Generated modules default to `<GeneratedDir>/<ObjName>PlacedObj.lean` (plus optional `<ObjName>ExtractedObj.lean`, `<ObjName>ElfObj.lean`, and `<ObjName>PlacedWitness.lean`). Unsupported fields
(`target_crate`, `symbol_allowlist`, `stub_*`, `link_*`, `emit_obj_dump`, `base_addr`,
`rodata_addr`, `words_def`) are rejected.

A `[placed]` table emits the layout-generic placed library (`<ObjName>PlacedObj.lean`), the
pinned ELF bytes (`<ObjName>ElfObj.lean`) and the placement witness
(`<ObjName>PlacedWitness.lean`); see the field docs of `PlacedTomlConfig` in
`src/untrusted_driver/config.rs`. With `linked = true`, the parsed ELF, its O(ELF)
kernel-checked parse theorem against the bytes constant and its symbol tables go in a Proof-role
`<Base>ElfFacts.lean`, named after the bytes constant (`myLibElfBytes` -> `MyLibElfFacts`). It is emitted once per distinct bytes constant and imported by every linked witness
about that constant, and each witness re-exports the facts under its own names (`<obj>Elf`,
`<obj>Elf_parse`, `<obj>ElfSyms`, `<obj>ElfSymChars`, `<obj>ElfSyms_eq`) as reducible aliases.
`[placed] elf_bytes` / `elf_bytes_module` name an existing bytes constant (e.g. a hand-written
Spec module) instead of emitting `<ObjName>ElfObj.lean`. `elf_facts_module = "<Base>ElfFacts"`
(on `[placed]` or `[[placed.extra_witnesses]]`) imports a facts module emitted by another config
in the same generated directory instead of emitting one. Generation fails closed unless that
module exists and its marker line records the same bytes constant, defining module and ELF
SHA-256. List every emitted `Generated/<Base>ElfFacts.lean` among the lakefile outputs.
A linked multi-block witness (`multi = true`) also proves, for each extern with exactly one
global defined `STT_FUNC` entry in the ELF's `.symtab` at its placed address,
`<p>_externSymtab : ∀ s ∈ [...], Obj.lookupUnique s <p>Elf.symbols = some (<mpl>.ρ s)` with one
`decide +kernel` (`Obj.Interned.externSymtab_of` in `ProofLib/Placed/ExternSymtab.lean`); the
docstring of `<p>ExternIds` lists the other externs and why each is left out.
`[placed] split_check_module = "<Module>"` (with `multi` and `linked`) names a Lean module whose
namespace of the same name provides `seg_lens%`, `rLen`, the chunked walks (`lTextChunk`,
`lTextTail`, `lTextChunks_cons` / `_nil`, and the same for `lData`), the per-check Bools
(`textPlaceableAllB`, `blocksDisjointB`, `blockSymsNodupB`, `dataPlaceableAllB`, `dataNotBlockB`,
`dataDisjointFastB`) and `checkMultiDisjoint_spec_chunks` (`ProofLib.Placed.Split`, or a module
that re-exports it). Each linked multi-block witness then proves `<p>_ok` from separate top-level
kernel facts (`<p>L_segLens_eq`, the text walk `<p>L_text` and data walk `<p>L_data`) and one
`decide +kernel` fact per segment-free check (`<p>L_chk_<check>`), instead of one
`decide +kernel` over `Obj.Interned.checkMultiDisjoint`. A walk whose code (or data) bytes, with
each relocation weighted as 16 bytes, exceed 32 KiB is split greedily into chunks of at most that
cost (`<p>L_text0`, `<p>L_text1`, ..., the last one a tail walk). The per-block symbol, text
placement and data-not-block checks are likewise split into index-range chunks
(`<p>L_chk_<check>0`, ...) proved with `allIdxChunk` / `allIdxTail` and composed by
`allIdxChunks_cons` / `_nil` and `<check>_of_chunks`, and the interned library equation is
proved as `toMultiPlacedLib_of_r (by rfl_kernel)` over the `List.rec`-based `toMultiPlacedLibR`
(which looks names up with `rGetD` rather than structural `List.getD`). The kernel's peak memory is then
that of the largest fact, which keeps multi-megabyte ELFs within the CI memory cap. The witness is
also split into sibling modules, each checked in its own Lean process:
`<…>PlacedWitnessShardDefs.lean` (the placement, interned library and layout, ELF aliases and
cheap facts), one `<…>PlacedWitnessShard<Fact>.lean` per heavy fact (`LibEq`, `SegLens`, `Text`
or `Text0`, `Text1`, ..., `Data` or `Data0`, ..., `Chk<Check>`, `ExternSymtab`), and
`<…>PlacedWitness.lean`, which imports them all and proves
`<p>_ok` and `<p>_linkedIn`. `cleanupStaleGeneratedFiles` keeps `<stem>Shard*.lean`
companions, so the lakefile lists only `<…>PlacedWitness.lean`.
`[placed] split_parse_module = "<Module>"` (with `elf` and `linked`) names a Lean module whose
namespace of the same name provides `suffix_of%`, `TailsOk`, `drop_of_rDrop`, `drop_chain`,
`length_of_drop`, `hdrOk`, `phdrsOf`, `symtabOf` and `parse_of_parts`. Each emitted facts module
then proves `<base>Image_parse` from separate top-level kernel facts instead of one `rfl_kernel`
over `ElfImage.fastParse`: suffix constants `<base>Image_tail<i>` of the bytes at the far offsets
the symbol-table parse seeks to (section headers, first global symbol, string table; read from the
ELF by the generator), each proved equal to a `List.drop` of the bytes, plus `<base>Image_length`,
`<base>Image_hdr`, `<base>Image_phdrs`, `<base>Image_symtab` and `<base>Image_wf`.
For a large multi-block library (`multi = true`),
`placed_shards = N` splits the code blocks over sibling modules
`<ObjName>PlacedObjShard0.lean` … `<ObjName>PlacedObjShard<N-1>.lean`, balanced by code size, so
that Lake elaborates them in parallel. Each shard defines its blocks' `include_bytes%` code
constants and a `<obj>BlocksShard<k> : List Obj.CodeBlock`. `<ObjName>PlacedObj.lean` imports the
shards and defines `<obj>Blocks` as their concatenation, so `<obj>Lib` is the same
`Obj.MultiPlacedLib` value. List the outputs in the lakefile as
`shardOutputs "Generated/<ObjName>PlacedObj" N` (plus the `.bin` sidecar). With the option
omitted or `1`, the output is unchanged.
For a large single-block library without a placement witness, `noncomputable_code = true` emits
`<obj>PlacedCode`, `<obj>Text` and `<obj>Lib` as `noncomputable def`s. Lean then skips compiling
the `include_bytes%` code literal, which takes time superlinear in its size; the kernel still
reduces these constants, so proofs are unaffected. `#guard` / `#eval` over the library and computable
definitions built on it are no longer available (check opcode coverage with kernel proofs instead).
The option is off by default and is rejected with `multi`, `elf`, `linked` or any witness key.

`extern_boundary = ["sym", ...]` (with `multi = true`) stops the reachability search from
`exports` at the named functions of the library (raw `.symtab` or demangled names). Their blocks,
and code reachable only through them, are left out of `<obj>Lib`, and direct calls (`CALL26` /
`JUMP26`) to them become ordinary externs under their raw names, placed from the ELF `.symtab`
like any other extern. Generation fails closed when a boundary name is an export, is not a
function defined in the library, is listed twice, shares its block with a reachable symbol, has
its address taken (a non-branch relocation in code or data), or lacks exactly one global defined
`STT_FUNC` entry in every witness ELF. The option changes only the emitted library data (fewer
blocks, more externs): the generator does not check that each boundary function is proved
elsewhere, typically as another config's export. A proof that composes the library must supply a
contract for each such extern, so the kernel enforces that obligation when the proof is closed.
With the option omitted, the output is unchanged.

`[upstream]` sources are located via `<NAME>_SRC`, then `~/sw/<name>`, then a fresh clone
(unless `<NAME>_NO_CLONE` is set). Under `lake`, `lakefile.lean` first runs
`scripts/fetch-upstream-sources.sh`, which checks out the pinned commit, verifies its tree
SHA-256, and passes `<NAME>_SRC` plus `<NAME>_NO_CLONE=1`. If you run `rust-obj2lean` outside
`lake`, set these yourself (`scripts/fetch-upstream-sources.sh --print-env` prints them).

##### Build flags (`rustflags`)

`rustflags = ["--cfg", "aes_backend=\"soft\""]` appends arguments (one per entry, no
whitespace) to the fixed `RUSTFLAGS` of the build, so they apply to every crate of the build,
dependencies included (e.g. to select a dependency's backend).

##### Sysroot objects (`[[sysroot_objects]]`) and pure-C libraries (`[[native_objects]]`)

Each `translation.toml` configures a **Rust** library (`crates` plus optional
`[[sysroot_objects]]`), a **pure-C** library (`[native_compiler]` plus `[[native_objects]]`,
`c_sources`, `c_objects`, or `c_archives`, with no `Cargo.toml` or `crates`; see
`Implementation/c-examples/translation.toml`), or a **mixed Rust + C** library when `crates = [...]`
is explicitly listed alongside C inputs (ordered `crates`, then C inputs, then `[[sysroot_objects]]`).

`[[sysroot_objects]]` extracts only the sections of a sysroot rlib member defining `roots`
(global functions or objects, matched by demangled or raw symbol name), closed under relocations
against local symbols via `untrusted_driver::root_section_closure` (with optional `name` when
extracting multiple members from the same multi-object sysroot rlib):

```toml
[[sysroot_objects]]        # a function from a sysroot rlib (e.g. liballoc)
crate = "alloc"
roots = ["alloc::raw_vec::RawVecInner<A>::grow_amortized"]
```

In a pure-C configuration, `[native_compiler]` and `[[native_objects]]`, `c_sources`,
`c_archives`, or `c_objects` compile or unpack C translation units:

```toml
obj_name = "my_lib"
build_script = "build.sh"                  # receives CC="zig cc", AR="zig ar", CFLAGS="..."
c_flags = ["-Iinclude", "-DHAVE_CONFIG_H"]
c_archives = ["build/libmy_lib.a"]         # extracts all `.o` members from the `.a` archive
c_objects = ["build/shim.o"]

[[externs]]                                # optional explicit extern symbol declarations
name = "custom_state"
kind = { data = 64 }                       # or "func", { tls = 16 }, etc.
```

Native objects are compiled with `NATIVE_CFLAGS` (`untrusted_driver/config.rs`:
`-target aarch64-linux-musl -O2 -fno-pic -fno-jump-tables -fno-common -ffunction-sections`, no
unwind tables, stack protector, or auto-vectorization; query via `rust-obj2lean print-cflags`).

---

### 3.2 Untrusted Proof & Analysis Tooling (`src/untrusted_lemmas/` & `src/test_infra/`)

`untrusted_lemmas/` provides prologue frame analysis, `*Index.json` sidecar deserialization, the fast symbolic execution advisor (`symexec`), DWARF source-annotation tools, and standalone `fetch-decode-lemmas`:

1. **Prologue Frame Inference & `*Index.json` Schema ([`untrusted_lemmas/index.rs`](./src/untrusted_lemmas/index.rs), [`untrusted_lemmas/index_schema.rs`](./src/untrusted_lemmas/index_schema.rs))**:
   - Infers downward prologue stack frame sizes (`infer_prologue_frame`, mirroring `inferPrologueFrameBytes?` in `ProofLib/PrologueFrame.lean`) and defines the `TargetSymbolIndex`, `FunctionIndexEntry`, and `CalleeInfo` JSON schema and discovery helpers (`symbol_index_paths`, `load_symbol_indices`) consumed by `symexec`, `dwarf`, and coverage tooling.
   - [`untrusted_lemmas/mod.rs`](./src/untrusted_lemmas/mod.rs) also provides `lemma_allowlist` regex matching (`lemma_patterns`, `name_selected`) and the standalone `rust-obj2lean fetch-decode-lemmas` CLI subcommand.
2. **Symbolic Execution & CFG Advisor ([`untrusted_lemmas/symexec/`](./src/untrusted_lemmas/symexec/mod.rs))**:
   - Executes AArch64 machine code symbolically in `< 5 ms` (`insn_semantics.rs`, `atomics.rs`, `expr.rs`, `state.rs`, `driver.rs`, `emit.rs`, `source.rs`), exploring basic-block CFGs, detecting loop headers, tracking stack-slot `(sp, offset)` reads/writes, and emitting human/JSON proof advice (`rust-obj2lean symexec` / `lean-sig symexec`) for authoring `*Sym.lean` symbolic execution and loop/CFG lemmas.
3. **DWARF Companion Build & Layout CLI ([`untrusted_lemmas/dwarf/`](./src/untrusted_lemmas/dwarf/mod.rs))**:
   - The trusted build always uses `-g0` so debug info never alters codegen. `dwarf/companion.rs` recompiles C translation units a second time with `-g0 -g2 -fdebug-prefix-map=...` and attaches function signatures, parameter locations, line tables, inlined call chains, and struct/union/bitfield layouts to `*Index.json` (with `exact: true` when the companion's function bytes match the trusted bytes). Set `RUST_OBJ2LEAN_NO_DWARF=1` to skip the companion build.
   - `dwarf/cli.rs` provides `rust-obj2lean layout <file.o | *Index.json | translation.toml> [FILTER] [--lean]`.
4. **Differential Test Infrastructure ([`src/test_infra/`](./src/test_infra/mod.rs), `#[cfg(test)]`)**:
   - [`placed_lld_diff.rs`](./src/test_infra/placed_lld_diff.rs) differentially tests `Arm64.Obj.Placed` (`placed_eval`) and `untrusted_placed` against stock `ld.lld` across synthetic relocation/relaxation suites, multi-TU C/Rust corpora, and every repository crate (`repo_crates_match_lld`).
   - [`symexec_diff.rs`](./src/test_infra/symexec_diff.rs) differentially tests `symexec::insn_semantics` against Unicorn (`UC_ARCH_ARM64`).

#### Why Bugs in `untrusted_placed` and `untrusted_lemmas` Can Only Cause Proof Rejection, Never Unsoundness

- **Zero axioms or trusted declarations**: `<ObjName>PlacedWitness.lean` and `<Base>ElfFacts.lean` are ordinary untrusted Lean modules (`Role::Proof` inputs) that contain **zero** `axiom`, `sorry`, or `native_decide` declarations. Every generated placement and ELF-parse theorem is proved by kernel reduction (`decide +kernel` / `rfl_kernel`) against trusted definitions in `Arm64/Trusted/`.
- **Specifications never import witness or advisor modules**: Trusted `Spec/Top.lean` files import only `<ObjName>PlacedObj.lean`, `<ObjName>ExtractedObj.lean`, or `<ObjName>ElfObj.lean` (enforced by `check-trust-guards`). If `untrusted_placed` emitted an invalid placement witness, Lean's kernel rejects the proof during `lake build`. Similarly, `symexec` and `dwarf` only produce developer advice and `*Index.json` hints; they cannot bypass the Lean kernel.

---

## 4. Usage

```sh
# Export one or more translation.toml configs (or verify they are up to date with --check):
cargo run --release --locked --manifest-path tools/Cargo.toml --bin rust-obj2lean -- \
  --config Implementation/examples/translation.toml [--out-dir DIR] [--only TARGET] [--check]

# Print verification-friendly C compiler flags for external build scripts:
cargo run --release --locked --manifest-path tools/Cargo.toml --bin rust-obj2lean -- print-cflags

# Run the symbolic execution & CFG advisor on an exported function:
cargo run --release --locked --manifest-path tools/Cargo.toml --bin rust-obj2lean -- \
  symexec Examples encrypt_blob

# Inspect DWARF struct/union layouts:
cargo run --release --locked --manifest-path tools/Cargo.toml --bin rust-obj2lean -- \
  layout <file.o | *Index.json | translation.toml> [NAME_FILTER] [--lean]

# Run the unit and differential test suite:
cargo test --locked --manifest-path tools/Cargo.toml -p rust-obj2lean
```
