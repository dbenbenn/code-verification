// Copyright 2026 Google LLC
//
// All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
// limitations under the License.

//! Static-ELF loader invariant and symbol-bloat checks (`[OUTSIDE TCB]`).
//!
//! # Purpose & Trust Role
//! - **Trust Role:** `[OUTSIDE TCB]` — an early, readable failure when a linked static ELF
//!   violates the structural invariants of `Arm64.Process.ElfImage.parse` or pulls in forbidden
//!   unwind/backtrace machinery. Soundness does not depend on this check: Lean proofs verify
//!   `ElfImage.parse` directly against the SHA-256-pinned ELF bytes.
//! - **Purpose:** [`check_std_elf`] verifies that a linked static AArch64 executable:
//!   - is little-endian `ET_EXEC` (`EM_AARCH64`) with a valid program header table and aligned
//!     non-zero `e_entry` inside an executable `PT_LOAD` segment;
//!   - carries no `PT_DYNAMIC` or `PT_INTERP` segments and no executable `PT_GNU_STACK`;
//!   - maps every non-empty `PT_LOAD` segment within `[0x1000, 2^48)` with 4 KiB page-congruent
//!     `p_vaddr` and `p_offset`, `W^X` permissions, explicit file zero-fill (`p_filesz == p_memsz`)
//!     on read-only segments, and pairwise disjoint page ranges;
//!   - includes a `PT_TLS` program header whenever any non-empty `SHF_TLS` section is present;
//!   - contains none of the forbidden unwind/backtrace symbol substrings (`gimli`,
//!     `_Unwind_Backtrace`, `sigaltstack`) in `.symtab` (except pure aliases listed in `exempt`
//!     under [`check_std_elf_exempting`]).
//!
//! # Key Types & Functions
//! - [`check_std_elf`], [`check_std_elf_exempting`], [`forbidden_symbols`],
//!   [`is_forbidden_name`]: static-ELF and symbol-bloat checks used by [`crate::stock`],
//!   [`crate::trimmed`], and [`crate::link`].
//!
//! # When to Read This File
//! - Read this file to see the static-ELF invariants checked after linking.

use crate::link::PAGE;
use anyhow::{Context, Result, bail, ensure};
use object::elf::{
    EM_AARCH64, ET_EXEC, PF_R, PF_W, PF_X, PT_DYNAMIC, PT_GNU_EH_FRAME, PT_GNU_PROPERTY,
    PT_GNU_RELRO, PT_GNU_STACK, PT_INTERP, PT_LOAD, PT_NOTE, PT_NULL, PT_PHDR, PT_TLS, SHF_TLS,
};
use object::read::elf::{ElfFile64, FileHeader, ProgramHeader};
use object::{Endianness, Object, ObjectSection, ObjectSymbol, SectionFlags};

/// Verify `Arm64.Process.ElfImage.parse` static-ELF invariants and the `panic = immediate-abort`
/// symbol-bloat audit on a linked static executable.
pub fn check_std_elf(elf_bytes: &[u8]) -> Result<()> {
    check_std_elf_exempting(elf_bytes, &[])
}

/// [`check_std_elf`], with the flagged names in `exempt` allowed where they are pure aliases
/// (see [`forbidden_symbols`]).
pub fn check_std_elf_exempting(elf_bytes: &[u8], exempt: &[String]) -> Result<()> {
    const USER_SPACE_LIMIT: u64 = 1u64 << 48;
    const PT_AARCH64_MEMTAG_MTE: u32 = 0x7000_0002;

    let elf = ElfFile64::<Endianness>::parse(elf_bytes).context("cannot parse std ELF64 binary")?;
    let e = elf.endian();
    ensure!(
        e == Endianness::Little,
        "std ELF check failed: expected little-endian (ELFDATA2LSB), got {e:?}"
    );
    let hdr = elf.elf_header();
    ensure!(
        hdr.e_type(e) == ET_EXEC,
        "std ELF check failed: expected static ET_EXEC ({ET_EXEC}), got e_type={}",
        hdr.e_type(e)
    );
    ensure!(
        hdr.e_machine(e) == EM_AARCH64,
        "std ELF check failed: expected EM_AARCH64 ({EM_AARCH64}), got e_machine={}",
        hdr.e_machine(e)
    );
    ensure!(
        hdr.e_phentsize(e) == 56 && hdr.e_phnum(e) > 0,
        "std ELF check failed: invalid program header table (e_phentsize={}, e_phnum={})",
        hdr.e_phentsize(e),
        hdr.e_phnum(e)
    );
    let entry = hdr.e_entry(e);
    ensure!(
        entry != 0 && entry % 4 == 0,
        "std ELF check failed: invalid e_entry={entry:#x} (must be non-zero and 4-byte aligned)"
    );

    let phdrs = hdr.program_headers(e, elf.data())?;
    let mut load_regions: Vec<(usize, u64, u64, bool)> = Vec::new();
    let file_len = elf_bytes.len() as u64;
    let mut has_tls_phdr = false;

    for (idx, p) in phdrs.iter().enumerate() {
        let ptype = p.p_type(e);
        match ptype {
            PT_DYNAMIC => bail!("std ELF check failed: PT_DYNAMIC segment is forbidden"),
            PT_INTERP => bail!("std ELF check failed: PT_INTERP segment is forbidden"),
            PT_GNU_STACK => {
                ensure!(
                    p.p_flags(e) & PF_X == 0,
                    "std ELF check failed: executable PT_GNU_STACK segment is forbidden"
                );
            }
            PT_TLS => {
                has_tls_phdr = true;
            }
            PT_NULL
            | PT_NOTE
            | PT_PHDR
            | PT_GNU_EH_FRAME
            | PT_GNU_RELRO
            | PT_GNU_PROPERTY
            | PT_AARCH64_MEMTAG_MTE => {}
            PT_LOAD => {
                let memsz = p.p_memsz(e);
                if memsz == 0 {
                    continue;
                }
                let vaddr = p.p_vaddr(e);
                let offset = p.p_offset(e);
                let filesz = p.p_filesz(e);
                let flags = p.p_flags(e);

                ensure!(
                    vaddr >= PAGE,
                    "std ELF check failed: PT_LOAD[{idx}] maps below {PAGE:#x} (p_vaddr={vaddr:#x})"
                );
                ensure!(
                    filesz <= memsz,
                    "std ELF check failed: PT_LOAD[{idx}] has p_filesz ({filesz:#x}) > p_memsz ({memsz:#x})"
                );
                ensure!(
                    offset
                        .checked_add(filesz)
                        .is_some_and(|end| end <= file_len),
                    "std ELF check failed: PT_LOAD[{idx}] file range [{offset:#x}, + {filesz:#x}) exceeds file length {file_len:#x}"
                );
                ensure!(
                    vaddr % PAGE == offset % PAGE,
                    "std ELF check failed: PT_LOAD[{idx}] p_vaddr ({vaddr:#x}) and p_offset ({offset:#x}) are not 4 KiB page-congruent"
                );
                let raw_end = vaddr.checked_add(memsz).ok_or_else(|| {
                    anyhow::anyhow!("std ELF check failed: PT_LOAD[{idx}] vaddr+memsz overflow")
                })?;
                let page_end = raw_end
                    .checked_add(PAGE - 1)
                    .map(|x| x & !(PAGE - 1))
                    .ok_or_else(|| {
                        anyhow::anyhow!("std ELF check failed: PT_LOAD[{idx}] page_end overflow")
                    })?;
                ensure!(
                    raw_end <= USER_SPACE_LIMIT && page_end <= USER_SPACE_LIMIT,
                    "std ELF check failed: PT_LOAD[{idx}] [{vaddr:#x}, {page_end:#x}) exceeds 48-bit user address space"
                );

                let r = flags & PF_R != 0;
                let w = flags & PF_W != 0;
                let x = flags & PF_X != 0;
                ensure!(
                    r || w || x,
                    "std ELF check failed: PT_LOAD[{idx}] has no R/W/X permissions"
                );
                ensure!(
                    !(w && x),
                    "std ELF check failed: PT_LOAD[{idx}] violates W^X (flags={flags:#x})"
                );
                if !w {
                    ensure!(
                        filesz == memsz,
                        "std ELF check failed: non-writable PT_LOAD[{idx}] has p_filesz ({filesz:#x}) != p_memsz ({memsz:#x})"
                    );
                }
                let page_start = vaddr & !(PAGE - 1);
                load_regions.push((idx, page_start, page_end, x));
            }
            other => bail!(
                "std ELF check failed: unsupported program header type {other:#x} at index {idx}"
            ),
        }
    }

    ensure!(
        !load_regions.is_empty(),
        "std ELF check failed: executable has no non-empty PT_LOAD segments"
    );
    load_regions.sort_by_key(|&(_, start, _, _)| start);
    for pair in load_regions.windows(2) {
        let (i0, s0, e0, _) = pair[0];
        let (i1, s1, e1, _) = pair[1];
        ensure!(
            e0 <= s1,
            "std ELF check failed: page-rounded PT_LOAD[{i0}] [{s0:#x}, {e0:#x}) overlaps PT_LOAD[{i1}] [{s1:#x}, {e1:#x})"
        );
    }
    ensure!(
        load_regions
            .iter()
            .any(|&(_, s, end, x)| x && s <= entry && entry + 4 <= end),
        "std ELF check failed: e_entry={entry:#x} does not lie inside an executable PT_LOAD segment"
    );

    for s in elf.sections() {
        let name = s.name().unwrap_or("?");
        if let SectionFlags::Elf { sh_flags } = s.flags()
            && sh_flags & u64::from(SHF_TLS) != 0
            && s.size() > 0
            && !has_tls_phdr
        {
            bail!("std ELF check failed: TLS section {name} present without PT_TLS");
        }
    }

    let bad_syms = forbidden_symbols(&elf, exempt);
    if !bad_syms.is_empty() {
        bail!(
            "std ELF symbol audit failed: found unwind/backtrace symbols in .symtab: {}",
            bad_syms.join(", ")
        );
    }
    Ok(())
}

/// The forbidden unwind/backtrace symbol substrings of the symbol-bloat audit.
const FORBIDDEN_SYMS: &[&str] = &["gimli", "_Unwind_Backtrace", "sigaltstack"];

/// Whether `name` contains a [`FORBIDDEN_SYMS`] substring.
pub(crate) fn is_forbidden_name(name: &str) -> bool {
    FORBIDDEN_SYMS.iter().any(|pat| name.contains(pat))
}

/// The symbols of `obj` whose names contain a [`FORBIDDEN_SYMS`] substring, sorted and
/// deduplicated, except the names in `exempt` that are pure aliases here: a flagged function or
/// object at the same section and address as a non-flagged defined function or object at least
/// as large (identical code folded under several names, which links no bytes of its own). A
/// flagged symbol that is not in `exempt`, or that owns any byte outside such a symbol, is still
/// reported.
pub(crate) fn forbidden_symbols<'d>(obj: &impl Object<'d>, exempt: &[String]) -> Vec<String> {
    let owners: Vec<_> = obj
        .symbols()
        .filter(|s| {
            s.is_definition()
                && matches!(
                    s.kind(),
                    object::SymbolKind::Text | object::SymbolKind::Data
                )
                && s.name()
                    .is_ok_and(|n| !n.is_empty() && !n.starts_with('$') && !is_forbidden_name(n))
        })
        .map(|s| (s.section_index(), s.address(), s.size()))
        .collect();
    let mut bad: Vec<String> = obj
        .symbols()
        .filter(|s| s.name().is_ok_and(is_forbidden_name))
        .filter(|s| {
            let alias = s.name().is_ok_and(|n| exempt.iter().any(|e| e == n))
                && s.is_definition()
                && s.section_index().is_some()
                && matches!(
                    s.kind(),
                    object::SymbolKind::Text | object::SymbolKind::Data
                )
                && owners.iter().any(|&(sec, a, size)| {
                    sec == s.section_index() && a == s.address() && size >= s.size()
                });
            !alias
        })
        .map(|s| s.name().unwrap_or("?").to_string())
        .collect();
    bad.sort();
    bad.dedup();
    bad
}
