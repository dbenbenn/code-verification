/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtAlloc -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Externs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtSubroutineProofs -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
import ProofLib.Placed.Split
import ProofLib.ProgramReflection
meta import ProofLib.ProgramReflection

/-!
# Crate-Local `<String as fmt::Write>` Placements (`c2MplAllocCli`), `seg[1]` Blocks, & `.rodata` Guards (`CliFmtRow.AllocRo`)
-/

set_option autoImplicit false
set_option maxRecDepth 4000000

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.AllocRo

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.ProgramReflection
open VerifiedLibraries.RustStd
  (allocBudgetHandleErrorSym allocMultiLib allocRustAllocSym allocRustNoAllocShimSym
   allocRustReallocSym allocStringWriteAddrs stringWriterKeep)
open VerifiedLibraries.RustStd.CoreFmt (LibBlockNoExtern)
open CryptoVerification (LibsignalPlacement LibsignalRoLoaded libsignalSessionLib_blocks_length lsmpl)
open CryptoVerification.SignalSession (cliElfBytes cliElfImage libsignalSessionLib)
open LibsignalBinary.Heap.AesDecErrRoBudget (cliAesDecErrStr1Addr cliAesDecErrStr2Addr)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (lsLen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.BlockWordTreeBase
  (checkRoSegSlice roSlice_of_checkRoSegSlice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtAlloc
  (c2AllocMpl c2_alloc_roDataAt_vtableWriteChar c2_alloc_roDataAt_vtableWriteFmt
   c2_alloc_roDataAt_vtableWriteStr c2_alloc_seg2_rx_blocks)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtCore
  (c2CoreFmtMpl c2_coreFmt_roDataAt_decDigitsLut)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Code
  (checkSeg1BlockWalk f3PatchedElf_roSeg_eq rxCode_of_c2FmtProg_codeLoaded seg1_blockCodeLoaded_of_walk)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Defs
  (c2FmtProg c2FmtProgTrap)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.Externs
  (c2FmtProg_externAt_none_of_lt_stub c2FmtProgTrap_externAt_of_ne list_getD_eq_getElem)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtGhostSpecs
  (CliFmtWriteVtableKind LsRetAddrFmtWrite isFmtWriteInternalBlock isFormatInnerInternalBlock)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.CliFmtSubroutineProofs
  (StringWriteVtableRoAt cliFmtWriteRoGuard cliFormatInnerRoGuard)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (f3CodeInv_roDataAt_of_checkSegSlice)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics (F3CodeInv)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfPlaced
  (cliElfBlockBases cliElfMultiPlacement cliElf_linkedAt_unique lsInternedMultiLib)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FirstExternStubAddr wp4HandleErrorAddr wp4MemcpyRealAddr wp4NoShimV2Addr)

attribute [local irreducible] c2FmtProg c2FmtProgTrap f3TrialRxProg

/-- Closed 0-hook stock-ELF `Obj.MultiPlacement` for each of the 3 crate-local copies of
    `allocMultiLib`'s `<String as core::fmt::Write>` vtable and methods (`B00, B01, B02, B06, B07, B08`)
    in `seg[1]`, sharing `B03..B05` and helper symbols with `c2AllocMpl`. -/
@[expose] noncomputable def c2MplAllocCli (k : CliFmtWriteVtableKind) : Obj.MultiPlacement where
  base i :=
    match k, i with
    | .libsignalSession, 0 => cliElfMultiPlacement.base 134
    | .libsignalSession, 1 => cliElfMultiPlacement.base 157
    | .libsignalSession, 2 => cliElfMultiPlacement.base 160
    | .libsignalSession, 6 => cliElfMultiPlacement.base 181
    | .libsignalSession, 7 => cliElfMultiPlacement.base 182
    | .libsignalSession, 8 => cliElfMultiPlacement.base 196
    | .cliRatchet, 0 => cliElfMultiPlacement.base 437
    | .cliRatchet, 1 => cliElfMultiPlacement.base 460
    | .cliRatchet, 2 => cliElfMultiPlacement.base 465
    | .cliRatchet, 6 => cliElfMultiPlacement.base 488
    | .cliRatchet, 7 => cliElfMultiPlacement.base 489
    | .cliRatchet, 8 => cliElfMultiPlacement.base 503
    | .cliHandshake, 0 => cliElfMultiPlacement.base 510
    | .cliHandshake, 1 => cliElfMultiPlacement.base 517
    | .cliHandshake, 2 => cliElfMultiPlacement.base 522
    | .cliHandshake, 6 => cliElfMultiPlacement.base 533
    | .cliHandshake, 7 => cliElfMultiPlacement.base 534
    | .cliHandshake, 8 => cliElfMultiPlacement.base 540
    | _, j => c2AllocMpl.base j
  ρ sym :=
    if sym == "rust_alloc:.data.rel.ro..Lanon.34" then
      cliElfMultiPlacement.ρ k.vtableSym
    else
      c2AllocMpl.ρ sym

set_option maxHeartbeats 2000000 in
theorem c2MplAllocCli_placeable (k : CliFmtWriteVtableKind) :
    allocMultiLib.Placeable (c2MplAllocCli k) := by
  cases k <;> exact allocMultiLib.placeable_of_checkPlaceable (by rfl_kernel)

theorem c2MplAllocCli_vtable_eq [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (k : CliFmtWriteVtableKind) :
    (allocStringWriteAddrs (c2MplAllocCli k)).vtable = k.vtableAddr := by
  have hmem : k.vtableSym ∈ lsInternedMultiLib.names := by
    cases k <;> exact List.contains_iff_mem.mp
      (by rfl_kernel : lsInternedMultiLib.names.contains _ = true)
  have hnone : Obj.lookupBlockSym k.vtableSym libsignalSessionLib.blocks = none := by
    cases k <;> rfl_kernel
  have hvt : (allocStringWriteAddrs (c2MplAllocCli k)).vtable =
      cliElfMultiPlacement.ρ k.vtableSym := by
    cases k <;> rfl_kernel
  exact hvt.trans ((cliElf_linkedAt_unique hLs).2.2.1 k.vtableSym hmem hnone).symm

theorem c2MplAllocCli_handleError_resolve (k : CliFmtWriteVtableKind) :
    allocMultiLib.resolve (c2MplAllocCli k) allocBudgetHandleErrorSym = wp4HandleErrorAddr := by
  cases k <;> rfl_kernel

theorem c2MplAllocCli_memcpy_resolve (k : CliFmtWriteVtableKind) :
    allocMultiLib.resolve (c2MplAllocCli k) "memcpy" = wp4MemcpyRealAddr := by
  cases k <;> rfl_kernel

theorem c2MplAllocCli_noAllocShim_resolve (k : CliFmtWriteVtableKind) :
    allocMultiLib.resolve (c2MplAllocCli k) allocRustNoAllocShimSym = wp4NoShimV2Addr := by
  cases k <;> rfl_kernel

theorem c2MplAllocCli_rustAlloc_resolve (k : CliFmtWriteVtableKind) :
    allocMultiLib.resolve (c2MplAllocCli k) allocRustAllocSym = wp4NoShimV2Addr - 16#64 := by
  cases k <;> rfl_kernel

theorem c2MplAllocCli_rustRealloc_resolve (k : CliFmtWriteVtableKind) :
    allocMultiLib.resolve (c2MplAllocCli k) allocRustReallocSym = wp4NoShimV2Addr - 8#64 := by
  cases k <;> rfl_kernel

set_option maxHeartbeats 2000000 in
private theorem c2MplAllocCli_writer_seg1_chk (k : CliFmtWriteVtableKind) :
    (([1, 2, 6, 7] : List Nat).all fun j =>
      checkSeg1BlockWalk allocMultiLib (c2MplAllocCli k) j) = true := by
  cases k <;> rfl_kernel

theorem c2MplAllocCli_stringWriter_codeLoaded (k : CliFmtWriteVtableKind) {m : Memory}
    (hL : c2FmtProg.CodeLoaded m) :
    allocMultiLib.CodeLoadedWhere stringWriterKeep (c2MplAllocCli k) m := by
  have hlen : allocMultiLib.blocks.length = 9 := by decide
  intro j hj hk
  rw [hlen] at hj
  have hmem : j ∈ ([1, 2, 6, 7] : List Nat) := by
    match j, hj, hk with
    | 1, _, _ | 2, _, _ | 6, _, _ | 7, _, _ => decide
    | 0, _, hk | 3, _, hk | 4, _, hk | 5, _, hk | 8, _, hk => cases hk
  exact seg1_blockCodeLoaded_of_walk
    (List.all_eq_true.mp (c2MplAllocCli_writer_seg1_chk k) j hmem) hL

set_option maxHeartbeats 2000000 in
private theorem c2_alloc_seg1_blk4_ok :
    checkSeg1BlockWalk allocMultiLib c2AllocMpl 4 = true := by
  rfl_kernel

theorem c2AllocMpl_codeLoaded_of_c2FmtProg {m : Memory} (hL : c2FmtProg.CodeLoaded m) :
    allocMultiLib.CodeLoaded c2AllocMpl m := by
  have hlen : allocMultiLib.blocks.length = 9 := by decide
  intro j hj
  rw [hlen] at hj
  by_cases h4 : j = 4
  · subst h4
    exact seg1_blockCodeLoaded_of_walk c2_alloc_seg1_blk4_ok hL
  · exact codeLoaded_of_checkProgCodeSubslice
      (rxCode_of_c2FmtProg_codeLoaded hL) (c2_alloc_seg2_rx_blocks hj h4)

/-! ### Low-RSS Disjointness of Caller `lr` from Internal `seg[1]` Blocks via `cliElfBlockBases` & `lsLen` -/

@[expose] def c2FmtWriteInternalIndices : List Nat :=
  [121, 157, 160, 181, 182, 191, 214, 216, 217,
   460, 465, 488, 489, 498, 517, 522, 533, 534, 537]

@[expose] def c2FormatInnerInternalIndices : List Nat :=
  [78, 121, 157, 160, 170, 181, 182, 191, 214, 215, 216, 217,
   392, 393, 394, 395, 396, 397, 412, 460, 465, 477, 488, 489, 498,
   517, 522, 529, 533, 534, 537, 623]

@[expose] def checkBlocksDisjointAux (skip : Nat → Bool) (pairs : List (Nat × Nat)) :
    Nat → List (BitVec 64) → Bool
  | _, [] => true
  | j, b :: bs =>
    (skip j ||
      pairs.all fun (bbi, lbi) =>
        Nat.ble (b.toNat + lsLen j) bbi || Nat.ble (bbi + lbi) b.toNat) &&
    checkBlocksDisjointAux skip pairs (j + 1) bs

private theorem checkBlocksDisjointAux_spec {skip : Nat → Bool} {pairs : List (Nat × Nat)} :
    ∀ (j : Nat) (bs : List (BitVec 64)),
      checkBlocksDisjointAux skip pairs j bs = true →
      ∀ (k : Nat) (hk : k < bs.length),
        skip (j + k) = true ∨
        ∀ p ∈ pairs, bs[k].toNat + lsLen (j + k) ≤ p.1 ∨ p.1 + p.2 ≤ bs[k].toNat
  | _, [], _, _, hk => nomatch hk
  | j, b :: bs, h, 0, _ => by
    simp only [checkBlocksDisjointAux, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h.1 with hs | hall
    · exact Or.inl hs
    · refine Or.inr fun p hp => ?_
      rcases p with ⟨bbi, lbi⟩
      have hp0 := List.all_eq_true.mp hall (bbi, lbi) hp
      simp only [Bool.or_eq_true, Nat.ble_eq] at hp0
      exact hp0
  | j, _ :: bs, h, k + 1, hk => by
    simp only [checkBlocksDisjointAux, Bool.and_eq_true] at h
    have ih := checkBlocksDisjointAux_spec (j + 1) bs h.2 k (Nat.lt_of_succ_lt_succ hk)
    simpa [Nat.add_right_comm, Nat.add_assoc] using ih

@[expose] noncomputable def c2InternalPairsOf (idxs : List Nat) : List (Nat × Nat) :=
  idxs.map fun bi => ((cliElfBlockBases.getD bi 0#64).toNat, lsLen bi)

set_option maxHeartbeats 2000000 in
theorem c2_disjoint_fmtWrite_ok :
    checkBlocksDisjointAux isFmtWriteInternalBlock
      (c2InternalPairsOf c2FmtWriteInternalIndices) 0 cliElfBlockBases = true := by
  rfl_kernel

set_option maxHeartbeats 2000000 in
theorem c2_disjoint_formatInner_ok :
    checkBlocksDisjointAux isFormatInnerInternalBlock
      (c2InternalPairsOf c2FormatInnerInternalIndices) 0 cliElfBlockBases = true := by
  rfl_kernel

-- Exact code-length check on the 19 small `libsignalSessionLib` formatter blocks (`≤ 328` B).
set_option maxHeartbeats 2000000 in
theorem c2_lsSub_codeLen_eq_lsLen :
    (([78, 121, 170, 191, 214, 215, 216, 217,
       392, 393, 394, 395, 396, 397, 412, 477, 498, 529, 537] : List Nat).all fun bi =>
      Nat.beq (libsignalSessionLib.blockLib bi).text.code.length (lsLen bi)) = true := by
  rfl_kernel

-- Exact code-length check on the 12 crate-local `<String as fmt::Write>` blocks of `allocMultiLib`.
set_option maxHeartbeats 2000000 in
theorem c2_allocWriter_codeLen_eq_lsLen :
    (([(1, 157), (2, 160), (6, 181), (7, 182),
       (1, 460), (2, 465), (6, 488), (7, 489),
       (1, 517), (2, 522), (6, 533), (7, 534)] : List (Nat × Nat)).all fun (aj, bi) =>
      Nat.beq (allocMultiLib.blockLib aj).text.code.length (lsLen bi)) = true := by
  rfl_kernel

set_option maxHeartbeats 2000000 in
private theorem c2_bases_bounds_chk :
    (Nat.beq cliElfBlockBases.length 624 &&
     (List.range 624).all fun bi =>
       Nat.ble ((cliElfBlockBases.getD bi 0#64).toNat + lsLen bi)
         c2FirstExternStubAddr.toNat) = true := by
  rfl_kernel

private theorem cliElfBlockBases_len_and_bounds :
    libsignalSessionLib.blocks.length = 624 ∧
    cliElfBlockBases.length = 624 ∧
    ∀ bi < 624, (cliElfBlockBases.getD bi 0#64).toNat + lsLen bi ≤ c2FirstExternStubAddr.toNat := by
  have hok := c2_bases_bounds_chk
  simp only [Bool.and_eq_true, Nat.beq_eq] at hok
  refine ⟨libsignalSessionLib_blocks_length, hok.1, fun bi hbi => ?_⟩
  exact Nat.ble_eq.mp (List.all_eq_true.mp hok.2 bi (List.mem_range.mpr hbi))

private theorem range_ne_lr_of_disjoint [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {skip : Nat → Bool} {idxs : List Nat}
    (hDisjOk : checkBlocksDisjointAux skip (c2InternalPairsOf idxs) 0 cliElfBlockBases = true)
    {lr : BitVec 64} {j : Nat} (hj : j < 624) {o : Nat} (ho : o < lsLen j)
    (hlrEq : lr = lsmpl.base j + BitVec.ofNat 64 o)
    (hnotSkip : skip j = false)
    {bi : Nat} (hbiMem : bi ∈ idxs) (hbi624 : bi < 624)
    {off : Nat} (hoff : off < lsLen bi) :
    cliElfMultiPlacement.base bi + BitVec.ofNat 64 off ≠ lr := by
  obtain ⟨hlenLs, hlenBases, hBounds⟩ := cliElfBlockBases_len_and_bounds
  have hj_lt : j < cliElfBlockBases.length := by omega
  have hspec := checkBlocksDisjointAux_spec 0 cliElfBlockBases hDisjOk j hj_lt
  rw [Nat.zero_add] at hspec
  rcases hspec with hs | hpairs
  · rw [hnotSkip] at hs; cases hs
  · have hpMem : ((cliElfBlockBases.getD bi 0#64).toNat, lsLen bi) ∈ c2InternalPairsOf idxs :=
      List.mem_map.mpr ⟨bi, hbiMem, rfl⟩
    have hdisj := hpairs _ hpMem
    have hbj_eq : lsmpl.base j = cliElfBlockBases[j] := by
      have h1 := (cliElf_linkedAt_unique hLs).1 j (by omega)
      have h2 : cliElfMultiPlacement.base j = cliElfBlockBases.getD j 0#64 := rfl
      have h3 : cliElfBlockBases.getD j 0#64 = cliElfBlockBases[j] :=
        list_getD_eq_getElem _ _ hj_lt
      exact h1.trans (h2.trans h3)
    have hbbi_eq : cliElfMultiPlacement.base bi = cliElfBlockBases.getD bi 0#64 := rfl
    have hj_bnd := hBounds j hj
    have hbi_bnd := hBounds bi hbi624
    have hbj_getD : cliElfBlockBases.getD j 0#64 = cliElfBlockBases[j] :=
      list_getD_eq_getElem _ _ hj_lt
    rw [hbj_getD] at hj_bnd
    have hstub_lt : c2FirstExternStubAddr.toNat < 2 ^ 64 := BitVec.isLt c2FirstExternStubAddr
    intro heq
    have hnat := congrArg BitVec.toNat heq
    rw [hlrEq, hbj_eq, hbbi_eq] at hnat
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hnat
    dsimp only at hdisj
    omega

theorem lsBlock_noExtern_of_disjoint [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {skip : Nat → Bool} {idxs : List Nat}
    (hDisjOk : checkBlocksDisjointAux skip (c2InternalPairsOf idxs) 0 cliElfBlockBases = true)
    {lr : BitVec 64} {j : Nat} (hj : j < 624) {o : Nat} (ho : o < lsLen j)
    (hlrEq : lr = lsmpl.base j + BitVec.ofNat 64 o)
    (hnotSkip : skip j = false)
    {bi : Nat} (hbiMem : bi ∈ idxs) (hbi624 : bi < 624)
    (hLenEq : (libsignalSessionLib.blockLib bi).text.code.length = lsLen bi) :
    LibBlockNoExtern libsignalSessionLib lsmpl (c2FmtProgTrap lr) bi := by
  obtain ⟨hlenLs, _, hBounds⟩ := cliElfBlockBases_len_and_bounds
  have hBaseEq : lsmpl.base bi = cliElfMultiPlacement.base bi :=
    (cliElf_linkedAt_unique hLs).1 bi (by omega)
  have hbi_bnd := hBounds bi hbi624
  have hstub_lt : c2FirstExternStubAddr.toNat < 2 ^ 64 := BitVec.isLt c2FirstExternStubAddr
  intro off hoff
  rw [hLenEq] at hoff
  rw [hBaseEq]
  have hne := range_ne_lr_of_disjoint hLs hDisjOk hj ho hlrEq hnotSkip hbiMem hbi624 hoff
  rw [c2FmtProgTrap_externAt_of_ne hne]
  apply c2FmtProg_externAt_none_of_lt_stub
  have hdef : cliElfMultiPlacement.base bi = cliElfBlockBases.getD bi 0#64 := rfl
  rw [hdef, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem allocWriter_noExtern_fmtWrite [LibsignalPlacement]
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hRet : LsRetAddrFmtWrite lr)
    (k : CliFmtWriteVtableKind) {aj : Nat}
    (haj : aj = 1 ∨ aj = 2 ∨ aj = 6 ∨ aj = 7) :
    LibBlockNoExtern allocMultiLib (c2MplAllocCli k) (c2FmtProgTrap lr) aj := by
  rcases hRet with ⟨j, hj, hnotInt, o, ho, hlrEq⟩
  obtain ⟨_, _, hBounds⟩ := cliElfBlockBases_len_and_bounds
  have hstub_lt : c2FirstExternStubAddr.toNat < 2 ^ 64 := BitVec.isLt c2FirstExternStubAddr
  let bi : Nat :=
    match k, aj with
    | .libsignalSession, 1 => 157
    | .libsignalSession, 2 => 160
    | .libsignalSession, 6 => 181
    | .libsignalSession, 7 => 182
    | .cliRatchet, 1 => 460
    | .cliRatchet, 2 => 465
    | .cliRatchet, 6 => 488
    | .cliRatchet, 7 => 489
    | .cliHandshake, 1 => 517
    | .cliHandshake, 2 => 522
    | .cliHandshake, 6 => 533
    | _, _ => 534
  have hBaseEq : (c2MplAllocCli k).base aj = cliElfMultiPlacement.base bi := by
    rcases haj with rfl | rfl | rfl | rfl <;> cases k <;> rfl
  have hbiMem : bi ∈ c2FmtWriteInternalIndices := by
    rcases haj with rfl | rfl | rfl | rfl <;> cases k <;> decide
  have hbi624 : bi < 624 := by
    rcases haj with rfl | rfl | rfl | rfl <;> cases k <;> decide
  have hPairMem : (aj, bi) ∈
      ([(1, 157), (2, 160), (6, 181), (7, 182),
        (1, 460), (2, 465), (6, 488), (7, 489),
        (1, 517), (2, 522), (6, 533), (7, 534)] : List (Nat × Nat)) := by
    rcases haj with rfl | rfl | rfl | rfl <;> cases k <;> decide
  have hLenEq : (allocMultiLib.blockLib aj).text.code.length = lsLen bi := by
    have h0 := List.all_eq_true.mp c2_allocWriter_codeLen_eq_lsLen (aj, bi) hPairMem
    dsimp only at h0
    exact Nat.beq_eq.mp h0
  have hbi_bnd := hBounds bi hbi624
  intro off hoff
  rw [hLenEq] at hoff
  rw [hBaseEq]
  have hne := range_ne_lr_of_disjoint hLs c2_disjoint_fmtWrite_ok hj ho hlrEq hnotInt
    hbiMem hbi624 hoff
  rw [c2FmtProgTrap_externAt_of_ne hne]
  apply c2FmtProg_externAt_none_of_lt_stub
  have hdef : cliElfMultiPlacement.base bi = cliElfBlockBases.getD bi 0#64 := rfl
  rw [hdef, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-! ### `.rodata` Guards (`cliFmtWriteRoGuard`, `cliFormatInnerRoGuard`) from `F3CodeInv` -/

private theorem unpack64_eq_leBytes64 (w : BitVec 64) :
    unpack64 w = CliFmtAlloc.leBytes64 w := rfl

private theorem f3CodeInv_roDataAt_of_cliRoSegSlice
    {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m)
    {addr : BitVec 64} {bytes : List (BitVec 8)}
    (h : checkRoSegSlice cliElfImage addr bytes = true) :
    RoDataAt m addr bytes := by
  obtain ⟨seg, hseg, hperm, hsl⟩ := roSlice_of_checkRoSegSlice h
  exact f3CodeInv_roDataAt_of_checkSegSlice hLs hInv addr bytes
    ⟨seg, f3PatchedElf_roSeg_eq.trans hseg, hperm, hsl⟩

set_option maxHeartbeats 2000000 in
private theorem c2MplAllocCli_vtSlots_ro_chk (k : CliFmtWriteVtableKind) :
    let va := allocStringWriteAddrs (c2MplAllocCli k)
    (checkRoSegSlice cliElfImage (va.vtable + 24#64) (CliFmtAlloc.leBytes64 va.writeStr) &&
     checkRoSegSlice cliElfImage (va.vtable + 32#64) (CliFmtAlloc.leBytes64 va.writeChar) &&
     checkRoSegSlice cliElfImage (va.vtable + 40#64) (CliFmtAlloc.leBytes64 va.writeFmt)) = true := by
  cases k <;> (dsimp only; rfl_kernel)

theorem c2_stringWriteVtableRoAt_cli {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) (k : CliFmtWriteVtableKind) :
    StringWriteVtableRoAt (allocStringWriteAddrs (c2MplAllocCli k)) m := by
  have hchk := c2MplAllocCli_vtSlots_ro_chk k
  dsimp only at hchk
  simp only [Bool.and_eq_true] at hchk
  rcases hchk with ⟨⟨h1, h2⟩, h3⟩
  refine ⟨?_, ?_, ?_⟩ <;> rw [unpack64_eq_leBytes64]
  · exact f3CodeInv_roDataAt_of_cliRoSegSlice hLs hInv h1
  · exact f3CodeInv_roDataAt_of_cliRoSegSlice hLs hInv h2
  · exact f3CodeInv_roDataAt_of_cliRoSegSlice hLs hInv h3

theorem c2_stringWriteVtableRoAt_alloc {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    StringWriteVtableRoAt (allocStringWriteAddrs c2AllocMpl) m := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [unpack64_eq_leBytes64]
  · exact c2_alloc_roDataAt_vtableWriteStr hLs hInv
  · exact c2_alloc_roDataAt_vtableWriteChar hLs hInv
  · exact c2_alloc_roDataAt_vtableWriteFmt hLs hInv

/-- Exact 51-byte `.rodata` slice at `cliAesDecErrStr1Addr`. -/
@[expose] def c2AesDecErrStr1Bytes : List (BitVec 8) :=
  Arm64.Process.bytesOfString "ciphertext length must be a non-zero multiple of 16"

/-- Exact 17-byte `.rodata` slice at `cliAesDecErrStr2Addr`. -/
@[expose] def c2AesDecErrStr2Bytes : List (BitVec 8) :=
  Arm64.Process.bytesOfString "failed to decrypt"

set_option maxHeartbeats 2000000 in
private theorem c2_aesErrStrs_ro_chk :
    (checkRoSegSlice cliElfImage cliAesDecErrStr1Addr c2AesDecErrStr1Bytes &&
     checkRoSegSlice cliElfImage cliAesDecErrStr2Addr c2AesDecErrStr2Bytes) = true := by
  rfl_kernel

theorem f3CodeInv_libsignalRoLoaded {mpl mmpl : Obj.MultiPlacement} {m : Memory}
    (_hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : F3CodeInv mpl mmpl m) :
    LibsignalRoLoaded mpl m :=
  hInv.lsRo.2

theorem c2_cliFmtWriteRoGuard [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hInv : F3CodeInv lsmpl mmpl m) :
    cliFmtWriteRoGuard c2MplAllocCli c2CoreFmtMpl m :=
  ⟨f3CodeInv_libsignalRoLoaded hLs hInv,
   c2_coreFmt_roDataAt_decDigitsLut hLs hInv,
   c2_stringWriteVtableRoAt_cli hLs hInv⟩

theorem c2_cliFormatInnerRoGuard [LibsignalPlacement] {mmpl : Obj.MultiPlacement} {m : Memory}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hInv : F3CodeInv lsmpl mmpl m) :
    cliFormatInnerRoGuard c2AllocMpl c2CoreFmtMpl m := by
  have hchk := c2_aesErrStrs_ro_chk
  simp only [Bool.and_eq_true] at hchk
  have hlen1 : c2AesDecErrStr1Bytes.length = 51 := by decide
  have hlen2 : c2AesDecErrStr2Bytes.length = 17 := by decide
  have h1 := hlen1 ▸ (f3CodeInv_roDataAt_of_cliRoSegSlice hLs hInv hchk.1).1
  have h2 := hlen2 ▸ (f3CodeInv_roDataAt_of_cliRoSegSlice hLs hInv hchk.2).1
  exact ⟨f3CodeInv_libsignalRoLoaded hLs hInv,
    c2_coreFmt_roDataAt_decDigitsLut hLs hInv,
    c2_stringWriteVtableRoAt_alloc hLs hInv,
    h1, h2⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CliFmtRow.AllocRo
