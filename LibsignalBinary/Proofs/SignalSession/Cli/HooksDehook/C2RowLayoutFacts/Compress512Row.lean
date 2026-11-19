/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress512GhostReplays -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts -- proof-setup: allow-public-import

/-!
# Stage-B `GhostRowOk` & `.text.lib2` Layout Glue for `sha2::sha512::compress512` (`C2RowLayoutFacts.Compress512Row`)

Parameterized by `(comp512Addr comp512K64Addr : BitVec 64)` (closed at Stage-B B2 once LINK-PREP
lands the stock-ELF `Wp4LayoutGen` constants), this module discharges `Placeable` from boolean
`checkPlaceable`, `.rodata` `K64` slice loading, `.text.lib2` hull / return-address separation, and
`GhostRowOk` (`lsmpl` + `guardOf` forms) for `compress512Sym` (`lsCompress512SymCli`).
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512Row

open Arm64 Arm64.Obj Arm64.Process ProofLib ProofLib.StdStartup
open CryptoVerification (LibsignalPlacement lsmpl)
open CryptoVerification.SignalSession (CliHooks cliElfBytes libsignalSessionLib)
open LibsignalBinary.Heap.Fine (f3StdLayout)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512 (sha512KBytes_length)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
  (compress512Block compress512K64Data compress512Lib compress512Sym sha2K64Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells (sha512KBytes)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt (HookNoAllocFailed)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.CodeSubslice
  (checkProgCodeSubslice codeLoaded_of_checkProgCodeSubslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512
  (c2Compress512Addr c2Compress512K64Addr c2_compress512Lib_placeable c2_compress512_in_lib2_hi
   c2_compress512_in_lib2_lo c2_compress512_resolve_eq c2_compress512_ro_slice
   c2_compress512_rx_subslice)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.RowCommon
  (f3CodeInv_and_fs_keepsFrozen)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress512GhostReplays
  (compress512ByteLen compress512Ghost compress512Ghost_noAllocFailed compress512Ghost_rowOk
   compress512Placement compress512Placement_base compress512Placement_k64 compress512SubProg
   keepR_compress512)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay (GhostRowOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs (ExtraRowSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress512RowSpec
  (Compress512RowSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Lib2LayoutFacts
  (C2ExternTableFacts f3CodeInv_roDataAt_of_checkSegSlice
   f3LsRetAddr624_lt_firstExternStub f3RxSeg_realProg617_externAt_none isLinkedPanicAddr
   isLinkedPanicAddr_false_of_mid keepLib2Text keepLib2Text_sub_rxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.StartupStatics
  (F3CodeInv f3PatchedElf)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfF3Relink.Tie (f3TrialRxProg)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.Wp4LayoutGen
  (c2FirstExternStubAddr c2Lib2TextHi c2Lib2TextLo)

/-- Construct `compress512Lib.Placeable (compress512Placement comp512Addr comp512K64Addr)` from
    boolean `checkPlaceable` and `.rodata` alignment/no-wrap checks (closed by `decide` at B2). -/
theorem compress512Lib_placeable_of_checks {comp512Addr comp512K64Addr : BitVec 64}
    (hText : compress512Block.checkPlaceable
      (compress512Placement comp512Addr comp512K64Addr) = true)
    (hAlign : comp512K64Addr.toNat % 8 = 0)
    (hNoWrap : comp512K64Addr.toNat + 640 ≤ 2 ^ 64) :
    compress512Lib.Placeable (compress512Placement comp512Addr comp512K64Addr) where
  text := CodeBlock.placeable_of_checkPlaceable hText
  data_nodup := by decide
  data_ok := by
    intro d hd
    simp only [compress512Lib, List.mem_singleton] at hd
    subst hd
    refine ⟨by decide, by decide, ?_, ?_⟩
    · change ((compress512Placement comp512Addr comp512K64Addr).ρ sha2K64Sym).toNat % 8 = 0
      rw [compress512Placement_k64]; exact hAlign
    · have hlen : compress512K64Data.bytes.length = 640 := sha512KBytes_length
      have hzt : compress512K64Data.zeroTail = 0 := rfl
      have hsym : compress512K64Data.sym = sha2K64Sym := rfl
      rw [hsym, compress512Placement_k64, hlen, hzt, Nat.add_zero]
      exact hNoWrap
  data_relocs_ok := by
    intro d hd r hr
    simp only [compress512Lib, List.mem_singleton] at hd
    subst hd
    cases hr

/-- Stock-ELF layout witness bundle for `compress512Lib` at `(comp512Addr, comp512K64Addr)`. -/
structure C2Compress512LayoutFacts (mpl : Obj.MultiPlacement)
    (comp512Addr comp512K64Addr : BitVec 64) : Prop where
  placeable : compress512Lib.Placeable (compress512Placement comp512Addr comp512K64Addr)
  resolve_eq : libsignalSessionLib.resolve mpl compress512Sym = comp512Addr
  rx_subslice : checkProgCodeSubslice f3TrialRxProg
    (compress512SubProg (compress512Placement comp512Addr comp512K64Addr)) = true
  ro_slice : ∃ seg, f3PatchedElf.segments[f3StdLayout.roSegIdx]? = some seg ∧
    seg.perm.rwx = Perm.ro ∧
    checkSegSlice seg seg.bytes.length comp512K64Addr sha512KBytes = true
  in_lib2_lo : c2Lib2TextLo.toNat ≤ comp512Addr.toNat
  in_lib2_hi : comp512Addr.toNat + compress512ByteLen ≤ c2Lib2TextHi.toNat
  in_mid_lo : 0x47ac2c ≤ comp512Addr.toNat
  in_mid_hi : comp512Addr.toNat + compress512ByteLen ≤ 0x4cb070

theorem keepR_compress512_noPanic {mpl : Obj.MultiPlacement}
    {comp512Addr comp512K64Addr : BitVec 64}
    (hLay : C2Compress512LayoutFacts mpl comp512Addr comp512K64Addr)
    {pc : BitVec 64}
    (hk : keepR_compress512 (compress512Placement comp512Addr comp512K64Addr) pc = true) :
    isLinkedPanicAddr pc = false := by
  unfold keepR_compress512 compress512Placement at hk
  have hlt : (pc - comp512Addr).toNat < compress512ByteLen := of_decide_eq_true hk
  have hlo := hLay.in_mid_lo
  have hhi := hLay.in_mid_hi
  have hpc_eq : pc = comp512Addr + (pc - comp512Addr) := by bv_omega
  have hpc_nat : pc.toNat = comp512Addr.toNat + (pc - comp512Addr).toNat := by
    conv => lhs; rw [hpc_eq]
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact isLinkedPanicAddr_false_of_mid (by omega) (by omega)

theorem keepR_compress512_sub_keepLib2Text {mpl : Obj.MultiPlacement}
    {comp512Addr comp512K64Addr : BitVec 64}
    (hLay : C2Compress512LayoutFacts mpl comp512Addr comp512K64Addr)
    {pc : BitVec 64}
    (hk : keepR_compress512 (compress512Placement comp512Addr comp512K64Addr) pc = true) :
    keepLib2Text pc = true := by
  unfold keepR_compress512 compress512Placement at hk
  have hlt : (pc - comp512Addr).toNat < compress512ByteLen := of_decide_eq_true hk
  have hlo := hLay.in_lib2_lo
  have hhi := hLay.in_lib2_hi
  have htop : c2Lib2TextHi.toNat < 2 ^ 64 := BitVec.isLt c2Lib2TextHi
  unfold keepLib2Text
  apply decide_eq_true
  have hpc_eq : pc = comp512Addr + (pc - comp512Addr) := by bv_omega
  have hpc_nat : pc.toNat = comp512Addr.toNat + (pc - comp512Addr).toNat := by
    conv => lhs; rw [hpc_eq]
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

theorem keepR_compress512_sub_rxProg {mpl : Obj.MultiPlacement}
    {comp512Addr comp512K64Addr : BitVec 64}
    (hLay : C2Compress512LayoutFacts mpl comp512Addr comp512K64Addr)
    {pc : BitVec 64}
    (hk : keepR_compress512 (compress512Placement comp512Addr comp512K64Addr) pc = true) :
    progKeep f3TrialRxProg pc = true :=
  keepLib2Text_sub_rxProg (keepR_compress512_sub_keepLib2Text hLay hk)

theorem c2_compress512_hKeep [LibsignalPlacement] {mpl : Obj.MultiPlacement}
    {comp512Addr comp512K64Addr : BitVec 64}
    (hLay : C2Compress512LayoutFacts mpl comp512Addr comp512K64Addr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    {lr : BitVec 64} (hlr : LsRetAddr624 lr) :
    keepR_compress512 (compress512Placement comp512Addr comp512K64Addr) lr = false := by
  have hlt := f3LsRetAddr624_lt_firstExternStub hLs hlr
  have hlo : c2FirstExternStubAddr.toNat ≤ c2Lib2TextLo.toNat := by decide
  cases hk : keepR_compress512 (compress512Placement comp512Addr comp512K64Addr) lr
  · rfl
  · have hlib2 := keepR_compress512_sub_keepLib2Text hLay hk
    unfold keepLib2Text at hlib2
    rw [decide_eq_true_eq] at hlib2
    omega

theorem c2_compress512_hCL {mpl mmpl : Obj.MultiPlacement}
    {comp512Addr comp512K64Addr : BitVec 64} {InvS : State → Prop}
    (hLay : C2Compress512LayoutFacts mpl comp512Addr comp512K64Addr)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, InvS u →
      (compress512SubProg (compress512Placement comp512Addr comp512K64Addr)).CodeLoaded u.mem :=
  fun u hu => codeLoaded_of_checkProgCodeSubslice (hInv u hu).rxCode hLay.rx_subslice

theorem c2_compress512_hRo {mpl mmpl : Obj.MultiPlacement}
    {comp512Addr comp512K64Addr : BitVec 64} {InvS : State → Prop}
    (hLay : C2Compress512LayoutFacts mpl comp512Addr comp512K64Addr)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem) :
    ∀ u : State, InvS u →
      RoDataAt u.mem
        ((compress512Placement comp512Addr comp512K64Addr).ρ sha2K64Sym) sha512KBytes := by
  intro u hu
  rw [compress512Placement_k64]
  exact f3CodeInv_roDataAt_of_checkSegSlice hLs (hInv u hu) comp512K64Addr sha512KBytes hLay.ro_slice

theorem c2_compress512_hRealHullNoExt {mpl mmpl : Obj.MultiPlacement}
    {comp512Addr comp512K64Addr : BitVec 64}
    (hLay : C2Compress512LayoutFacts mpl comp512Addr comp512K64Addr)
    (hExt : C2ExternTableFacts mpl) :
    ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_compress512 (compress512Placement comp512Addr comp512K64Addr) pc = true →
      (cliProgExtPlacedAt mpl (CryptoVerification.SignalSession.cliExternsPlaced mmpl) 617 W).externAt? pc = none :=
  fun W _ hkeep =>
    f3RxSeg_realProg617_externAt_none hExt W (keepR_compress512_sub_rxProg hLay hkeep)
      (keepR_compress512_noPanic hLay hkeep)

theorem compress512Sym_extraRowSpec [LibsignalPlacement] {f : State → State}
    (h : Compress512RowSpec f) : ExtraRowSpec compress512Sym f := by
  unfold ExtraRowSpec
  iterate 23 rw [ite_eq_right (by decide)]
  rw [ite_eq_left (by decide)]
  exact h

theorem c2_compress512Ghost_rowOk_of_inv [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement)
    (comp512Addr comp512K64Addr : BitVec 64)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hLay : C2Compress512LayoutFacts mpl comp512Addr comp512K64Addr)
    (hExt : C2ExternTableFacts mpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl)
    (hLsLsmpl : libsignalSessionLib.LinkedAt cliElfBytes lsmpl)
    (hInv : ∀ u : State, InvS u → F3CodeInv mpl mmpl u.mem)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v) :
    GhostRowOk mpl mmpl InvS EG compress512Sym (fun _ => True)
      (compress512Ghost (compress512Placement comp512Addr comp512K64Addr)) :=
  compress512Ghost_rowOk mpl mmpl (compress512Placement comp512Addr comp512K64Addr) InvS EG
    hLay.placeable compress512Sym_extraRowSpec
    (hLay.resolve_eq.trans (compress512Placement_base comp512Addr comp512K64Addr).symm)
    (c2_compress512_hCL hLay hInv)
    (c2_compress512_hRo hLay hLs hInv)
    hInvKeep
    (fun _ hlr => c2_compress512_hKeep hLay hLsLsmpl hlr)
    (c2_compress512_hRealHullNoExt hLay hExt)

theorem c2_compress512Ghost_rowOk_guardOf [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (comp512Addr comp512K64Addr : BitVec 64)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hLay : C2Compress512LayoutFacts lsmpl comp512Addr comp512K64Addr)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG compress512Sym
      (guardOf compress512Sym)
      (compress512Ghost (compress512Placement comp512Addr comp512K64Addr)) := by
  obtain ⟨hSpec, hRep⟩ :=
    c2_compress512Ghost_rowOk_of_inv lsmpl mmpl comp512Addr comp512K64Addr
      (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
      hLay hExt hLs hLs (fun _ h => h.1)
      (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)
  exact ⟨hSpec, ⟨hRep.preserves_execFrozen, fun W s0 sf _ => hRep.replay_at_stub W s0 sf trivial⟩⟩

theorem c2_compress512Ghost_noAllocFailed [LibsignalPlacement]
    {mpl : Obj.MultiPlacement} {comp512Addr comp512K64Addr : BitVec 64}
    (hLay : C2Compress512LayoutFacts mpl comp512Addr comp512K64Addr) :
    HookNoAllocFailed (compress512Ghost (compress512Placement comp512Addr comp512K64Addr)) :=
  compress512Ghost_noAllocFailed hLay.placeable

/-- Concrete 0-hook stock-ELF (`0d6227d2…`) witness for `C2Compress512LayoutFacts`. -/
theorem c2Compress512LayoutFacts_of_linkedAt {mpl : Obj.MultiPlacement}
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    C2Compress512LayoutFacts mpl c2Compress512Addr c2Compress512K64Addr where
  placeable := c2_compress512Lib_placeable
  resolve_eq := c2_compress512_resolve_eq hLs
  rx_subslice := c2_compress512_rx_subslice
  ro_slice := c2_compress512_ro_slice
  in_lib2_lo := c2_compress512_in_lib2_lo
  in_lib2_hi := c2_compress512_in_lib2_hi
  in_mid_lo := by decide
  in_mid_hi := by decide

/-- Concrete `GhostRowOk` for `compress512Sym` (`fun _ => True` guard) at `(c2Compress512Addr, c2Compress512K64Addr)`. -/
theorem c2_compress512Ghost_rowOk_true_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG compress512Sym
      (fun _ => True)
      (compress512Ghost (compress512Placement c2Compress512Addr c2Compress512K64Addr)) :=
  c2_compress512Ghost_rowOk_of_inv lsmpl mmpl c2Compress512Addr c2Compress512K64Addr
    (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG
    (c2Compress512LayoutFacts_of_linkedAt hLs) hExt hLs hLs (fun _ h => h.1)
    (f3CodeInv_and_fs_keepsFrozen lsmpl mmpl PredFs)

/-- Concrete `GhostRowOk` for `compress512Sym` (`guardOf` form) at `(c2Compress512Addr, c2Compress512K64Addr)`. -/
theorem c2_compress512Ghost_rowOk_c2 [LibsignalPlacement]
    (mmpl : Obj.MultiPlacement)
    (PredFs : FsState → Prop)
    (EG : CliHooks → String → Option (State → State))
    (guardOf : String → State → Prop)
    (hExt : C2ExternTableFacts lsmpl)
    (hLs : libsignalSessionLib.LinkedAt cliElfBytes lsmpl) :
    GhostRowOk lsmpl mmpl (fun u => F3CodeInv lsmpl mmpl u.mem ∧ PredFs u.fs) EG compress512Sym
      (guardOf compress512Sym)
      (compress512Ghost (compress512Placement c2Compress512Addr c2Compress512K64Addr)) :=
  c2_compress512Ghost_rowOk_guardOf mmpl c2Compress512Addr c2Compress512K64Addr PredFs EG guardOf
    (c2Compress512LayoutFacts_of_linkedAt hLs) hExt hLs

theorem c2_compress512Ghost_noAllocFailed_c2 [LibsignalPlacement]
    {mpl : Obj.MultiPlacement} (hLs : libsignalSessionLib.LinkedAt cliElfBytes mpl) :
    HookNoAllocFailed
      (compress512Ghost (compress512Placement c2Compress512Addr c2Compress512K64Addr)) :=
  c2_compress512Ghost_noAllocFailed (c2Compress512LayoutFacts_of_linkedAt hLs)

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.C2RowLayoutFacts.Compress512Row
