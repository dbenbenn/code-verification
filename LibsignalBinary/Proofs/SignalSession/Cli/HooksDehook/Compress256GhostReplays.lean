/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256 -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
import ProofLib.Process.OracleEq

/-!
# `sha2::sha256::compress256` Ghost Hook and `GhostRowReplayOn`

Ghost-hook and replay proofs for `lsCompress256Sym` (`sha2::sha256::compress256`) under
`WithLsRet.withLsRet` / `LsRetAddr624` in `.text.lib2`:

- Row anchor and ghost hook (`keepR_compress256`, `compress256SubProg`, `compress256Ghost`):
  `compress256SubProg pl` places `compress256Lib` (7,636 B = 1,909 words at `pl.base`, no external
  call stubs) with `Syscall.standard`. `masterCompress256ROSpec` separates `mem.perm` out of
  `.post` (`MemsetStatePreserved`) so `SpecStripSInvariant keep masterCompress256ROSpec` holds by
  `rfl`, while `compress256StackedMasterROSpec 176` (`ProcessFieldsPreserved`) recovers `mem.perm`
  preservation (`VmPreserved`, `AllocCallPreserved`, `KeepsExec`) on the active real branch.
  `compress256Ghost pl` wraps `withLsRet masterCompress256ROSpec` via
  `linkedCallHookG (roTableGuard (pl.ρ sha2K32Sym) sha256KBytes)` on `emptyStdProg` with fallback
  `compress256Hook sha256Compress`.
- State preservation and consumer `HookOk` proofs: unconditional `compress256Ghost_fs`,
  `compress256Ghost_fsT`, and `compress256Ghost_preserves_execFrozen`; under
  `compress256Lib.Placeable pl`, `compress256Ghost_vmPreserved`, `compress256Ghost_keepsExec`, and
  `Compress256RowSpec (compress256Ghost pl)` (`176 ≤ stk`).
- Generic-`InvS` `GhostRowReplayOn` and `GhostRowOk` with `entryGuard := fun _ => True`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress256GhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames.HMAC (ShaState chunks64)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalSpqrV1 (sha256Compress)
open CryptoVerification.LibsignalTripleRatchet (compress256Spec withStack)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced libsignalSessionLib
   lsBlackBoxSym lsCompress256Sym lsDurationSinceSym lsFromUtf8Sym lsMemrchrSym
   lsSharedSecretDropSym lsStaticSecretDropSym lsTimeAddSym)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (AllocCallPreserved FdsHiFrame VmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas (perm_writeBytes_norm)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256
  (compress256MasterRO_simulates_stackedMasterRO_roSep compress256StackedMasterROSpec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Code
  (compress256Block compress256Lib compress256Sym compress256_code_eq
   compress256_tree_size sha2K32Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Compress256Loop
  (chunks64_cons_take_drop chunks64_of_length_lt compress256_fnAddr)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells (sha256KBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math (sha256CompressState)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.SpqrBridge
  (sha256CompressState_eq_spqrSha256Compress)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift
  (compress256MasterROSpec compress256_master_ro_ok stackAt_le_two_pow_64
   stackAt_split_frame176 withPlacedCodeLoaded)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt SpecSimulates withRoData)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealPre ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant
   keepFsTrace linkedCallHook satisfies_stripExecOutside stepsUntil_of_stripS_standard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (ExtraEntryGuard GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG
  (ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis hookOk_linkedCallHookG_roTable
   linkedCallHookG linkedCallHookG_activeRealPre_of_noException linkedCallHookG_fs
   linkedCallHookG_fsT roDataAt_of_keepsFrozen roTableGuard roTableGuard_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs
  (hookOk_withLsRet_of_simulates keepLr_false_of_noException_via_activeRealPre
   specPreservesFsTrace_withLsRet specStripSInvariant_withLsRet subroutine_ok_withRoData_withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (MemsetStatePreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (emptyStdProg emptyStdProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords
  (codeLoaded_stripExecOutside_of_keep)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (hookOk_withLsRet withLsRet withLsRet_outcome_setPC withLsRet_pre_setPC)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraRowSpec GhostRowSpecOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress256RowSpec
  (Compress256RowSpec compress256RowSingleSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_steps_lift_of_visitedIn_noExtern)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (KeepsExec compress256Hook_keepsExec compress256Hook_roBudget_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (compress256Blocks sessionCompress256ROBudgetSpec sessionCompress256ROSpec)

/-! ## 1. Row Anchor Definitions & Strip-Invariant Master Spec -/

/-- Byte length (`7,636` B = `1,909` words) of `sha2::sha256::compress256`. -/
@[expose] def compress256ByteLen : Nat := 7636

/-- Canonical `Obj.Placement` for `compress256Lib` at code base `base` and `K32` `.rodata`
    address `k32Addr`. -/
@[expose] def compress256Placement (base k32Addr : BitVec 64) : Obj.Placement where
  base := base
  ρ sym := if sym == sha2K32Sym then k32Addr else 0#64

theorem compress256Placement_base (base k32Addr : BitVec 64) :
    (compress256Placement base k32Addr).base = base :=
  rfl

/-- Kept-region byte predicate `[pl.base, pl.base + 7636)` covering `compress256Lib`. -/
@[expose] def keepR_compress256 (pl : Obj.Placement) (pc : BitVec 64) : Bool :=
  decide ((pc - pl.base).toNat < compress256ByteLen)

theorem keepR_compress256_entry (pl : Obj.Placement) :
    keepR_compress256 pl pl.base = true := by
  unfold keepR_compress256 compress256ByteLen
  have hsub : pl.base - pl.base = 0#64 := by bv_omega
  rw [hsub]
  decide

/-- Pure `1,909`-word (`7,636`-byte) sub-program holding `compress256Lib` at `pl.base` with
    `Syscall.standard`. -/
@[expose] def compress256SubProg (pl : Obj.Placement) : Program :=
  { compress256Lib.program pl (fun _ => none) with svc := Syscall.standard }

theorem compress256SubProg_base (pl : Obj.Placement) :
    (compress256SubProg pl).base = pl.base :=
  rfl

theorem compress256SubProg_svc (pl : Obj.Placement) :
    (compress256SubProg pl).svc = Syscall.standard :=
  rfl

theorem compress256SubProg_externAt_none (pl : Obj.Placement) (pc : BitVec 64) :
    (compress256SubProg pl).externAt? pc = none := by
  simp [compress256SubProg, compress256Lib, compress256Block,
    Obj.PlacedLib.program, Program.externAt?, Program.hookAtOff?]

set_option maxRecDepth 400000 in
theorem compress256SubProg_code_length {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) :
    (compress256SubProg pl).code.length = compress256ByteLen := by
  have hc : (compress256SubProg pl).code = compress256Lib.text.patched pl := rfl
  rw [hc, Obj.CodeBlock.length_patched_of_aligned pl hpl.text.len_aligned,
      compress256_code_eq,
      ProofLib.ProgramReflection.WordTree.length_toBytes_of_checkSize? compress256_tree_size]
  rfl

theorem keepR_compress256_of_code_offset {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {i : Nat}
    (hi : i < (compress256SubProg pl).code.length) :
    keepR_compress256 pl ((compress256SubProg pl).base + BitVec.ofNat 64 i) = true := by
  rw [compress256SubProg_code_length hpl] at hi
  rw [compress256SubProg_base]
  unfold keepR_compress256
  have hi2 : i < 2 ^ 64 := by
    unfold compress256ByteLen at hi
    omega
  have hsub : pl.base + BitVec.ofNat 64 i - pl.base = BitVec.ofNat 64 i := by bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi2]
  exact decide_eq_true hi

theorem compress256SubProg_codeLoaded_stripExecOutside {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {mem : Memory}
    (hL : (compress256SubProg pl).CodeLoaded mem) :
    (compress256SubProg pl).CodeLoaded (stripExecOutside (keepR_compress256 pl) mem) :=
  codeLoaded_stripExecOutside_of_keep (fun _ hi => keepR_compress256_of_code_offset hpl hi) hL

/-- Strip-invariant `176`-B master `compress256` contract (`rfl`-identical `.pre` to
    `compress256StackedMasterROSpec 176`, with `MemsetStatePreserved` in `.post` so
    `SpecStripSInvariant keep masterCompress256ROSpec` holds definitionally). -/
@[expose] def masterCompress256ROSpec :
    Spec (Bool × BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat) where
  pre := (compress256StackedMasterROSpec 176).pre
  post := fun (ro, stA, st, blkA, bs, _) s0 sf =>
    ⌜MemsetStatePreserved s0 sf⌝ ∗
      (stA ↦ₛ shaStateBytes ((chunks64 bs).foldl sha256Compress st)) ∗
      compress256Blocks ro blkA bs ∗ stackAt s0.sp 176
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- `withLsRet`-wrapped, `W`-independent ghost hook for `lsCompress256Sym`. -/
@[expose] noncomputable def compress256Ghost [LibsignalPlacement]
    (pl : Obj.Placement) : State → State :=
  linkedCallHookG
    (roTableGuard (pl.ρ sha2K32Sym) sha256KBytes)
    (keepR_compress256 pl)
    emptyStdProg
    (compress256SubProg pl)
    pl.base
    (withLsRet masterCompress256ROSpec)
    (compress256Hook sha256Compress)

/-- Convenience wrapper constructing `compress256Ghost` directly from `(base, k32Addr)`. -/
noncomputable abbrev compress256MplGhost [LibsignalPlacement]
    (base k32Addr : BitVec 64) : State → State :=
  compress256Ghost (compress256Placement base k32Addr)

/-- Block-617 entry-state guard for `lsCompress256Sym` (`True`: `LsRetAddr624` is
    extracted directly from non-`.Exception` at each call step). -/
@[expose] def compress256EntryGuard (_mpl : Obj.MultiPlacement) (_s0 : State) : Prop :=
  True

/-! ## 2. Master `subroutine_ok`, Invariants, & State Preservation -/

private theorem sha256KBytes_length_le : sha256KBytes.length ≤ 2 ^ 64 := by
  have h : sha256KBytes.length = 256 := by
    simp [sha256KBytes, List.length_flatMap, unpack32_length,
      LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Cells.sha256K_length]
  omega

private theorem keepFsTrace_compress256Hook_eq
    (F : ShaState → List (BitVec 8) → ShaState) :
    keepFsTrace (compress256Hook F) = compress256Hook F := by
  funext s
  unfold keepFsTrace compress256Hook returnToLinkRegister
  congr

private theorem compress256Hook_vm (F : ShaState → List (BitVec 8) → ShaState) (s : State) :
    VmPreserved s (compress256Hook F s) := by
  refine ⟨⟨rfl, rfl, ?_⟩, rfl, fun a => ?_, FdsHiFrame.of_fs_eq rfl⟩
  · unfold compress256Hook returnToLinkRegister; rfl
  · unfold compress256Hook returnToLinkRegister
    dsimp only [State.setPC, State.setMem]
    exact congrFun (perm_writeBytes_norm s.mem (s.readReg64 .x0) _) a

private theorem compress256Hook_memsetPreserved
    (F : ShaState → List (BitVec 8) → ShaState) (s : State) :
    MemsetStatePreserved s (compress256Hook F s) := by
  unfold compress256Hook returnToLinkRegister MemsetStatePreserved
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem specStripSInvariant_masterCompress256RO (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterCompress256ROSpec where
  pre_eq := fun _ s => by cases s; rfl
  post_eq := fun _ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

private theorem specStripSInvariant_masterCompress256ROLs [LibsignalPlacement]
    (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (withLsRet masterCompress256ROSpec) :=
  specStripSInvariant_withLsRet (specStripSInvariant_masterCompress256RO keep)

private theorem specPreservesFsTrace_masterCompress256RO :
    SpecPreservesFsTrace masterCompress256ROSpec := by
  intro x R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterCompress256ROSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfs : sf.fs = s0.fs := hpost.1.1
    have htr : sf.trace = s0.trace := hpost.1.2.1
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem specPreservesFsTrace_masterCompress256ROLs [LibsignalPlacement] :
    SpecPreservesFsTrace (withLsRet masterCompress256ROSpec) :=
  specPreservesFsTrace_withLsRet specPreservesFsTrace_masterCompress256RO

private theorem masterCompress256RO_pre_setPC
    (x : Bool × BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat)
    (s : State) (pc : BitVec 64) :
    masterCompress256ROSpec.pre x (s.setPC pc) = masterCompress256ROSpec.pre x s := by
  cases s; rfl

private theorem masterCompress256RO_outcome_setPC
    (x : Bool × BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat)
    (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterCompress256ROSpec x R (s0.setPC pc) sf) :
    SubroutineOutcome masterCompress256ROSpec x R s0 sf := by
  rcases h with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨by cases s0; exact hret, by cases s0; exact hcc, ?_⟩
    have heq : masterCompress256ROSpec.post x (s0.setPC pc) sf =
        masterCompress256ROSpec.post x s0 sf := by
      cases s0; rfl
    rwa [heq] at hpost
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem masterCompress256ROLs_pre_setPC [LibsignalPlacement]
    (x : Bool × BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat)
    (s : State) (pc : BitVec 64) :
    (withLsRet masterCompress256ROSpec).pre x (s.setPC pc) =
      (withLsRet masterCompress256ROSpec).pre x s :=
  withLsRet_pre_setPC masterCompress256RO_pre_setPC x s pc

private theorem masterCompress256ROLs_outcome_setPC [LibsignalPlacement]
    (x : Bool × BitVec 64 × ShaState × BitVec 64 × List (BitVec 8) × Nat)
    (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (withLsRet masterCompress256ROSpec) x R (s0.setPC pc) sf) :
    SubroutineOutcome (withLsRet masterCompress256ROSpec) x R s0 sf :=
  withLsRet_outcome_setPC masterCompress256RO_outcome_setPC x R s0 sf pc h

set_option maxRecDepth 400000 in
private theorem compress256StackedMasterRO_subroutine_ok {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) {hookStack : Nat} (hstack : 176 ≤ hookStack) :
    subroutine_ok (compress256SubProg pl) pl.base
      (withRoData (pl.ρ sha2K32Sym) sha256KBytes (compress256StackedMasterROSpec hookStack)) := by
  have hm := compress256_master_ro_ok hpl (P := compress256SubProg pl)
    (fun off _ => compress256SubProg_externAt_none pl _)
  rw [compress256_fnAddr pl] at hm
  have hsim : SpecSimulates (compress256MasterROSpec (pl.ρ sha2K32Sym))
      (withRoData (pl.ρ sha2K32Sym) sha256KBytes (compress256StackedMasterROSpec hookStack)) :=
    (compress256MasterRO_simulates_stackedMasterRO_roSep (pl.ρ sha2K32Sym) hstack).trans
      (SpecSimulates.withRoData_of_sep sha256KBytes_length_le)
  have hm_sim :=
    (LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift.SpecSimulates.withPlacedCodeLoaded
      hsim compress256Lib pl).subroutine_ok hm
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hLP
  have hL0 : (compress256Lib.program pl).CodeLoaded s0.mem := by
    have hb : (compress256SubProg pl).base = (compress256Lib.program pl).base := rfl
    have hc : (compress256SubProg pl).code = (compress256Lib.program pl).code := rfl
    refine Program.CodeLoaded.intro (hb ▸ hLP.aligned) (hb ▸ hc ▸ hLP.no_wrap) fun i hi => ?_
    have hi' : i < (compress256SubProg pl).code.length := hc.symm ▸ hi
    have hget? : (compress256SubProg pl).code[i]? = (compress256Lib.program pl).code[i]? :=
      congrArg (fun l => l[i]?) hc
    rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at hget?
    rw [← hb, ← Option.some.inj hget?]
    exact ⟨hLP.byte_eq i hi', hLP.perm_eq i hi', hLP.isLazyFree_eq i hi'⟩
  have hpre_cl : s0.mem ⊨
      (withPlacedCodeLoaded compress256Lib pl
        (withRoData (pl.ρ sha2K32Sym) sha256KBytes
          (compress256StackedMasterROSpec hookStack))).pre x s0 ∗ R := by
    dsimp only [withPlacedCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, satisfies_pure_sepConj]
    exact ⟨hL0, hpre⟩
  exact hm_sim.mono_outcome x R s0 hpc hrun hpre_cl hsp (fun _ h => h)

private theorem subroutine_ok_masterCompress256RO {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) :
    subroutine_ok (compress256SubProg pl) pl.base
      (withRoData (pl.ρ sha2K32Sym) sha256KBytes masterCompress256ROSpec) := by
  have hst := compress256StackedMasterRO_subroutine_ok hpl (by decide : 176 ≤ 176)
  apply subroutine_ok.of_codeLoaded
  intro ⟨ro, stA, st, blkA, bs, n⟩ R s0 hpc hrun hpre hsp _
  refine hst.mono_outcome (ro, stA, st, blkA, bs, n) R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withRoData, compress256StackedMasterROSpec] at hpost
    dsimp only [withRoData, masterCompress256ROSpec]
    simp only [sepConj_assoc] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨⟨hpf, _⟩, hmem⟩ := hpost
    rw [sha256CompressState_eq_spqrSha256Compress] at hmem
    exact ⟨⟨hpf.1, hpf.2.1, hpf.2.2.1, hpf.2.2.2.1, hpf.2.2.2.2.1,
            hpf.2.2.2.2.2.1, hpf.2.2.2.2.2.2.1⟩, hmem⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

private theorem subroutine_ok_masterCompress256ROLs [LibsignalPlacement] {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) :
    subroutine_ok (compress256SubProg pl) pl.base
      (withRoData (pl.ρ sha2K32Sym) sha256KBytes (withLsRet masterCompress256ROSpec)) :=
  subroutine_ok_withRoData_withLsRet (subroutine_ok_masterCompress256RO hpl)

private theorem compress256Hook_master_ok :
    HookOk (keepFsTrace (compress256Hook sha256Compress)) masterCompress256ROSpec := by
  rw [keepFsTrace_compress256Hook_eq]
  have hro := compress256Hook_roBudget_ok sha256Compress 176
  intro ⟨ro, stA, st, blkA, bs, n⟩ R s0 hrun hpre hsp
  have hpre_ro : s0.mem ⊨
      (sessionCompress256ROBudgetSpec sha256Compress 176).pre (ro, stA, st, blkA, bs, n) s0 ∗ R := by
    dsimp only [masterCompress256ROSpec, compress256StackedMasterROSpec] at hpre
    dsimp only [sessionCompress256ROBudgetSpec, sessionCompress256ROSpec]
    simp only [sepConj_assoc] at hpre ⊢
    rw [satisfies_pure_sepConj] at hpre ⊢
    exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1, hpre.1.2.2.2.1, hpre.1.2.2.2.2⟩, hpre.2⟩
  obtain ⟨hkf, hsym, hout⟩ := hro (ro, stA, st, blkA, bs, n) R s0 hrun hpre_ro hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [sessionCompress256ROBudgetSpec, sessionCompress256ROSpec] at hpost
    dsimp only [masterCompress256ROSpec]
    simp only [sepConj_assoc] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨_, hpost'⟩ := hpost
    rw [satisfies_pure_sepConj] at hpost'
    exact ⟨compress256Hook_memsetPreserved sha256Compress s0, hpost'.2⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

private theorem compress256Hook_masterLs_ok [LibsignalPlacement] :
    HookOk (keepFsTrace (compress256Hook sha256Compress)) (withLsRet masterCompress256ROSpec) :=
  hookOk_withLsRet compress256Hook_master_ok

theorem compress256Ghost_masterLs_ok [LibsignalPlacement] {pl : Obj.Placement}
    (hpl : compress256Lib.Placeable pl) :
    HookOk (compress256Ghost pl) (withLsRet masterCompress256ROSpec) :=
  hookOk_linkedCallHookG_roTable
    emptyStdProg_svc
    (compress256SubProg_svc pl)
    (fun _ _ => rfl)
    (compress256SubProg_externAt_none pl)
    (subroutine_ok_masterCompress256ROLs hpl)
    (specStripSInvariant_masterCompress256ROLs (keepR_compress256 pl))
    specPreservesFsTrace_masterCompress256ROLs
    masterCompress256ROLs_pre_setPC
    masterCompress256ROLs_outcome_setPC
    compress256Hook_masterLs_ok

theorem compress256Ghost_fs [LibsignalPlacement] (pl : Obj.Placement) (s : State) :
    (compress256Ghost pl s).fs = s.fs :=
  linkedCallHookG_fs _ _ _ _ _ _ _ s

theorem compress256Ghost_fsT [LibsignalPlacement] (pl : Obj.Placement) :
    HookFsTraced IsFsC (compress256Ghost pl) :=
  linkedCallHookG_fsT _ _ _ _ _ _ _

private theorem linkedCallHook_preserves_execFrozen {α : Type}
    {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hfb : ∀ s : State, ExecFrozen s.mem → ExecFrozen (fallback s).mem)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (linkedCallHook keep P_real P_sub entryTarget spec fallback u).mem := by
  classical
  unfold linkedCallHook
  split
  · split
    · rename_i hReal
      exact (Classical.choose_spec hReal.2.2.2).2.2.2.2
    · exact hfb u hfr
  · exact hfr

private theorem linkedCallHookG_preserves_execFrozen {α : Type}
    {Guard : State → Prop} {keep : BitVec 64 → Bool} {P_real P_sub : Program}
    {entryTarget : BitVec 64} {spec : Spec α} {fallback : State → State}
    (hfb : ∀ s : State, ExecFrozen s.mem → ExecFrozen (fallback s).mem)
    {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (linkedCallHookG Guard keep P_real P_sub entryTarget spec fallback u).mem := by
  classical
  unfold linkedCallHookG
  split
  · exact linkedCallHook_preserves_execFrozen hfb hfr
  · split
    · exact hfb u hfr
    · exact hfr

theorem compress256Ghost_preserves_execFrozen [LibsignalPlacement]
    (pl : Obj.Placement) {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (compress256Ghost pl u).mem := by
  unfold compress256Ghost
  refine linkedCallHookG_preserves_execFrozen (fun s hs => ?_) hfr
  exact ExecFrozen.of_perm_eq hs (compress256Hook_vm sha256Compress s).perm_eq

private theorem perm_eq_of_stripExecOutside_keepsFrozen
    {keepR : BitVec 64 → Bool} {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hfrf : ExecFrozen mf) (hkf : m0.KeepsFrozen mf)
    (hstrip : ∀ a : BitVec 64,
      (stripExecOutside keepR mf).perm a = (stripExecOutside keepR m0).perm a) :
    ∀ a : BitVec 64, mf.perm a = m0.perm a := by
  intro a
  have hst := hstrip a
  rw [strip_perm, strip_perm] at hst
  have hfr0_a := hfr0 a
  have hfrf_a := hfrf a
  by_cases hfrozen0 : m0.Frozen a
  · exact (hkf a hfrozen0).2.1
  · unfold Memory.Frozen Option.frozen Perm.frozen at hfrozen0
    cases hp0 : m0.perm a with
    | none =>
      cases hpf : mf.perm a with
      | none => rfl
      | some pf =>
        rw [hp0, hpf] at hst
        simp [Option.map] at hst
    | some p0 =>
      cases hpf : mf.perm a with
      | none =>
        rw [hp0, hpf] at hst
        simp [Option.map] at hst
      | some pf =>
        rw [hp0] at hfr0_a hfrozen0 hst
        rw [hpf] at hfrf_a hst
        rcases p0 with ⟨r0, w0, x0, lf0, an0⟩
        rcases pf with ⟨rf, wf, xf, lff, anf⟩
        unfold stripPerm at hst
        cases hk : keepR a <;> cases r0 <;> cases w0 <;> cases x0 <;>
          cases rf <;> cases wf <;> cases xf <;>
          simp_all [Option.map, Option.x, Option.r, Option.w]

private theorem keepsExec_of_execFrozen_keepsFrozen {m0 mf : Memory}
    (hfr0 : ExecFrozen m0) (hkf : m0.KeepsFrozen mf) :
    KeepsExec m0 mf := by
  intro a hx
  have hfr_a : m0.Frozen a := by
    have ⟨hr, hw⟩ := hfr0 a hx
    unfold Memory.Frozen Option.frozen Perm.frozen
    cases hp : m0.perm a with
    | none => simp [hp, Option.x] at hx
    | some p =>
      rw [hp] at hr hw
      rcases p with ⟨r, w, x, lf, an⟩
      simp [Option.r, Option.w] at hr hw
      subst hr hw
      rfl
  obtain ⟨hrd, hperm, hlf, han⟩ := hkf a hfr_a
  exact ⟨hrd, hperm, hlf, han⟩

private theorem activeRealRun_compress256_vm_acp_keepsExec [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress256Lib.Placeable pl)
    {s0 : State}
    (hG : roTableGuard (pl.ρ sha2K32Sym) sha256KBytes s0)
    (hAct : ActiveRealPre (withLsRet masterCompress256ROSpec) s0)
    (hReal : ActiveRealRun (keepR_compress256 pl) emptyStdProg (compress256SubProg pl) pl.base s0) :
    let sf := Classical.choose hReal.2.2.2
    VmPreserved s0 sf ∧ AllocCallPreserved s0 sf ∧ KeepsExec s0.mem sf.mem := by
  obtain ⟨hrun, hsp, x, R, hpreLs⟩ := hAct
  dsimp only [withLsRet] at hpreLs
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreLs
  obtain ⟨_, hpreM⟩ := hpreLs
  let s1 := s0.setPC pl.base
  let s1' := stripS (keepR_compress256 pl) s1
  have hG' : RoDataAt s1'.mem (pl.ρ sha2K32Sym) sha256KBytes :=
    roTableGuard_stripS (keepR_compress256 pl) pl.base (pl.ρ sha2K32Sym) sha256KBytes s0
      hReal.1 hG
  have hs1_pre : s1.mem ⊨ (compress256StackedMasterROSpec 176).pre x s1 ∗ R := by
    have heq : (compress256StackedMasterROSpec 176).pre x s1 = masterCompress256ROSpec.pre x s0 := by
      cases s0; rfl
    rwa [heq]
  have hs1'_std : s1'.mem ⊨ (compress256StackedMasterROSpec 176).pre x s1' ∗ R := by
    have heq : (compress256StackedMasterROSpec 176).pre x s1' =
        (compress256StackedMasterROSpec 176).pre x s1 := by
      dsimp only [s1']; cases s1; rfl
    rw [heq]
    exact satisfies_stripExecOutside (keepR_compress256 pl) hs1_pre
  have hs1'_pre :
      s1'.mem ⊨ (withRoData (pl.ρ sha2K32Sym) sha256KBytes
        (compress256StackedMasterROSpec 176)).pre x s1' ∗ R := by
    dsimp only [withRoData]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hG', hs1'_std⟩
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome
      (compress256StackedMasterRO_subroutine_ok hpl (by decide : 176 ≤ 176))
      x R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
  rcases hout' with ⟨hret', _, hpost'⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · have hstop0' : SubroutineStop s0 sf' := Or.inl hret'
    have hnhalt' : sf'.status ≠ .Halted := by rw [hret'.2.2]; decide
    obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
      stepsUntil_of_stripS_standard (s0 := s0)
        emptyStdProg_svc (compress256SubProg_svc pl) (fun _ _ => rfl)
        (fun pc _ he => nomatch compress256SubProg_externAt_none pl pc ▸ he)
        hReal.2.1 hsteps' hstop0' hnhalt' s1 rfl hReal.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
    dsimp only
    rw [hdet]
    dsimp only [withRoData, compress256StackedMasterROSpec] at hpost'
    simp only [sepConj_assoc] at hpost'
    rw [satisfies_pure_sepConj] at hpost'
    obtain ⟨⟨hpf', hacp'⟩, _⟩ := hpost'
    rw [hsf_eq] at hpf' hacp'
    have hperm : ∀ a, sf.mem.perm a = s0.mem.perm a :=
      perm_eq_of_stripExecOutside_keepsFrozen hReal.1 hfr_sf huntil.toSteps.keepsFrozen
        hpf'.2.2.2.2.2.2.2
    have htp : sf.tpidrEl0 = s0.tpidrEl0 := by cases s0; cases sf; exact hpf'.2.2.1
    have hbrk : sf.brk = s0.brk := by cases s0; cases sf; exact hpf'.2.2.2.2.1
    have hbrkS : sf.brkStart = s0.brkStart := by cases s0; cases sf; exact hpf'.2.2.2.2.2.1
    have hphys : sf.physMemAvail = s0.physMemAvail := by
      cases s0; cases sf; exact hpf'.2.2.2.2.2.2.1
    have hfs : sf.fs = s0.fs := by cases s0; cases sf; exact hpf'.1
    have hvm : VmPreserved s0 sf :=
      ⟨⟨hbrkS, hbrk, htp⟩, hphys, hperm, FdsHiFrame.of_fs_eq hfs⟩
    have hacp : AllocCallPreserved s0 sf := by
      cases s0; cases sf; exact hacp'
    exact ⟨hvm, hacp, keepsExec_of_execFrozen_keepsFrozen hReal.1 huntil.toSteps.keepsFrozen⟩
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem compress256Ghost_vmPreserved [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress256Lib.Placeable pl) (s0 : State) :
    VmPreserved s0 (compress256Ghost pl s0) := by
  classical
  unfold compress256Ghost linkedCallHookG
  by_cases hG : roTableGuard (pl.ρ sha2K32Sym) sha256KBytes s0
  · simp only [hG, ↓reduceDIte]
    unfold linkedCallHook
    by_cases hAct : ActiveRealPre (withLsRet masterCompress256ROSpec) s0
    · simp only [hAct, ↓reduceDIte]
      by_cases hReal : ActiveRealRun (keepR_compress256 pl) emptyStdProg (compress256SubProg pl) pl.base s0
      · simp only [hReal, ↓reduceDIte]
        exact (activeRealRun_compress256_vm_acp_keepsExec hpl hG hAct hReal).1
      · simp only [hReal, ↓reduceDIte, keepFsTrace_compress256Hook_eq]
        exact compress256Hook_vm sha256Compress s0
    · simp only [hAct, ↓reduceDIte]
      exact VmPreserved.refl s0
  · simp only [hG, ↓reduceDIte]
    by_cases hAct : ActiveRealPre (withLsRet masterCompress256ROSpec) s0
    · simp only [hAct, ↓reduceDIte, keepFsTrace_compress256Hook_eq]
      exact compress256Hook_vm sha256Compress s0
    · simp only [hAct, ↓reduceDIte]
      exact VmPreserved.refl s0

private theorem compress256Hook_acp (F : ShaState → List (BitVec 8) → ShaState) (s0 : State) :
    AllocCallPreserved s0 (compress256Hook F s0) := by
  unfold compress256Hook returnToLinkRegister
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem compress256Ghost_allocCallPreserved [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress256Lib.Placeable pl) (s0 : State) :
    AllocCallPreserved s0 (compress256Ghost pl s0) := by
  classical
  unfold compress256Ghost linkedCallHookG
  by_cases hG : roTableGuard (pl.ρ sha2K32Sym) sha256KBytes s0
  · simp only [hG, ↓reduceDIte]
    unfold linkedCallHook
    by_cases hAct : ActiveRealPre (withLsRet masterCompress256ROSpec) s0
    · simp only [hAct, ↓reduceDIte]
      by_cases hReal : ActiveRealRun (keepR_compress256 pl) emptyStdProg (compress256SubProg pl) pl.base s0
      · simp only [hReal, ↓reduceDIte]
        exact (activeRealRun_compress256_vm_acp_keepsExec hpl hG hAct hReal).2.1
      · simp only [hReal, ↓reduceDIte, keepFsTrace_compress256Hook_eq]
        exact compress256Hook_acp sha256Compress s0
    · simp only [hAct, ↓reduceDIte]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [hG, ↓reduceDIte]
    by_cases hAct : ActiveRealPre (withLsRet masterCompress256ROSpec) s0
    · simp only [hAct, ↓reduceDIte, keepFsTrace_compress256Hook_eq]
      exact compress256Hook_acp sha256Compress s0
    · simp only [hAct, ↓reduceDIte]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem compress256Ghost_keepsExec [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress256Lib.Placeable pl) (s0 : State)
    (hrw : s0.mem.RW (s0.readReg64 .x0) 32) :
    KeepsExec s0.mem (compress256Ghost pl s0).mem := by
  classical
  unfold compress256Ghost linkedCallHookG
  by_cases hG : roTableGuard (pl.ρ sha2K32Sym) sha256KBytes s0
  · simp only [hG, ↓reduceDIte]
    unfold linkedCallHook
    by_cases hAct : ActiveRealPre (withLsRet masterCompress256ROSpec) s0
    · simp only [hAct, ↓reduceDIte]
      by_cases hReal : ActiveRealRun (keepR_compress256 pl) emptyStdProg (compress256SubProg pl) pl.base s0
      · simp only [hReal, ↓reduceDIte]
        exact (activeRealRun_compress256_vm_acp_keepsExec hpl hG hAct hReal).2.2
      · simp only [hReal, ↓reduceDIte, keepFsTrace_compress256Hook_eq]
        exact compress256Hook_keepsExec sha256Compress s0 hrw
    · simp only [hAct, ↓reduceDIte]
      exact fun _ _ => ⟨rfl, rfl, rfl, rfl⟩
  · simp only [hG, ↓reduceDIte]
    by_cases hAct : ActiveRealPre (withLsRet masterCompress256ROSpec) s0
    · simp only [hAct, ↓reduceDIte, keepFsTrace_compress256Hook_eq]
      exact compress256Hook_keepsExec sha256Compress s0 hrw
    · simp only [hAct, ↓reduceDIte]
      exact fun _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-! ## 3. Consumer `HookOk` Arms & `Compress256RowSpec` -/

private theorem state_pointsToBytes_length_le {stA blkA : BitVec 64} {st : ShaState}
    {bs : List (BitVec 8)} {m : Memory} {R : SepProp}
    (h : m ⊨ (stA ↦ₛ shaStateBytes st) ∗ ((blkA ↦ₛ bs) ∗ R)) :
    bs.length ≤ 2 ^ 64 := by
  rcases Nat.eq_zero_or_pos bs.length with h0 | hpos
  · omega
  · rw [LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math.pointsToBytes_shaStateBytes,
        sepConj_assoc, sepConj_left_comm _ (blkA ↦ₛ bs)] at h
    have hd := (IsBlock.pointsTo32 stA (st.toList.getD 0 0#32)).disjoint
      (IsBlock.pointsToBytes blkA bs) (by decide) hpos h
    have hlt := (stA - blkA).isLt
    have h2 := hd.2
    omega

theorem compress256Ghost_roBudget_ok [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress256Lib.Placeable pl)
    (stk : Nat) (hstk : 176 ≤ stk) :
    HookOk (compress256Ghost pl)
      (withLsRet (sessionCompress256ROBudgetSpec sha256Compress stk)) := by
  have hm := compress256Ghost_masterLs_ok hpl
  intro ⟨ro, stA, st, blkA, bs, n⟩ R s0 hrun hpre hsp
  dsimp only [withLsRet, sessionCompress256ROBudgetSpec, sessionCompress256ROSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨hlr, hpre'⟩ := hpre
  rw [satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hx0, hx1, hx2, hlen, hbs_le⟩, hmem⟩ := hpre'
  have hstk_le : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ (stA ↦ₛ shaStateBytes st) ∗
        (stackAt s0.sp stk ∗ (compress256Blocks ro blkA bs ∗ R)) := by
      ac_nf at hmem ⊢
    exact stackAt_le_two_pow_64 hm_stk
  rw [stackAt_split_frame176 s0 hstk hstk_le] at hmem
  let R₁ := stackAt (s0.sp - 176#64) (stk - 176) ∗ R
  have hpreM : s0.mem ⊨
      (withLsRet masterCompress256ROSpec).pre (ro, stA, st, blkA, bs, n) s0 ∗ R₁ := by
    dsimp only [withLsRet, masterCompress256ROSpec, compress256StackedMasterROSpec, R₁]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨hlr, ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen, hbs_le⟩, ?_⟩
    simpa only [sepConj_assoc] using hmem
  obtain ⟨hkf, hsym, hout⟩ := hm (ro, stA, st, blkA, bs, n) R₁ s0 hrun hpreM hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRet, masterCompress256ROSpec, R₁] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hmsp, hmem_f⟩ := hpost
    dsimp only [withLsRet, sessionCompress256ROBudgetSpec, sessionCompress256ROSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨⟨compress256Ghost_vmPreserved hpl s0, compress256Ghost_allocCallPreserved hpl s0⟩, ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨hmsp.2.1, ?_⟩
    rw [stackAt_split_frame176 s0 hstk hstk_le]
    simpa only [sepConj_assoc] using hmem_f
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem compress256Ghost_multi_ok [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress256Lib.Placeable pl)
    (stk : Nat) (hstk : 176 ≤ stk) :
    HookOk (compress256Ghost pl)
      (withLsRet (withStack (compress256Spec sha256Compress) stk)) := by
  have hro := compress256Ghost_roBudget_ok hpl stk hstk
  intro ⟨stA, st, blkA, bs, n⟩ R s0 hrun hpre hsp
  dsimp only [withLsRet, withStack, compress256Spec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨hlr, hpre'⟩ := hpre
  rw [satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩ := hpre'
  have hbs_le : bs.length ≤ 2 ^ 64 := state_pointsToBytes_length_le hmem
  have hpre_ro : s0.mem ⊨
      (withLsRet (sessionCompress256ROBudgetSpec sha256Compress stk)).pre
        (false, stA, st, blkA, bs, n) s0 ∗ R := by
    dsimp only [withLsRet, sessionCompress256ROBudgetSpec, sessionCompress256ROSpec, compress256Blocks]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨hlr, (satisfies_pure_sepConj ..).mpr ⟨⟨hx0, hx1, hx2, ⟨hlen, hbs_le⟩⟩, hmem⟩⟩
  obtain ⟨hkf, hsym, hout⟩ := hro (false, stA, st, blkA, bs, n) R s0 hrun hpre_ro hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRet, sessionCompress256ROBudgetSpec, sessionCompress256ROSpec,
      compress256Blocks] at hpost
    dsimp only [withLsRet, withStack, compress256Spec]
    simp only [sepConj_assoc] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨_, hpost'⟩ := hpost
    rw [satisfies_pure_sepConj] at hpost' ⊢
    exact hpost'
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem compress256Ghost_single_ok [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress256Lib.Placeable pl)
    (stk : Nat) (hstk : 176 ≤ stk) :
    HookOk (compress256Ghost pl)
      (withLsRet (withStack (compress256RowSingleSpec sha256Compress) stk)) := by
  have hm := compress256Ghost_multi_ok hpl stk hstk
  intro ⟨stA, st, blkA, blk⟩ R s0 hrun hpre hsp
  dsimp only [withLsRet, withStack, compress256RowSingleSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨hlr, hpre'⟩ := hpre
  rw [satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩ := hpre'
  have hx2_nat : (s0.readReg64 .x2).toNat = 1 := by rw [hx2]; decide
  have hpre_m : s0.mem ⊨
      (withLsRet (withStack (compress256Spec sha256Compress) stk)).pre
        (stA, st, blkA, blk, 1) s0 ∗ R := by
    dsimp only [withLsRet, withStack, compress256Spec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨hlr, (satisfies_pure_sepConj ..).mpr ⟨⟨hx0, hx1, hx2_nat, by omega⟩, hmem⟩⟩
  obtain ⟨hkf, hsym, hout⟩ := hm (stA, st, blkA, blk, 1) R s0 hrun hpre_m hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRet, withStack, compress256Spec] at hpost
    dsimp only [withLsRet, withStack, compress256RowSingleSpec]
    simp only [sepConj_assoc] at hpost ⊢
    have hchunks : chunks64 blk = [blk] := by
      rw [chunks64_cons_take_drop (by omega), List.take_of_length_le (by omega),
          List.drop_eq_nil_of_le (by omega), chunks64_of_length_lt (by decide)]
    rw [hchunks, List.foldl_cons, List.foldl_nil] at hpost
    exact hpost
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem compress256Ghost_compress256RowSpec [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress256Lib.Placeable pl) :
    Compress256RowSpec (compress256Ghost pl) :=
  Compress256RowSpec.of_ls_vm
    (compress256Ghost_keepsExec hpl)
    (compress256Ghost_roBudget_ok hpl)
    (compress256Ghost_multi_ok hpl)
    (compress256Ghost_single_ok hpl)
    (compress256Ghost_vmPreserved hpl)

/-! ## 4. `GhostRowSpecOk`, `GhostRowReplayOn`, & `GhostRowOk` -/

theorem compress256Ghost_rowSpecOk [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress256Lib.Placeable pl) :
    GhostRowSpecOk lsCompress256Sym (compress256Ghost pl) where
  fs_eq := compress256Ghost_fs pl
  fsT := compress256Ghost_fsT pl
  rowSpec := by
    unfold ExtraRowSpec
    have hd1 : (lsCompress256Sym == "bcmp") = false := by decide
    have hd2 : (lsCompress256Sym == "strlen") = false := by decide
    have hd3 : (lsCompress256Sym == "memmove") = false := by decide
    have hd4 : (lsCompress256Sym == lsFromUtf8Sym) = false := by decide
    have hd5 : (lsCompress256Sym == lsMemrchrSym) = false := by decide
    have hd6 : (lsCompress256Sym == lsDurationSinceSym) = false := by decide
    have hd7 : (lsCompress256Sym == lsTimeAddSym) = false := by decide
    have hd8 : (lsCompress256Sym == lsBlackBoxSym) = false := by decide
    have hd9 : (lsCompress256Sym == lsStaticSecretDropSym) = false := by decide
    have hd10 : (lsCompress256Sym == lsSharedSecretDropSym) = false := by decide
    have hd11 : (lsCompress256Sym == lsCompress256Sym) = true := by decide
    simp only [hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10, hd11,
      Bool.false_eq_true, ↓reduceIte]
    exact compress256Ghost_compress256RowSpec hpl

private theorem setPC_eq_self_of_pc_eq {u : State} {pc : BitVec 64} (hpc : u.pc = pc) :
    u.setPC pc = u := by
  cases u
  dsimp only [State.setPC] at hpc ⊢
  subst hpc
  rfl

private theorem realProg617_svc (mpl mmpl : Obj.MultiPlacement) (W : CliHooks) :
    (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).svc = Syscall.standard :=
  rfl

private theorem emptyStdProg_externAt (pc : BitVec 64) :
    emptyStdProg.externAt? pc = none :=
  rfl

/-- Behind-stub (`StubReachesTargetOn`) `GhostRowReplayOn` for `lsCompress256Sym`. -/
theorem compress256Ghost_rowReplayOn_of_stub [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (pl : Obj.Placement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : compress256Lib.Placeable pl)
    (hCL : ∀ u : State, InvS u → (compress256SubProg pl).CodeLoaded u.mem)
    (hRo : ∀ u : State, InvS u → RoDataAt u.mem (pl.ρ sha2K32Sym) sha256KBytes)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_compress256 pl lr = false)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_compress256 pl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl lsCompress256Sym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn
        (fun m => (compress256SubProg pl).CodeLoaded m ∧
          RoDataAt m (pl.ρ sha2K32Sym) sha256KBytes)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl lsCompress256Sym)
        pl.base) :
    GhostRowReplayOn mpl mmpl InvS EG lsCompress256Sym (fun _ => True)
      (compress256Ghost pl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨compress256Ghost_preserves_execFrozen pl hfr,
     compress256Ghost_fs pl u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    have hRep :=
      ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis
        (InvMem := fun m => (compress256SubProg pl).CodeLoaded m ∧
          RoDataAt m (pl.ρ sha2K32Sym) sha256KBytes)
        (keep := keepR_compress256 pl)
        (P_run := emptyStdProg)
        (P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (P_sub := compress256SubProg pl)
        (stubPc := libsignalSessionLib.resolve mpl lsCompress256Sym)
        (entryTarget := pl.base)
        (tbl := pl.ρ sha2K32Sym)
        (bytes := sha256KBytes)
        (fallback := compress256Hook sha256Compress)
        emptyStdProg_svc
        (compress256SubProg_svc pl)
        (fun pc _ => emptyStdProg_externAt pc)
        (compress256SubProg_externAt_none pl)
        (hRealStubNone W)
        (hStub W)
        (fun _ _ _ _ _ hvis =>
          h2fsgen_steps_lift_of_visitedIn_noExtern
            (D := keepR_compress256 pl)
            (P1 := emptyStdProg)
            (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
            (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
            (fun pc _ => emptyStdProg_externAt pc)
            (fun _ hk => hRealHullNoExt W hk)
            hvis)
        (fun _ _ hInvM => compress256SubProg_codeLoaded_stripExecOutside hpl hInvM.1)
        (fun _ _ hInvM hkf =>
          ⟨hInvM.1.of_keepsFrozen hkf, roDataAt_of_keepsFrozen hInvM.2 hkf⟩)
        (fun _ _ hInvM => hInvM.2)
        (subroutine_ok_masterCompress256ROLs hpl)
        (specStripSInvariant_masterCompress256ROLs (keepR_compress256 pl))
        specPreservesFsTrace_masterCompress256ROLs
        masterCompress256ROLs_pre_setPC
        masterCompress256ROLs_outcome_setPC
    refine ⟨hRep.1, ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hlr : keepR_compress256 pl (u.readReg64 .lr) = false :=
      keepLr_false_of_noException_via_activeRealPre
        hKeep linkedCallHookG_activeRealPre_of_noException hnoex
    obtain ⟨hSteps1, hfr1, _⟩ :=
      hRep.2 u hpc hrun hnoex hfr hlr ⟨hCL u hInvU, hRo u hInvU⟩
    exact ⟨hSteps1, hfr1,
      hInvKeep u (compress256Ghost pl u) hInvU hkf (compress256Ghost_fs pl u)⟩

/-- Direct `.text.lib2` `GhostRowReplayOn` for `lsCompress256Sym` (`entryGuard := fun _ => True`). -/
theorem compress256Ghost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (pl : Obj.Placement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : compress256Lib.Placeable pl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsCompress256Sym = pl.base)
    (hCL : ∀ u : State, InvS u → (compress256SubProg pl).CodeLoaded u.mem)
    (hRo : ∀ u : State, InvS u → RoDataAt u.mem (pl.ρ sha2K32Sym) sha256KBytes)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_compress256 pl lr = false)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_compress256 pl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG lsCompress256Sym (fun _ => True)
      (compress256Ghost pl) :=
  compress256Ghost_rowReplayOn_of_stub mpl mmpl pl InvS EG hpl hCL hRo hInvKeep hKeep
    hRealHullNoExt
    (fun W => by rw [hTargetEq]; exact hRealHullNoExt W (keepR_compress256_entry pl))
    (fun _ u hpc _ _ _ => by
      rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)]
      exact Steps.refl _)

/-- Full per-row `GhostRowOk` bundle (`GhostRowSpecOk` ∧ `GhostRowReplayOn`) for
    `lsCompress256Sym` (`entryGuard := fun _ => True`). -/
theorem compress256Ghost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (pl : Obj.Placement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : compress256Lib.Placeable pl)
    (hTargetEq : libsignalSessionLib.resolve mpl lsCompress256Sym = pl.base)
    (hCL : ∀ u : State, InvS u → (compress256SubProg pl).CodeLoaded u.mem)
    (hRo : ∀ u : State, InvS u → RoDataAt u.mem (pl.ρ sha2K32Sym) sha256KBytes)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_compress256 pl lr = false)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_compress256 pl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl InvS EG lsCompress256Sym (fun _ => True)
      (compress256Ghost pl) :=
  ⟨compress256Ghost_rowSpecOk hpl,
   compress256Ghost_rowReplayOn mpl mmpl pl InvS EG hpl hTargetEq hCL hRo hInvKeep hKeep
     hRealHullNoExt⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress256GhostReplays
