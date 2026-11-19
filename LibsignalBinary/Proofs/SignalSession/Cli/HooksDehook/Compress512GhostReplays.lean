/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress512RowSpec -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
import LibsignalBinary.Heap.IfaceBudgetLemmas
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget
import ProofLib.Process.OracleEq

/-!
# `sha2::sha512::compress512` Route-`R0` `GhostRowReplayOn` (`HooksDehook.Compress512GhostReplays`)

Stage-B consumer-closure module for `lsCompress512SymCli` (`compress512Sym`,
`sha2::sha512::compress512`) on the Route-`R0` (`WithLsRet.withLsRet` / `LsRetAddr624`)
`.text.lib2` track:

1. **Row Anchor & `W`-Independent Ghost (`keepR_compress512`, `compress512SubProg`, `compress512Ghost`):**
   - `compress512SubProg pl` places `compress512Lib` (`9,652` B = `2,413` words at `pl.base`, zero
     external call stubs) with `Syscall.standard`.
   - `masterCompress512Spec` separates `mem.perm` out of `.post` (`MemsetStatePreserved`), so
     `SpecStripSInvariant keep masterCompress512Spec` holds definitionally (`rfl`), while
     `compress512StackedMasterSpec 256` (`ProcessFieldsPreserved`) recovers full `mem.perm`
     preservation (`VmPreserved` + `AllocCallPreserved`) on the active real branch.
   - `compress512Ghost pl` wraps `withLsRet masterCompress512Spec` via
     `linkedCallHookG (roTableGuard (pl.ρ sha2K64Sym) sha512KBytes)` on `emptyStdProg` with
     `W`-independent fallback `E2E.compress512Hook sha512CompressState`.
2. **State Preservation, `HookNoAllocFailed`, & `withLsRet` Consumer `HookOk` Arms:**
   - Unconditional (`0` layout premises) `compress512Ghost_fs`, `compress512Ghost_fsT`,
     `compress512Ghost_trace`, `compress512Ghost_noAllocFailed`, and
     `compress512Ghost_preserves_execFrozen`.
   - Under `hpl : compress512Lib.Placeable pl`: `compress512Ghost_vmPreserved`,
     `compress512Ghost_allocCallPreserved`, and `Compress512RowSpec (compress512Ghost pl)` (`256 ≤ stk`).
3. **Generic-`InvS` `GhostRowReplayOn` & `GhostRowOk` (`entryGuard := fun _ => True`).**
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress512GhostReplays

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E
  (Sha512State chunks128 compress512Hook readSha512State sha512StateBytesLE)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister toLEBytes)
open CryptoVerification.SignalSession (CliHooks cliExternsPlaced libsignalSessionLib)
open CryptoVerification.SignalSession.Cli.RunGlue (IsFsC)
open LibsignalBinary.Heap (AllocCallPreserved FdsHiFrame VmPreserved)
open LibsignalBinary.Heap.IfaceBudgetLemmas (perm_writeBytes_norm)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512
  (compress512StackedMasterSpec compress512_master_ok)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Code
  (compress512Block compress512Lib compress512Sym compress512_code_eq
   compress512_tree_size sha2K64Sym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Compress512Loop (compress512_fnAddr)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Cells (sha512KBytes)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.Sha512Ref (sha512CompressState)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha512.StepsLift
  (stackAt_le_two_pow_64 stackAt_split_frame256 withPlacedCodeLoaded)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Common (RoDataAt withRoData)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (ActiveRealPre ActiveRealRun ExecFrozen SpecPreservesFsTrace SpecStripSInvariant
   keepFsTrace linkedCallHook satisfies_stripExecOutside stepsUntil_of_stripS_standard)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HInit.CliInitSlotOkPlacedAt
  (HookNoAllocFailed hookNoAllocFailed_of_trace_eq)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.F3HarnessPlaced (cliProgExtPlacedAt)
open LibsignalBinary.Proofs.SignalSession.Cli.F3.L4B.Ghost617Transfer (StubReachesTargetOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.ExtraGhostReplay
  (GhostRowOk GhostRowReplayOn)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookG
  (ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis hookOk_linkedCallHookG_roTable
   linkedCallHookG linkedCallHookG_activeRealPre_of_noException linkedCallHookG_fs
   linkedCallHookG_fsT roDataAt_of_keepsFrozen roTableGuard roTableGuard_stripS)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.LinkedCallHookLs
  (keepLr_false_of_noException_via_activeRealPre specPreservesFsTrace_withLsRet
   specStripSInvariant_withLsRet subroutine_ok_withRoData_withLsRet)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (MemsetStatePreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetGhostK
  (emptyStdProg emptyStdProg_svc)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.TrapSafeWords
  (codeLoaded_stripExecOutside_of_keep)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet
  (hookOk_withLsRet withLsRet withLsRet_outcome_setPC withLsRet_pre_setPC)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraGhostSpecs
  (ExtraRowSpec GhostRowSpecOk)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ExtraRowSpecs.Compress512RowSpec
  (Compress512RowSpec)
open LibsignalBinary.Proofs.SpecLemmas.SignalSession.ElfSlicesPqOomH2FirstStopGeneric
  (h2fsgen_steps_lift_of_visitedIn_noExtern)

/-! ## 1. Row Anchor Definitions & Strip-Invariant Master Spec -/

/-- Byte length (`9,652` B = `2,413` words) of `sha2::sha512::compress512`. -/
@[expose] def compress512ByteLen : Nat := 9652

/-- Canonical `Obj.Placement` for `compress512Lib` at code base `base` and `K64` `.rodata`
    address `k64Addr`. -/
@[expose] def compress512Placement (base k64Addr : BitVec 64) : Obj.Placement where
  base := base
  ρ sym := if sym == sha2K64Sym then k64Addr else 0#64

theorem compress512Placement_base (base k64Addr : BitVec 64) :
    (compress512Placement base k64Addr).base = base :=
  rfl

theorem compress512Placement_k64 (base k64Addr : BitVec 64) :
    (compress512Placement base k64Addr).ρ sha2K64Sym = k64Addr := by
  simp [compress512Placement]

/-- Kept-region byte predicate `[pl.base, pl.base + 9652)` covering `compress512Lib`. -/
@[expose] def keepR_compress512 (pl : Obj.Placement) (pc : BitVec 64) : Bool :=
  decide ((pc - pl.base).toNat < compress512ByteLen)

theorem keepR_compress512_entry (pl : Obj.Placement) :
    keepR_compress512 pl pl.base = true := by
  unfold keepR_compress512 compress512ByteLen
  have hsub : pl.base - pl.base = 0#64 := by bv_omega
  rw [hsub]
  decide

/-- Pure `2,413`-word (`9,652`-byte) sub-program holding `compress512Lib` at `pl.base` with
    `Syscall.standard`. -/
@[expose] def compress512SubProg (pl : Obj.Placement) : Program :=
  { compress512Lib.program pl (fun _ => none) with svc := Syscall.standard }

theorem compress512SubProg_base (pl : Obj.Placement) :
    (compress512SubProg pl).base = pl.base :=
  rfl

theorem compress512SubProg_svc (pl : Obj.Placement) :
    (compress512SubProg pl).svc = Syscall.standard :=
  rfl

theorem compress512SubProg_externAt_none (pl : Obj.Placement) (pc : BitVec 64) :
    (compress512SubProg pl).externAt? pc = none := by
  simp [compress512SubProg, compress512Lib, compress512Block,
    Obj.PlacedLib.program, Program.externAt?, Program.hookAtOff?]

set_option maxRecDepth 400000 in
theorem compress512SubProg_code_length {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) :
    (compress512SubProg pl).code.length = compress512ByteLen := by
  have hc : (compress512SubProg pl).code = compress512Lib.text.patched pl := rfl
  rw [hc, Obj.CodeBlock.length_patched_of_aligned pl hpl.text.len_aligned,
      compress512_code_eq,
      ProofLib.ProgramReflection.WordTree.length_toBytes_of_checkSize? compress512_tree_size]
  rfl

theorem keepR_compress512_of_code_offset {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) {i : Nat}
    (hi : i < (compress512SubProg pl).code.length) :
    keepR_compress512 pl ((compress512SubProg pl).base + BitVec.ofNat 64 i) = true := by
  rw [compress512SubProg_code_length hpl] at hi
  rw [compress512SubProg_base]
  unfold keepR_compress512
  have hi2 : i < 2 ^ 64 := by
    unfold compress512ByteLen at hi
    omega
  have hsub : pl.base + BitVec.ofNat 64 i - pl.base = BitVec.ofNat 64 i := by bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi2]
  exact decide_eq_true hi

theorem compress512SubProg_codeLoaded_stripExecOutside {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) {mem : Memory}
    (hL : (compress512SubProg pl).CodeLoaded mem) :
    (compress512SubProg pl).CodeLoaded (stripExecOutside (keepR_compress512 pl) mem) :=
  codeLoaded_stripExecOutside_of_keep (fun _ hi => keepR_compress512_of_code_offset hpl hi) hL

theorem compress512SubProg_codeLoaded_of_stripExecOutside {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) {mem : Memory}
    (hL : (compress512SubProg pl).CodeLoaded (stripExecOutside (keepR_compress512 pl) mem)) :
    (compress512SubProg pl).CodeLoaded mem := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hk := keepR_compress512_of_code_offset hpl hi
  have hbyte := hL.byte_eq i hi
  have hperm := hL.perm_eq i hi
  have hlf := hL.isLazyFree_eq i hi
  rw [ProofLib.strip_read8] at hbyte
  rw [ProofLib.strip_perm_of_keep hk] at hperm
  rw [ProofLib.strip_isLazyFree] at hlf
  exact ⟨hbyte, hperm, hlf⟩

/-- Strip-invariant `256`-B master `compress512` contract (`rfl`-identical `.pre` to
    `compress512StackedMasterSpec 256`, with `MemsetStatePreserved` in `.post` so
    `SpecStripSInvariant keep masterCompress512Spec` holds definitionally). -/
@[expose] def masterCompress512Spec :
    Spec (BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat) where
  pre := (compress512StackedMasterSpec 256).pre
  post := fun (stA, st, blkA, bs, _) s0 sf =>
    ⌜MemsetStatePreserved s0 sf⌝ ∗
      (stA ↦ₛ sha512StateBytesLE ((chunks128 bs).foldl sha512CompressState st)) ∗
      (blkA ↦ₛ bs) ∗ stackAt s0.sp 256
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Route-`R0` (`withLsRet`) `W`-independent ghost hook for `compress512Sym`
    (`lsCompress512SymCli`). -/
@[expose] noncomputable def compress512Ghost [LibsignalPlacement]
    (pl : Obj.Placement) : State → State :=
  linkedCallHookG
    (roTableGuard (pl.ρ sha2K64Sym) sha512KBytes)
    (keepR_compress512 pl)
    emptyStdProg
    (compress512SubProg pl)
    pl.base
    (withLsRet masterCompress512Spec)
    (compress512Hook sha512CompressState)

/-- Convenience wrapper constructing `compress512Ghost` directly from `(base, k64Addr)`. -/
noncomputable abbrev compress512MplGhost [LibsignalPlacement]
    (base k64Addr : BitVec 64) : State → State :=
  compress512Ghost (compress512Placement base k64Addr)

/-- Block-`617` entry-state guard for Route-`R0` `compress512Sym` (`True`: `LsRetAddr624` is
    extracted directly from non-`.Exception` at each call step). -/
@[expose] def compress512EntryGuard (_mpl : Obj.MultiPlacement) (_s0 : State) : Prop :=
  True

/-! ## 2. Pure Fallback Lemmas & Master `subroutine_ok` -/

private theorem keepFsTrace_compress512Hook_eq
    (F : Sha512State → List (BitVec 8) → Sha512State) :
    keepFsTrace (compress512Hook F) = compress512Hook F := by
  funext s
  unfold keepFsTrace compress512Hook returnToLinkRegister
  rfl

private theorem compress512Hook_vm
    (F : Sha512State → List (BitVec 8) → Sha512State) (s : State) :
    VmPreserved s (compress512Hook F s) := by
  refine ⟨⟨rfl, rfl, ?_⟩, rfl, fun a => ?_, FdsHiFrame.of_fs_eq rfl⟩
  · unfold compress512Hook returnToLinkRegister; rfl
  · unfold compress512Hook returnToLinkRegister
    dsimp only [State.setPC, State.setMem]
    exact congrFun (perm_writeBytes_norm s.mem (s.readReg64 .x0) _) a

private theorem compress512Hook_acp
    (F : Sha512State → List (BitVec 8) → Sha512State) (s0 : State) :
    AllocCallPreserved s0 (compress512Hook F s0) := by
  unfold compress512Hook returnToLinkRegister
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem compress512Hook_memsetPreserved
    (F : Sha512State → List (BitVec 8) → Sha512State) (s : State) :
    MemsetStatePreserved s (compress512Hook F s) := by
  unfold compress512Hook returnToLinkRegister MemsetStatePreserved
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem sha512State_toList_eq (h : Sha512State) :
    h.toList = [h.get 0, h.get 1, h.get 2, h.get 3, h.get 4, h.get 5, h.get 6, h.get 7] := by
  rcases h with
    ⟨_ | ⟨w0, _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, _ | ⟨w4, _ | ⟨w5, _ | ⟨w6, _ | ⟨w7, _ | _⟩⟩⟩⟩⟩⟩⟩⟩, hl⟩
  all_goals (first | rfl | (simp at hl))

private theorem sha512StateBytesLE_length (h : Sha512State) :
    (sha512StateBytesLE h).length = 64 := by
  rw [sha512StateBytesLE, sha512State_toList_eq]; rfl

private theorem readBytes_pointsToBytes_take {m : Memory} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} {k : Nat} (hk : k ≤ bs.length) (h : m ⊨ (p ↦ₛ bs) ∗ R) :
    m.readBytes p k = bs.take k := by
  have hsplit : (p ↦ₛ bs) =
      (p ↦ₛ bs.take k) ∗ ((p + BitVec.ofNat 64 (bs.take k).length) ↦ₛ bs.drop k) := by
    conv_lhs => rw [← List.take_append_drop k bs, pointsToBytes_append]
  rw [hsplit, sepConj_assoc] at h
  have hread := ((IsBlock.pointsToBytes p (bs.take k)).read h).2
  rwa [List.length_take_of_le hk] at hread

private theorem readBytes_pointsToBytes_slice {m : Memory} {p : BitVec 64} {bs : List (BitVec 8)}
    {R : SepProp} (k n : Nat) (hkn : k + n ≤ bs.length) (h : m ⊨ (p ↦ₛ bs) ∗ R) :
    m.readBytes (p + BitVec.ofNat 64 k) n = (bs.drop k).take n := by
  have hsplit : (p ↦ₛ bs) =
      (p ↦ₛ bs.take k) ∗ ((p + BitVec.ofNat 64 (bs.take k).length) ↦ₛ bs.drop k) := by
    conv_lhs => rw [← List.take_append_drop k bs, pointsToBytes_append]
  rw [hsplit, List.length_take_of_le (by omega), sepConj_assoc] at h
  have h' : m ⊨ ((p + BitVec.ofNat 64 k) ↦ₛ bs.drop k) ∗ ((p ↦ₛ bs.take k) ∗ R) := by
    rw [show ((p + BitVec.ofNat 64 k) ↦ₛ bs.drop k) ∗ ((p ↦ₛ bs.take k) ∗ R) =
      (p ↦ₛ bs.take k) ∗ (((p + BitVec.ofNat 64 k) ↦ₛ bs.drop k) ∗ R) by
      simp only [sepConj_left_comm]]
    exact h
  exact readBytes_pointsToBytes_take (by simp; omega) h'

private theorem read64_of_readBytes_toLEBytes_8 {m : Memory} {a : BitVec 64} {w : BitVec 64}
    (h : m.readBytes a 8 = toLEBytes 8 w) :
    m.read64 a = w := by
  have h8 : m.readBytes a 8 =
      [m.read8 a, m.read8 (a + 1#64), m.read8 (a + 2#64), m.read8 (a + 3#64),
       m.read8 (a + 4#64), m.read8 (a + 5#64), m.read8 (a + 6#64), m.read8 (a + 7#64)] := by
    simp only [Memory.readBytes, BitVec.add_assoc]; rfl
  have hle : toLEBytes 8 w =
      [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8,
       w.extractLsb' 32 8, w.extractLsb' 40 8, w.extractLsb' 48 8, w.extractLsb' 56 8] := rfl
  rw [h8, hle] at h
  simp only [List.cons.injEq, and_true] at h
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  dsimp only [Memory.read64]
  rw [BitVec.add_zero, h0, h1, h2, h3, h4, h5, h6, h7]
  bv_bits

private theorem readSha512State_of_pointsToBytes {m : Memory} {a : BitVec 64}
    {st : Sha512State} {R : SepProp} (h : m ⊨ (a ↦ₛ sha512StateBytesLE st) ∗ R) :
    readSha512State m a = st := by
  apply List.Vector.ext
  intro i
  simp only [readSha512State, List.Vector.get_ofFn]
  apply read64_of_readBytes_toLEBytes_8
  rw [readBytes_pointsToBytes_slice (8 * i.val) 8 (by rw [sha512StateBytesLE_length]; omega) h]
  fin_cases i <;> (rw [sha512StateBytesLE, sha512State_toList_eq]; rfl)

private theorem compress512Hook_master_ok :
    HookOk (keepFsTrace (compress512Hook sha512CompressState)) masterCompress512Spec := by
  rw [keepFsTrace_compress512Hook_eq]
  change HookOk
    (retHook (fun s =>
      let st := readSha512State s.mem (s.readReg64 .x0)
      let bs := s.mem.readBytes (s.readReg64 .x1) (128 * (s.readReg64 .x2).toNat)
      s.setMem (s.mem.writeBytes (s.readReg64 .x0)
        (sha512StateBytesLE ((chunks128 bs).foldl sha512CompressState st)))))
    masterCompress512Spec
  refine retHook_ok fun ⟨stA, st, blkA, bs, n⟩ R s0 hrun hpre _ => ?_
  dsimp only [masterCompress512Spec, compress512StackedMasterSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hbs_len⟩, hmem⟩
  have hst : readSha512State s0.mem stA = st := readSha512State_of_pointsToBytes hmem
  have hmem_blk : s0.mem ⊨ (blkA ↦ₛ bs) ∗ ((stA ↦ₛ sha512StateBytesLE st) ∗
      stackAt s0.sp 256 ∗ R) := by
    ac_nf at hmem ⊢
  have hbs : s0.mem.readBytes blkA (128 * n) = bs := by
    rw [← hbs_len]
    exact ((IsBlock.pointsToBytes blkA bs).read hmem_blk).2
  let out := sha512StateBytesLE ((chunks128 bs).foldl sha512CompressState st)
  have hout_len : out.length = (sha512StateBytesLE st).length := by
    simp only [out, sha512StateBytesLE_length]
  have hmem_reg : s0.mem ⊨ memRegion stA out.length ∗
      ((blkA ↦ₛ bs) ∗ stackAt s0.sp 256 ∗ R) := by
    rw [hout_len]
    exact Satisfies.mono (sepConj_mono_left (pointsToBytes_entails_memRegion stA _)) hmem
  have hlen : out.length ≤ 2 ^ 64 := by simp only [out, sha512StateBytesLE_length]; decide
  refine ⟨?_, rfl, hrun, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · simp only [State.setMem, hx0, hx1, hx2, hst, hbs]
    exact keepsFrozen_writeBytes_of_memRegion out hlen hmem_reg
  · dsimp only [masterCompress512Spec]
    simp only [retHook, State.setPC, State.setMem, hx0, hx1, hx2, hst, hbs, sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    exact satisfies_writeBytes out hlen hmem_reg

private theorem compress512Hook_masterLs_ok [LibsignalPlacement] :
    HookOk (keepFsTrace (compress512Hook sha512CompressState))
      (withLsRet masterCompress512Spec) :=
  hookOk_withLsRet compress512Hook_master_ok

private theorem specStripSInvariant_masterCompress512 (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterCompress512Spec where
  pre_eq := fun _ s => by cases s; rfl
  post_eq := fun _ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

private theorem specStripSInvariant_masterCompress512Ls [LibsignalPlacement]
    (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (withLsRet masterCompress512Spec) :=
  specStripSInvariant_withLsRet (specStripSInvariant_masterCompress512 keep)

private theorem specPreservesFsTrace_masterCompress512 :
    SpecPreservesFsTrace masterCompress512Spec := by
  intro x R s0 sf hout
  rcases hout with ⟨_, _, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · dsimp only [masterCompress512Spec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    have hfs : sf.fs = s0.fs := hpost.1.1
    have htr : sf.trace = s0.trace := hpost.1.2.1
    exact ⟨hfs, FsTraced.of_eq htr (congrArg FsState.files hfs)⟩
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem specPreservesFsTrace_masterCompress512Ls [LibsignalPlacement] :
    SpecPreservesFsTrace (withLsRet masterCompress512Spec) :=
  specPreservesFsTrace_withLsRet specPreservesFsTrace_masterCompress512

private theorem masterCompress512_pre_setPC
    (x : BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat)
    (s : State) (pc : BitVec 64) :
    masterCompress512Spec.pre x (s.setPC pc) = masterCompress512Spec.pre x s := by
  cases s; rfl

private theorem masterCompress512_outcome_setPC
    (x : BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat)
    (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome masterCompress512Spec x R (s0.setPC pc) sf) :
    SubroutineOutcome masterCompress512Spec x R s0 sf := by
  rcases h with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨by cases s0; exact hret, by cases s0; exact hcc, ?_⟩
    have heq : masterCompress512Spec.post x (s0.setPC pc) sf =
        masterCompress512Spec.post x s0 sf := by
      cases s0; rfl
    rwa [heq] at hpost
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem masterCompress512Ls_pre_setPC [LibsignalPlacement]
    (x : BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat)
    (s : State) (pc : BitVec 64) :
    (withLsRet masterCompress512Spec).pre x (s.setPC pc) =
      (withLsRet masterCompress512Spec).pre x s :=
  withLsRet_pre_setPC masterCompress512_pre_setPC x s pc

private theorem masterCompress512Ls_outcome_setPC [LibsignalPlacement]
    (x : BitVec 64 × Sha512State × BitVec 64 × List (BitVec 8) × Nat)
    (R : SepProp) (s0 sf : State) (pc : BitVec 64)
    (h : SubroutineOutcome (withLsRet masterCompress512Spec) x R (s0.setPC pc) sf) :
    SubroutineOutcome (withLsRet masterCompress512Spec) x R s0 sf :=
  withLsRet_outcome_setPC masterCompress512_outcome_setPC x R s0 sf pc h

set_option maxRecDepth 400000 in
private theorem compress512StackedMaster_subroutine_ok {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) {hookStack : Nat} (hstack : 256 ≤ hookStack) :
    subroutine_ok (compress512SubProg pl) pl.base
      (withRoData (pl.ρ sha2K64Sym) sha512KBytes (compress512StackedMasterSpec hookStack)) := by
  have hm := compress512_master_ok hpl (P := compress512SubProg pl)
    (fun _ _ => compress512SubProg_externAt_none pl _) hstack
  rw [compress512_fnAddr pl] at hm
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hLP
  have hL0 : (compress512Lib.program pl).CodeLoaded s0.mem := by
    have hb : (compress512SubProg pl).base = (compress512Lib.program pl).base := rfl
    have hc : (compress512SubProg pl).code = (compress512Lib.program pl).code := rfl
    refine Program.CodeLoaded.intro (hb ▸ hLP.aligned) (hb ▸ hc ▸ hLP.no_wrap) fun i hi => ?_
    have hi' : i < (compress512SubProg pl).code.length := hc.symm ▸ hi
    have hget? : (compress512SubProg pl).code[i]? = (compress512Lib.program pl).code[i]? :=
      congrArg (fun l => l[i]?) hc
    rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at hget?
    rw [← hb, ← Option.some.inj hget?]
    exact ⟨hLP.byte_eq i hi', hLP.perm_eq i hi', hLP.isLazyFree_eq i hi'⟩
  have hpre_cl : s0.mem ⊨
      (withPlacedCodeLoaded compress512Lib pl
        (withRoData (pl.ρ sha2K64Sym) sha512KBytes
          (compress512StackedMasterSpec hookStack))).pre x s0 ∗ R := by
    dsimp only [withPlacedCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm _ ⌜_⌝, satisfies_pure_sepConj]
    exact ⟨hL0, hpre⟩
  exact hm.mono_outcome x R s0 hpc hrun hpre_cl hsp (fun _ h => h)

private theorem subroutine_ok_masterCompress512 {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) :
    subroutine_ok (compress512SubProg pl) pl.base
      (withRoData (pl.ρ sha2K64Sym) sha512KBytes masterCompress512Spec) := by
  have hst := compress512StackedMaster_subroutine_ok hpl (by decide : 256 ≤ 256)
  apply subroutine_ok.of_codeLoaded
  intro ⟨stA, st, blkA, bs, n⟩ R s0 hpc hrun hpre hsp _
  refine hst.mono_outcome (stA, st, blkA, bs, n) R s0 hpc hrun hpre hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withRoData, compress512StackedMasterSpec] at hpost
    dsimp only [withRoData, masterCompress512Spec]
    simp only [sepConj_assoc] at hpost ⊢
    rw [satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨⟨hpf, _⟩, hmem⟩ := hpost
    exact ⟨⟨hpf.1, hpf.2.1, hpf.2.2.1, hpf.2.2.2.1, hpf.2.2.2.2.1,
            hpf.2.2.2.2.2.1, hpf.2.2.2.2.2.2.1⟩, hmem⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

private theorem subroutine_ok_masterCompress512Ls [LibsignalPlacement] {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) :
    subroutine_ok (compress512SubProg pl) pl.base
      (withRoData (pl.ρ sha2K64Sym) sha512KBytes (withLsRet masterCompress512Spec)) :=
  subroutine_ok_withRoData_withLsRet (subroutine_ok_masterCompress512 hpl)

theorem compress512Ghost_masterLs_ok [LibsignalPlacement] {pl : Obj.Placement}
    (hpl : compress512Lib.Placeable pl) :
    HookOk (compress512Ghost pl) (withLsRet masterCompress512Spec) :=
  hookOk_linkedCallHookG_roTable
    emptyStdProg_svc
    (compress512SubProg_svc pl)
    (fun _ _ => rfl)
    (compress512SubProg_externAt_none pl)
    (subroutine_ok_masterCompress512Ls hpl)
    (specStripSInvariant_masterCompress512Ls (keepR_compress512 pl))
    specPreservesFsTrace_masterCompress512Ls
    masterCompress512Ls_pre_setPC
    masterCompress512Ls_outcome_setPC
    compress512Hook_masterLs_ok

/-! ## 3. State Preservation, `HookNoAllocFailed`, & `Compress512RowSpec` -/

theorem compress512Ghost_fs [LibsignalPlacement] (pl : Obj.Placement) (s : State) :
    (compress512Ghost pl s).fs = s.fs :=
  linkedCallHookG_fs _ _ _ _ _ _ _ s

theorem compress512Ghost_fsT [LibsignalPlacement] (pl : Obj.Placement) :
    HookFsTraced IsFsC (compress512Ghost pl) :=
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

theorem compress512Ghost_preserves_execFrozen [LibsignalPlacement]
    (pl : Obj.Placement) {u : State} (hfr : ExecFrozen u.mem) :
    ExecFrozen (compress512Ghost pl u).mem := by
  unfold compress512Ghost
  refine linkedCallHookG_preserves_execFrozen (fun s hs => ?_) hfr
  exact ExecFrozen.of_perm_eq hs (compress512Hook_vm sha512CompressState s).perm_eq

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

private theorem activeRealRun_compress512_vm_acp_trace [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress512Lib.Placeable pl)
    {s0 : State}
    (hG : roTableGuard (pl.ρ sha2K64Sym) sha512KBytes s0)
    (hAct : ActiveRealPre (withLsRet masterCompress512Spec) s0)
    (hReal : ActiveRealRun (keepR_compress512 pl) emptyStdProg (compress512SubProg pl) pl.base s0) :
    let sf := Classical.choose hReal.2.2.2
    VmPreserved s0 sf ∧ AllocCallPreserved s0 sf ∧ sf.trace = s0.trace := by
  obtain ⟨hrun, hsp, x, R, hpreLs⟩ := hAct
  dsimp only [withLsRet] at hpreLs
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpreLs
  obtain ⟨_, hpreM⟩ := hpreLs
  let s1 := s0.setPC pl.base
  let s1' := stripS (keepR_compress512 pl) s1
  have hG' : RoDataAt s1'.mem (pl.ρ sha2K64Sym) sha512KBytes :=
    roTableGuard_stripS (keepR_compress512 pl) pl.base (pl.ρ sha2K64Sym) sha512KBytes s0
      hReal.1 hG
  have hs1_pre : s1.mem ⊨ (compress512StackedMasterSpec 256).pre x s1 ∗ R := by
    have heq : (compress512StackedMasterSpec 256).pre x s1 = masterCompress512Spec.pre x s0 := by
      cases s0; rfl
    rwa [heq]
  have hs1'_std : s1'.mem ⊨ (compress512StackedMasterSpec 256).pre x s1' ∗ R := by
    have heq : (compress512StackedMasterSpec 256).pre x s1' =
        (compress512StackedMasterSpec 256).pre x s1 := by
      dsimp only [s1']; cases s1; rfl
    rw [heq]
    exact satisfies_stripExecOutside (keepR_compress512 pl) hs1_pre
  have hs1'_pre :
      s1'.mem ⊨ (withRoData (pl.ρ sha2K64Sym) sha512KBytes
        (compress512StackedMasterSpec 256)).pre x s1' ∗ R := by
    dsimp only [withRoData]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hG', hs1'_std⟩
  obtain ⟨sf', hsteps', hout'⟩ :=
    subroutine_ok_elim_steps_outcome
      (compress512StackedMaster_subroutine_ok hpl (by decide : 256 ≤ 256))
      x R s1' rfl hrun hs1'_pre hsp hReal.2.2.1
  rcases hout' with ⟨hret', _, hpost'⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · have hstop0' : SubroutineStop s0 sf' := Or.inl hret'
    have hnhalt' : sf'.status ≠ .Halted := by rw [hret'.2.2]; decide
    obtain ⟨sf, huntil, hstop_sf, hsf_eq, hfr_sf⟩ :=
      stepsUntil_of_stripS_standard (s0 := s0)
        emptyStdProg_svc (compress512SubProg_svc pl) (fun _ _ => rfl)
        (fun pc _ he => nomatch compress512SubProg_externAt_none pl pc ▸ he)
        hReal.2.1 hsteps' hstop0' hnhalt' s1 rfl hReal.1
    have hchoose := Classical.choose_spec hReal.2.2.2
    have hdet : Classical.choose hReal.2.2.2 = sf :=
      StepsUntil.deterministic hchoose.1 hchoose.2.1 huntil hstop_sf
    dsimp only
    rw [hdet]
    dsimp only [withRoData, compress512StackedMasterSpec] at hpost'
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
    have htr : sf.trace = s0.trace := by cases s0; cases sf; exact hpf'.2.1
    have hvm : VmPreserved s0 sf :=
      ⟨⟨hbrkS, hbrk, htp⟩, hphys, hperm, FdsHiFrame.of_fs_eq hfs⟩
    have hacp : AllocCallPreserved s0 sf := by
      cases s0; cases sf; exact hacp'
    exact ⟨hvm, hacp, htr⟩
  · exact False.elim (not_satisfies_false_sepConj hpan)
  · exact False.elim (not_satisfies_false_sepConj hex)
  · exact False.elim (not_satisfies_false_sepConj hoom)

theorem compress512Ghost_vmPreserved [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress512Lib.Placeable pl) (s0 : State) :
    VmPreserved s0 (compress512Ghost pl s0) := by
  classical
  unfold compress512Ghost linkedCallHookG
  by_cases hG : roTableGuard (pl.ρ sha2K64Sym) sha512KBytes s0
  · simp only [hG, ↓reduceDIte]
    unfold linkedCallHook
    by_cases hAct : ActiveRealPre (withLsRet masterCompress512Spec) s0
    · simp only [hAct, ↓reduceDIte]
      by_cases hReal : ActiveRealRun (keepR_compress512 pl) emptyStdProg (compress512SubProg pl) pl.base s0
      · simp only [hReal, ↓reduceDIte]
        exact (activeRealRun_compress512_vm_acp_trace hpl hG hAct hReal).1
      · simp only [hReal, ↓reduceDIte, keepFsTrace_compress512Hook_eq]
        exact compress512Hook_vm sha512CompressState s0
    · simp only [hAct, ↓reduceDIte]
      exact VmPreserved.refl s0
  · simp only [hG, ↓reduceDIte]
    by_cases hAct : ActiveRealPre (withLsRet masterCompress512Spec) s0
    · simp only [hAct, ↓reduceDIte, keepFsTrace_compress512Hook_eq]
      exact compress512Hook_vm sha512CompressState s0
    · simp only [hAct, ↓reduceDIte]
      exact VmPreserved.refl s0

theorem compress512Ghost_allocCallPreserved [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress512Lib.Placeable pl) (s0 : State) :
    AllocCallPreserved s0 (compress512Ghost pl s0) := by
  classical
  unfold compress512Ghost linkedCallHookG
  by_cases hG : roTableGuard (pl.ρ sha2K64Sym) sha512KBytes s0
  · simp only [hG, ↓reduceDIte]
    unfold linkedCallHook
    by_cases hAct : ActiveRealPre (withLsRet masterCompress512Spec) s0
    · simp only [hAct, ↓reduceDIte]
      by_cases hReal : ActiveRealRun (keepR_compress512 pl) emptyStdProg (compress512SubProg pl) pl.base s0
      · simp only [hReal, ↓reduceDIte]
        exact (activeRealRun_compress512_vm_acp_trace hpl hG hAct hReal).2.1
      · simp only [hReal, ↓reduceDIte, keepFsTrace_compress512Hook_eq]
        exact compress512Hook_acp sha512CompressState s0
    · simp only [hAct, ↓reduceDIte]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [hG, ↓reduceDIte]
    by_cases hAct : ActiveRealPre (withLsRet masterCompress512Spec) s0
    · simp only [hAct, ↓reduceDIte, keepFsTrace_compress512Hook_eq]
      exact compress512Hook_acp sha512CompressState s0
    · simp only [hAct, ↓reduceDIte]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem compress512Ghost_trace [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress512Lib.Placeable pl) (s0 : State) :
    (compress512Ghost pl s0).trace = s0.trace := by
  classical
  unfold compress512Ghost linkedCallHookG
  by_cases hG : roTableGuard (pl.ρ sha2K64Sym) sha512KBytes s0
  · simp only [hG, ↓reduceDIte]
    unfold linkedCallHook
    by_cases hAct : ActiveRealPre (withLsRet masterCompress512Spec) s0
    · simp only [hAct, ↓reduceDIte]
      by_cases hReal : ActiveRealRun (keepR_compress512 pl) emptyStdProg (compress512SubProg pl) pl.base s0
      · simp only [hReal, ↓reduceDIte]
        exact (activeRealRun_compress512_vm_acp_trace hpl hG hAct hReal).2.2
      · simp only [hReal, ↓reduceDIte, keepFsTrace_compress512Hook_eq]
        unfold compress512Hook returnToLinkRegister; rfl
    · simp only [hAct, ↓reduceDIte]
  · simp only [hG, ↓reduceDIte]
    by_cases hAct : ActiveRealPre (withLsRet masterCompress512Spec) s0
    · simp only [hAct, ↓reduceDIte, keepFsTrace_compress512Hook_eq]
      unfold compress512Hook returnToLinkRegister; rfl
    · simp only [hAct, ↓reduceDIte]

theorem compress512Ghost_noAllocFailed [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress512Lib.Placeable pl) :
    HookNoAllocFailed (compress512Ghost pl) :=
  hookNoAllocFailed_of_trace_eq _ (compress512Ghost_trace hpl)

theorem compress512Ghost_stackedMaster_ok [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress512Lib.Placeable pl)
    (stk : Nat) (hstk : 256 ≤ stk) :
    HookOk (compress512Ghost pl)
      (withLsRet (compress512StackedMasterSpec stk)) := by
  have hm := compress512Ghost_masterLs_ok hpl
  intro ⟨stA, st, blkA, bs, n⟩ R s0 hrun hpre hsp
  dsimp only [withLsRet, compress512StackedMasterSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨hlr, hpre'⟩ := hpre
  rw [satisfies_pure_sepConj] at hpre'
  obtain ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩ := hpre'
  have hstk_le : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ (stA ↦ₛ sha512StateBytesLE st) ∗
        (stackAt s0.sp stk ∗ ((blkA ↦ₛ bs) ∗ R)) := by
      ac_nf at hmem ⊢
    exact stackAt_le_two_pow_64 hm_stk
  rw [stackAt_split_frame256 s0 hstk hstk_le] at hmem
  let R₁ := stackAt (s0.sp - 256#64) (stk - 256) ∗ R
  have hpreM : s0.mem ⊨
      (withLsRet masterCompress512Spec).pre (stA, st, blkA, bs, n) s0 ∗ R₁ := by
    dsimp only [withLsRet, masterCompress512Spec, compress512StackedMasterSpec, R₁]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    refine ⟨hlr, ?_⟩
    rw [satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, hlen⟩, ?_⟩
    simpa only [sepConj_assoc] using hmem
  obtain ⟨hkf, hsym, hout⟩ := hm (stA, st, blkA, bs, n) R₁ s0 hrun hpreM hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRet, masterCompress512Spec, R₁] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hmsp, hmem_f⟩ := hpost
    dsimp only [withLsRet, compress512StackedMasterSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    have hvm := compress512Ghost_vmPreserved hpl s0
    have hacp := compress512Ghost_allocCallPreserved hpl s0
    have hpf : ProcessFieldsPreserved s0 (compress512Ghost pl s0) :=
      ⟨hmsp.1, hmsp.2.1, hmsp.2.2.1, hmsp.2.2.2.1, hmsp.2.2.2.2.1,
       hmsp.2.2.2.2.2.1, hmsp.2.2.2.2.2.2, hvm.perm_eq⟩
    refine ⟨⟨hpf, hacp⟩, ?_⟩
    rw [stackAt_split_frame256 s0 hstk hstk_le]
    simpa only [sepConj_assoc] using hmem_f
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

theorem compress512Ghost_compress512RowSpec [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress512Lib.Placeable pl) :
    Compress512RowSpec (compress512Ghost pl) :=
  Compress512RowSpec.of_ls_vm
    (compress512Ghost_stackedMaster_ok hpl)
    (compress512Ghost_vmPreserved hpl)
    (compress512Ghost_fs pl)

/-- Pure fallback `compress512Hook sha512CompressState` also satisfies `Compress512RowSpec`. -/
theorem compress512Fallback_compress512RowSpec [LibsignalPlacement] :
    Compress512RowSpec (compress512Hook sha512CompressState) := by
  refine Compress512RowSpec.of_vm
    (fun stk hstk => ?_)
    (compress512Hook_vm sha512CompressState)
    (fun _ => rfl)
  have hm := compress512Hook_master_ok
  rw [keepFsTrace_compress512Hook_eq] at hm
  intro ⟨stA, st, blkA, bs, n⟩ R s0 hrun hpre hsp
  dsimp only [compress512StackedMasterSpec] at hpre
  simp only [sepConj_assoc] at hpre
  rw [satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩ := hpre
  have hstk_le : stk ≤ 2 ^ 64 := by
    have hm_stk : s0.mem ⊨ (stA ↦ₛ sha512StateBytesLE st) ∗
        (stackAt s0.sp stk ∗ ((blkA ↦ₛ bs) ∗ R)) := by
      ac_nf at hmem ⊢
    exact stackAt_le_two_pow_64 hm_stk
  rw [stackAt_split_frame256 s0 hstk hstk_le] at hmem
  let R₁ := stackAt (s0.sp - 256#64) (stk - 256) ∗ R
  have hpreM : s0.mem ⊨ masterCompress512Spec.pre (stA, st, blkA, bs, n) s0 ∗ R₁ := by
    dsimp only [masterCompress512Spec, compress512StackedMasterSpec, R₁]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen⟩, by simpa only [sepConj_assoc] using hmem⟩
  obtain ⟨hkf, hsym, hout⟩ := hm (stA, st, blkA, bs, n) R₁ s0 hrun hpreM hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [masterCompress512Spec, R₁] at hpost
    simp only [sepConj_assoc] at hpost
    rw [satisfies_pure_sepConj] at hpost
    obtain ⟨hmsp, hmem_f⟩ := hpost
    dsimp only [compress512StackedMasterSpec]
    simp only [sepConj_assoc]
    rw [satisfies_pure_sepConj]
    have hvm := compress512Hook_vm sha512CompressState s0
    have hacp := compress512Hook_acp sha512CompressState s0
    have hpf : ProcessFieldsPreserved s0 (compress512Hook sha512CompressState s0) :=
      ⟨hmsp.1, hmsp.2.1, hmsp.2.2.1, hmsp.2.2.2.1, hmsp.2.2.2.2.1,
       hmsp.2.2.2.2.2.1, hmsp.2.2.2.2.2.2, hvm.perm_eq⟩
    refine ⟨⟨hpf, hacp⟩, ?_⟩
    rw [stackAt_split_frame256 s0 hstk hstk_le]
    simpa only [sepConj_assoc] using hmem_f
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-! ## 4. `GhostRowSpecOk`, `GhostRowReplayOn`, & `GhostRowOk` -/

theorem compress512Ghost_rowSpecOk [LibsignalPlacement]
    {pl : Obj.Placement} (hpl : compress512Lib.Placeable pl)
    (hArm : Compress512RowSpec (compress512Ghost pl) →
      ExtraRowSpec compress512Sym (compress512Ghost pl)) :
    GhostRowSpecOk compress512Sym (compress512Ghost pl) where
  fs_eq := compress512Ghost_fs pl
  fsT := compress512Ghost_fsT pl
  rowSpec := hArm (compress512Ghost_compress512RowSpec hpl)

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

/-- Behind-stub (`StubReachesTargetOn`) `GhostRowReplayOn` for `compress512Sym`
    (`lsCompress512SymCli`). -/
theorem compress512Ghost_rowReplayOn_of_stub [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (pl : Obj.Placement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : compress512Lib.Placeable pl)
    (hCL : ∀ u : State, InvS u → (compress512SubProg pl).CodeLoaded u.mem)
    (hRo : ∀ u : State, InvS u → RoDataAt u.mem (pl.ρ sha2K64Sym) sha512KBytes)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_compress512 pl lr = false)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_compress512 pl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none)
    (hRealStubNone : ∀ W : CliHooks,
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt?
        (libsignalSessionLib.resolve mpl compress512Sym) = none)
    (hStub : ∀ W : CliHooks,
      StubReachesTargetOn
        (fun m => (compress512SubProg pl).CodeLoaded m ∧
          RoDataAt m (pl.ρ sha2K64Sym) sha512KBytes)
        (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (libsignalSessionLib.resolve mpl compress512Sym)
        pl.base) :
    GhostRowReplayOn mpl mmpl InvS EG compress512Sym (fun _ => True)
      (compress512Ghost pl) where
  preserves_execFrozen := fun u _ _ hfr =>
    ⟨compress512Ghost_preserves_execFrozen pl hfr,
     compress512Ghost_fs pl u⟩
  replay_at_stub := by
    intro W _ _ _ _ _ _ _ _ _
    right
    have hRep :=
      ghostExternReplaysOn_of_linkedCallHookG_roTable_liftVis
        (InvMem := fun m => (compress512SubProg pl).CodeLoaded m ∧
          RoDataAt m (pl.ρ sha2K64Sym) sha512KBytes)
        (keep := keepR_compress512 pl)
        (P_run := emptyStdProg)
        (P_real := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
        (P_sub := compress512SubProg pl)
        (stubPc := libsignalSessionLib.resolve mpl compress512Sym)
        (entryTarget := pl.base)
        (tbl := pl.ρ sha2K64Sym)
        (bytes := sha512KBytes)
        (fallback := compress512Hook sha512CompressState)
        emptyStdProg_svc
        (compress512SubProg_svc pl)
        (fun pc _ => emptyStdProg_externAt pc)
        (compress512SubProg_externAt_none pl)
        (hRealStubNone W)
        (hStub W)
        (fun _ _ _ _ _ hvis =>
          h2fsgen_steps_lift_of_visitedIn_noExtern
            (D := keepR_compress512 pl)
            (P1 := emptyStdProg)
            (P2 := cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W)
            (emptyStdProg_svc.trans (realProg617_svc mpl mmpl W).symm)
            (fun pc _ => emptyStdProg_externAt pc)
            (fun _ hk => hRealHullNoExt W hk)
            hvis)
        (fun _ _ hInvM => compress512SubProg_codeLoaded_stripExecOutside hpl hInvM.1)
        (fun _ _ hInvM hkf =>
          ⟨hInvM.1.of_keepsFrozen hkf, roDataAt_of_keepsFrozen hInvM.2 hkf⟩)
        (fun _ _ hInvM => hInvM.2)
        (subroutine_ok_masterCompress512Ls hpl)
        (specStripSInvariant_masterCompress512Ls (keepR_compress512 pl))
        specPreservesFsTrace_masterCompress512Ls
        masterCompress512Ls_pre_setPC
        masterCompress512Ls_outcome_setPC
    refine ⟨hRep.1, ?_⟩
    intro u _ _ hpc hrun hnoex hkf hfr hInvU
    have hlr : keepR_compress512 pl (u.readReg64 .lr) = false :=
      keepLr_false_of_noException_via_activeRealPre
        hKeep linkedCallHookG_activeRealPre_of_noException hnoex
    obtain ⟨hSteps1, hfr1, _⟩ :=
      hRep.2 u hpc hrun hnoex hfr hlr ⟨hCL u hInvU, hRo u hInvU⟩
    exact ⟨hSteps1, hfr1,
      hInvKeep u (compress512Ghost pl u) hInvU hkf (compress512Ghost_fs pl u)⟩

/-- Direct `.text.lib2` `GhostRowReplayOn` for `compress512Sym` (`entryGuard := fun _ => True`). -/
theorem compress512Ghost_rowReplayOn [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (pl : Obj.Placement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : compress512Lib.Placeable pl)
    (hTargetEq : libsignalSessionLib.resolve mpl compress512Sym = pl.base)
    (hCL : ∀ u : State, InvS u → (compress512SubProg pl).CodeLoaded u.mem)
    (hRo : ∀ u : State, InvS u → RoDataAt u.mem (pl.ρ sha2K64Sym) sha512KBytes)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_compress512 pl lr = false)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_compress512 pl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowReplayOn mpl mmpl InvS EG compress512Sym (fun _ => True)
      (compress512Ghost pl) :=
  compress512Ghost_rowReplayOn_of_stub mpl mmpl pl InvS EG hpl hCL hRo hInvKeep hKeep
    hRealHullNoExt
    (fun W => by rw [hTargetEq]; exact hRealHullNoExt W (keepR_compress512_entry pl))
    (fun _ u hpc _ _ _ => by
      rw [setPC_eq_self_of_pc_eq (hpc.trans hTargetEq)]
      exact Steps.refl _)

/-- Full per-row `GhostRowOk` bundle (`GhostRowSpecOk` ∧ `GhostRowReplayOn`) for
    `compress512Sym` (`entryGuard := fun _ => True`). -/
theorem compress512Ghost_rowOk [LibsignalPlacement]
    (mpl mmpl : Obj.MultiPlacement) (pl : Obj.Placement)
    (InvS : State → Prop)
    (EG : CliHooks → String → Option (State → State))
    (hpl : compress512Lib.Placeable pl)
    (hArm : Compress512RowSpec (compress512Ghost pl) →
      ExtraRowSpec compress512Sym (compress512Ghost pl))
    (hTargetEq : libsignalSessionLib.resolve mpl compress512Sym = pl.base)
    (hCL : ∀ u : State, InvS u → (compress512SubProg pl).CodeLoaded u.mem)
    (hRo : ∀ u : State, InvS u → RoDataAt u.mem (pl.ρ sha2K64Sym) sha512KBytes)
    (hInvKeep : ∀ u v : State, InvS u → u.mem.KeepsFrozen v.mem → v.fs = u.fs → InvS v)
    (hKeep : ∀ lr : BitVec 64, LsRetAddr624 lr → keepR_compress512 pl lr = false)
    (hRealHullNoExt : ∀ (W : CliHooks) {pc : BitVec 64},
      keepR_compress512 pl pc = true →
      (cliProgExtPlacedAt mpl (cliExternsPlaced mmpl) 617 W).externAt? pc = none) :
    GhostRowOk mpl mmpl InvS EG compress512Sym (fun _ => True)
      (compress512Ghost pl) :=
  ⟨compress512Ghost_rowSpecOk hpl hArm,
   compress512Ghost_rowReplayOn mpl mmpl pl InvS EG hpl hTargetEq hCL hRo hInvKeep hKeep
     hRealHullNoExt⟩

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.Compress512GhostReplays
