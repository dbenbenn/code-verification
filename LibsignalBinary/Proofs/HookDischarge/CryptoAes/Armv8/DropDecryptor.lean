/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import ProofLib.StdStartup.MemOps
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
meta import ProofLib.StdStartup.StdDetect
import Arm64.Trusted.ISA.Eval
import Arm64.Trusted.ISA.Semantics
import ProofLib.Abi.Aapcs
import ProofLib.BV.Bits
import ProofLib.Hoare.Hooks
import ProofLib.Hoare.Model
import ProofLib.SepLogic.Bytes
import ProofLib.SepLogic.Model
import ProofLib.SepLogic.Region
import ProofLib.SepLogic.WP

/-!
# `drop_glue::<cbc::decrypt::Decryptor<aes::autodetect::Aes256>>` Machine-Code Proof (`55` Insns)

Placement-generic (`G1` `p = 4096` invariant) verification of the 55-instruction `Decryptor<Aes256>`
drop glue: zeroes the 16-byte IV `[+0x3c0 .. +0x3d0)` unconditionally, then zeroes `[+0x000 .. +0x1e0)`
(`storageVal == 1#8`, ARMv8 AES) or `[+0x000 .. +0x3c0)` (`storageVal != 1#8`, `fixslice64`).
-/

set_option autoImplicit false

namespace LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.DropDecryptor

open Arm64 ProofLib
open ProofLib.StdStartup (decodeWord decodeWords hasInstrs adrpOff pageLo12)
open LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
  (PureStepPreserved pureStepProj step_str64_perm)
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon
open scoped LibsignalBinary.Proofs.HookDischarge.CryptoAes.Fixslice64.CodeCommon.Simp

public section

/-! ## 1. Placement-Generic Instruction & Word Definitions (`55` Instructions) -/

@[expose] def dropHeadWords : List (BitVec 32) := [0xd10043ff#32, 0x390f001f#32, 0x910f0009#32]

@[expose] def dropIvWordsA : List (BitVec 32) :=
  [0x390f041f#32, 0x910f0409#32, 0x390f081f#32, 0x910f0809#32, 0x390f0c1f#32, 0x910f0c09#32,
   0x390f101f#32, 0x910f1009#32, 0x390f141f#32, 0x910f1409#32, 0x390f181f#32, 0x910f1809#32,
   0x390f1c1f#32, 0x910f1c09#32]

@[expose] def dropIvWordsB : List (BitVec 32) :=
  [0x390f201f#32, 0x910f2009#32, 0x390f241f#32, 0x910f2409#32, 0x390f281f#32, 0x910f2809#32,
   0x390f2c1f#32, 0x910f2c09#32, 0x390f301f#32, 0x910f3009#32, 0x390f341f#32, 0x910f3409#32,
   0x390f381f#32, 0x910f3809#32, 0x390f3c1f#32, 0x910f3c09#32]

@[expose] def dropBranchWords : List (BitVec 32) := [0x7100051f#32, 0x54000161#32]
@[expose] def dropHwSetupWords : List (BitVec 32) := [0xaa1f03e8#32, 0xf90007e0#32]
@[expose] def dropHwLoopWords : List (BitVec 32) :=
  [0xaa0803e9#32, 0x91000508#32, 0xf107811f#32, 0x3829681f#32, 0x54ffff81#32]
@[expose] def dropHwEpilogueWords : List (BitVec 32) := [0x910023e8#32, 0x910043ff#32, 0xd65f03c0#32]
@[expose] def dropSwSetupWords : List (BitVec 32) := [0x52807808#32, 0xaa0003e9#32]
@[expose] def dropSwLoopWords : List (BitVec 32) :=
  [0xf800853f#32, 0xf1002108#32, 0xaa0903e0#32, 0x54ffffa1#32]
@[expose] def dropSwEpilogueWords : List (BitVec 32) := [0x910043ff#32, 0xd65f03c0#32]

/-- Placement-generic 55-instruction list for `drop_glue<Decryptor<autodetect::Aes256>>` at
    `fnAddr` reading the `cpufeatures` flag byte at `storageAddr`. -/
@[expose] def dropDecryptorInstrs (fnAddr storageAddr : BitVec 64) : List Instr :=
  List.flatten
    [ decodeWords dropHeadWords,
      [.adr true (.gpr 8#5) (adrpOff (fnAddr + 0x0c#64) storageAddr)],
      decodeWords dropIvWordsA, decodeWords dropIvWordsB,
      [.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 8#5) (pageLo12 storageAddr))],
      decodeWords dropBranchWords, decodeWords dropHwSetupWords, decodeWords dropHwLoopWords,
      decodeWords dropHwEpilogueWords, decodeWords dropSwSetupWords, decodeWords dropSwLoopWords,
      decodeWords dropSwEpilogueWords ]

/-- Raw 55-word list parameterized by the relocated `adrp` (`+0x0c`) and `ldrb` (`+0x88`) words. -/
@[expose] def dropDecryptorWords (adrpWord ldrbWord : BitVec 32) : List (BitVec 32) :=
  dropHeadWords ++ [adrpWord] ++ dropIvWordsA ++ dropIvWordsB ++ [ldrbWord] ++
  dropBranchWords ++ dropHwSetupWords ++ dropHwLoopWords ++ dropHwEpilogueWords ++
  dropSwSetupWords ++ dropSwLoopWords ++ dropSwEpilogueWords

theorem dropDecryptorInstrs_length (fnAddr storageAddr : BitVec 64) :
    (dropDecryptorInstrs fnAddr storageAddr).length = 55 := by
  have hd : ∀ ws : List (BitVec 32), (decodeWords ws).length = ws.length := fun _ => List.length_map _
  simp only [dropDecryptorInstrs, List.length_flatten, List.map_cons, List.map_nil, hd,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]; rfl

theorem decodeWords_dropDecryptorWords {fnAddr storageAddr : BitVec 64} {adrpWord ldrbWord : BitVec 32}
    (hadrp : decodeWord adrpWord = .adr true (.gpr 8#5) (adrpOff (fnAddr + 0x0c#64) storageAddr))
    (hldrb : decodeWord ldrbWord = .ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 8#5) (pageLo12 storageAddr))) :
    decodeWords (dropDecryptorWords adrpWord ldrbWord) = dropDecryptorInstrs fnAddr storageAddr := by
  simp [dropDecryptorWords, dropDecryptorInstrs, decodeWords, List.map_append, hadrp, hldrb]

/-! ## 2. Subroutine Specifications -/

/-- Exact postcondition footprint of `Decryptor<Aes256>` after `drop_glue`:
    - `[0x000 .. 0x1e0)` (`480` B) zeroed if `storageVal == 1#8`, or `[0x000 .. 0x3c0)` (`960` B)
      zeroed if `storageVal != 1#8`;
    - `[0x3c0 .. 0x3d0)` (`16` B IV) zeroed unconditionally. -/
@[expose] def dropDecryptorPostSpatial (decryptorPtr : BitVec 64) (storageVal : BitVec 8) : SepProp :=
  (if storageVal == 1#8 then
    (decryptorPtr ↦ₛ List.replicate 0x1e0 0#8) ∗ memRegion (decryptorPtr + 0x1e0#64) 0x1e0
   else
    (decryptorPtr ↦ₛ List.replicate 0x3c0 0#8)) ∗
  ((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 0x10 0#8)

/-- Strong `subroutine_ok` specification recording exact zeroed slices of `Decryptor<Aes256>`. -/
@[expose] def dropDecryptorZeroSpec (storageAddr : BitVec 64) : Spec (BitVec 64 × BitVec 8) where
  pre := fun (decryptorPtr, storageVal) s0 =>
    ⌜s0.readReg64 .x0 = decryptorPtr⌝ ∗
    (memRegion decryptorPtr 0x3d0 ∗ (storageAddr ↦₈ storageVal) ∗ stackFrameAt s0.sp 0x10)
  post := fun (decryptorPtr, storageVal) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗
    (dropDecryptorPostSpatial decryptorPtr storageVal ∗
      (storageAddr ↦₈ storageVal) ∗ stackFrameAt s0.sp 0x10)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

/-- Region-preserving `subroutine_ok` specification on `memRegion decryptorPtr 0x3d0`. -/
@[expose] def dropDecryptorSpec (storageAddr : BitVec 64) : Spec (BitVec 64 × BitVec 8) where
  pre := fun (decryptorPtr, storageVal) s0 =>
    ⌜s0.readReg64 .x0 = decryptorPtr⌝ ∗
    (memRegion decryptorPtr 0x3d0 ∗ (storageAddr ↦₈ storageVal) ∗ stackFrameAt s0.sp 0x10)
  post := fun (decryptorPtr, storageVal) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗
    (memRegion decryptorPtr 0x3d0 ∗ (storageAddr ↦₈ storageVal) ∗ stackFrameAt s0.sp 0x10)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

/-- Byte-slice `subroutine_ok` specification transforming `(decryptorPtr ↦ₛ bs)` (`bs.length = 0x3d0`)
    to `∃∗ bs', ⌜bs'.length = 0x3d0⌝ ∗ (decryptorPtr ↦ₛ bs')`. -/
@[expose] def dropDecryptorBytesSpec (storageAddr : BitVec 64) :
    Spec (BitVec 64 × BitVec 8 × List (BitVec 8)) where
  pre := fun (decryptorPtr, storageVal, bs) s0 =>
    ⌜s0.readReg64 .x0 = decryptorPtr ∧ bs.length = 0x3d0⌝ ∗
    ((decryptorPtr ↦ₛ bs) ∗ (storageAddr ↦₈ storageVal) ∗ stackFrameAt s0.sp 0x10)
  post := fun (decryptorPtr, storageVal, _) s0 sf =>
    ⌜PureStepPreserved s0 sf⌝ ∗
    ((∃∗ bs' : List (BitVec 8), ⌜bs'.length = 0x3d0⌝ ∗ (decryptorPtr ↦ₛ bs')) ∗
      (storageAddr ↦₈ storageVal) ∗ stackFrameAt s0.sp 0x10)
  onPanic := fun _ _ _ => ⌜False⌝; onExit := fun _ _ _ _ => ⌜False⌝; onOom := fun _ _ _ => ⌜False⌝

/-! ## 3. Separation-Logic & Code-Segment Helpers -/

theorem dropDecryptorPostSpatial_entails_memRegion (decryptorPtr : BitVec 64) (storageVal : BitVec 8) :
    dropDecryptorPostSpatial decryptorPtr storageVal ⊢ memRegion decryptorPtr 0x3d0 := by
  unfold dropDecryptorPostSpatial
  have h16 : ((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 0x10 0#8) ⊢ memRegion (decryptorPtr + 0x3c0#64) 0x10 := by
    simpa only [List.length_replicate] using pointsToBytes_entails_memRegion (decryptorPtr + 0x3c0#64) (List.replicate 0x10 0#8)
  by_cases h : storageVal == 1#8
  · simp only [h, ↓reduceIte]
    have h480 : (decryptorPtr ↦ₛ List.replicate 0x1e0 0#8) ⊢ memRegion decryptorPtr 0x1e0 := by
      simpa only [List.length_replicate] using pointsToBytes_entails_memRegion decryptorPtr (List.replicate 0x1e0 0#8)
    have h960 : memRegion decryptorPtr 0x1e0 ∗ memRegion (decryptorPtr + 0x1e0#64) 0x1e0 = memRegion decryptorPtr 0x3c0 :=
      (memRegion_split decryptorPtr 0x1e0 0x1e0 (by decide)).symm
    have h976 : memRegion decryptorPtr 0x3c0 ∗ memRegion (decryptorPtr + 0x3c0#64) 0x10 = memRegion decryptorPtr 0x3d0 :=
      (memRegion_split decryptorPtr 0x3c0 0x10 (by decide)).symm
    refine Entails.trans (sepConj_mono (sepConj_mono_left h480) h16) ?_
    rw [h960, h976]; exact Entails.refl _
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    have h960 : (decryptorPtr ↦ₛ List.replicate 0x3c0 0#8) ⊢ memRegion decryptorPtr 0x3c0 := by
      simpa only [List.length_replicate] using pointsToBytes_entails_memRegion decryptorPtr (List.replicate 0x3c0 0#8)
    have h976 : memRegion decryptorPtr 0x3c0 ∗ memRegion (decryptorPtr + 0x3c0#64) 0x10 = memRegion decryptorPtr 0x3d0 :=
      (memRegion_split decryptorPtr 0x3c0 0x10 (by decide)).symm
    refine Entails.trans (sepConj_mono h960 h16) ?_
    rw [h976]; exact Entails.refl _

private def bytes8At (p w : BitVec 64) : SepProp :=
  (p ↦₈ w.extractLsb' 0 8) ∗ ((p + 1#64) ↦₈ w.extractLsb' 8 8) ∗
  ((p + 2#64) ↦₈ w.extractLsb' 16 8) ∗ ((p + 3#64) ↦₈ w.extractLsb' 24 8) ∗
  ((p + 4#64) ↦₈ w.extractLsb' 32 8) ∗ ((p + 5#64) ↦₈ w.extractLsb' 40 8) ∗
  ((p + 6#64) ↦₈ w.extractLsb' 48 8) ∗ ((p + 7#64) ↦₈ w.extractLsb' 56 8)

private theorem memRegion8_entails_bytes8At (p : BitVec 64) :
    memRegion p 8 ⊢ ∃∗ w : BitVec 64, bytes8At p w := by
  rw [memRegion_eight p]
  refine Entails.sepExists_elim fun w => Entails.sepExists_right w ?_
  rw [pointsTo64_eq_pointsToBytes]; dsimp only [unpack64, bytes8At]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq_explicit (by sep_ac_rfl)

private theorem zero8_fold (p : BitVec 64) :
    (p ↦₈ 0#8) ∗ ((p + 1#64) ↦₈ 0#8) ∗ ((p + 2#64) ↦₈ 0#8) ∗ ((p + 3#64) ↦₈ 0#8) ∗
    ((p + 4#64) ↦₈ 0#8) ∗ ((p + 5#64) ↦₈ 0#8) ∗ ((p + 6#64) ↦₈ 0#8) ∗ ((p + 7#64) ↦₈ 0#8) =
    (p ↦ₛ List.replicate 8 0#8) := by
  rw [show List.replicate 8 (0#8) = [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] from rfl]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

private theorem stackFrameAt_16_unpack (sp : BitVec 64) :
    stackFrameAt sp 0x10 ⊢ ∃∗ w : BitVec 64 × BitVec 64, ((sp - 16#64) ↦₆₄ w.1) ∗ ((sp - 8#64) ↦₆₄ w.2) := by
  rw [stackFrameAt_eq_memRegion sp 16 (by decide), show sp - BitVec.ofNat 64 16 = sp - 16#64 from rfl,
      show (16 : Nat) = 8 + 8 from rfl, memRegion_split (sp - 16#64) 8 8 (by decide),
      show sp - 16#64 + BitVec.ofNat 64 8 = sp - 8#64 by bv_omega,
      memRegion_eight (sp - 16#64), memRegion_eight (sp - 8#64), sepExists_sepConj_left]
  refine Entails.sepExists_elim fun w0 => ?_
  rw [sepExists_sepConj_right]
  exact Entails.sepExists_elim fun w1 => Entails.sepExists_right (w0, w1) (Entails.refl _)

private theorem stackFrameAt_16_pack (sp w0 w1 : BitVec 64) :
    ((sp - 16#64) ↦₆₄ w0) ∗ ((sp - 8#64) ↦₆₄ w1) ⊢ stackFrameAt sp 0x10 := by
  rw [stackFrameAt_eq_memRegion sp 16 (by decide), show (16 : Nat) = 8 + 8 from rfl,
      memRegion_split (sp - 16#64) 8 8 (by decide),
      show sp - 16#64 + BitVec.ofNat 64 8 = sp - 8#64 by bv_omega]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)

private theorem dropPre_unpack (decryptorPtr storageAddr : BitVec 64) (storageVal : BitVec 8) (sp : BitVec 64) :
    memRegion decryptorPtr 0x3d0 ∗ (storageAddr ↦₈ storageVal) ∗ stackFrameAt sp 0x10 ⊢
      ∃∗ ba : BitVec 64, ∃∗ bb : BitVec 64, ∃∗ stk : BitVec 64 × BitVec 64,
        bytes8At (decryptorPtr + 0x3c0#64) ba ∗ bytes8At (decryptorPtr + 0x3c8#64) bb ∗
        memRegion decryptorPtr 0x3c0 ∗ (storageAddr ↦₈ storageVal) ∗
        ((sp - 16#64) ↦₆₄ stk.1) ∗ ((sp - 8#64) ↦₆₄ stk.2) := by
  rw [show (0x3d0 : Nat) = 0x3c0 + 0x10 from rfl, memRegion_split decryptorPtr 0x3c0 0x10 (by decide),
      show decryptorPtr + BitVec.ofNat 64 0x3c0 = decryptorPtr + 0x3c0#64 from rfl,
      show (0x10 : Nat) = 8 + 8 from rfl, memRegion_split (decryptorPtr + 0x3c0#64) 8 8 (by decide),
      show decryptorPtr + 0x3c0#64 + BitVec.ofNat 64 8 = decryptorPtr + 0x3c8#64 by bv_omega]
  refine Entails.trans (sepConj_mono
    (sepConj_mono_right (sepConj_mono (memRegion8_entails_bytes8At _) (memRegion8_entails_bytes8At _)))
    (sepConj_mono_right (stackFrameAt_16_unpack sp))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun stk => Entails.sepExists_elim fun bb =>
    Entails.sepExists_elim fun ba => Entails.sepExists_right ba (Entails.sepExists_right bb
      (Entails.sepExists_right stk (Entails.of_eq_explicit (by sep_ac_rfl))))

private theorem pointsTo64_zero_eq_replicate (p : BitVec 64) :
    (p ↦₆₄ 0#64) = (p ↦ₛ List.replicate 8 0#8) := by
  rw [pointsTo64_eq_pointsToBytes, show unpack64 0#64 = List.replicate 8 0#8 by decide]

private theorem hasInstrs_split_next {P : Program} {fnAddr off1 : BitVec 64} (off2 : BitVec 64)
    {xs ys : List Instr} (h : hasInstrs P (fnAddr + off1) (xs ++ ys))
    (hoff : off1 + BitVec.ofNat 64 (4 * xs.length) = off2) :
    hasInstrs P (fnAddr + off1) xs ∧ hasInstrs P (fnAddr + off2) ys := by
  obtain ⟨h1, h2⟩ := h.split_append (off := BitVec.ofNat 64 (4 * xs.length)) rfl
  exact ⟨h1, (show fnAddr + off1 + BitVec.ofNat 64 (4 * xs.length) = fnAddr + off2 by
    rw [BitVec.add_assoc, hoff]) ▸ h2⟩

private structure DropCodeSegs (P : Program) (fnAddr storageAddr : BitVec 64) : Prop where
  head     : hasInstrs P fnAddr (decodeWords dropHeadWords)
  adrp     : P.fetch (fnAddr + 0x0c#64) = some (.adr true (.gpr 8#5) (adrpOff (fnAddr + 0x0c#64) storageAddr))
  ivA      : hasInstrs P (fnAddr + 0x10#64) (decodeWords dropIvWordsA)
  ivB      : hasInstrs P (fnAddr + 0x48#64) (decodeWords dropIvWordsB)
  ldrb     : P.fetch (fnAddr + 0x88#64) = some (.ldr .W32 .B8 false (.gpr 8#5) (.Offset (.gpr 8#5) (pageLo12 storageAddr)))
  branch   : hasInstrs P (fnAddr + 0x8c#64) (decodeWords dropBranchWords)
  hwSetup  : hasInstrs P (fnAddr + 0x94#64) (decodeWords dropHwSetupWords)
  hwLoop   : hasInstrs P (fnAddr + 0x9c#64) (decodeWords dropHwLoopWords)
  hwEpi    : hasInstrs P (fnAddr + 0xb0#64) (decodeWords dropHwEpilogueWords)
  swSetup  : hasInstrs P (fnAddr + 0xbc#64) (decodeWords dropSwSetupWords)
  swLoop   : hasInstrs P (fnAddr + 0xc4#64) (decodeWords dropSwLoopWords)
  swEpi    : hasInstrs P (fnAddr + 0xd4#64) (decodeWords dropSwEpilogueWords)

private theorem DropCodeSegs.of_hasInstrs {P : Program} {fnAddr storageAddr : BitVec 64}
    (hc : hasInstrs P fnAddr (dropDecryptorInstrs fnAddr storageAddr)) :
    DropCodeSegs P fnAddr storageAddr := by
  simp only [dropDecryptorInstrs, List.flatten_cons, List.flatten_nil, List.append_nil] at hc
  obtain ⟨s0, hc⟩ := hc.split_append (off := 0x0c#64) rfl
  obtain ⟨s1, hc⟩ := hasInstrs_split_next 0x10#64 hc rfl
  obtain ⟨s2, hc⟩ := hasInstrs_split_next 0x48#64 hc rfl
  obtain ⟨s3, hc⟩ := hasInstrs_split_next 0x88#64 hc rfl
  obtain ⟨s4, hc⟩ := hasInstrs_split_next 0x8c#64 hc rfl
  obtain ⟨s5, hc⟩ := hasInstrs_split_next 0x94#64 hc rfl
  obtain ⟨s6, hc⟩ := hasInstrs_split_next 0x9c#64 hc rfl
  obtain ⟨s7, hc⟩ := hasInstrs_split_next 0xb0#64 hc rfl
  obtain ⟨s8, hc⟩ := hasInstrs_split_next 0xbc#64 hc rfl
  obtain ⟨s9, hc⟩ := hasInstrs_split_next 0xc4#64 hc rfl
  obtain ⟨s10, s11⟩ := hasInstrs_split_next 0xd4#64 hc rfl
  exact ⟨s0, s1.fetch_at_zero, s2, s3, s4.fetch_at_zero, s5, s6, s7, s8, s9, s10, s11⟩

/-! ## 4. Invariant Anchor & Chunk / Loop Lemmas -/

private structure DropAnchor (s0 : State) (s : State) : Prop where
  sp   : s.sp = s0.sp - 16#64
  lr   : s.readReg64 .lr = s0.readReg64 .lr
  cs   : CalleeSavedPreserved s0 s
  pres : PureStepPreserved s0 s

private theorem sp_sub16_and_15 {s0 : State} (hsp : s0.spAligned = true) :
    (s0.sp - 16#64) &&& 15#64 = 0#64 :=
  beq_iff_eq.mp (s0.spAligned_sub_of_dvd 16 hsp)

private theorem DropAnchor.step {s0 s sf : State} (ha : DropAnchor s0 s)
    (hsp : sf.sp = s.sp := by first | rfl | simp [wp_norm, arm64_norm])
    (hlr : sf.readReg64 .lr = s.readReg64 .lr := by first | rfl | simp [wp_norm, arm64_norm])
    (hcs : CalleeSavedPreserved s sf := by first | exact CalleeSavedPreserved.rfl | simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])
    (hproj : pureStepProj sf = pureStepProj s := by first | rfl | simp [wp_norm, arm64_norm])
    (hperm : sf.mem.perm = s.mem.perm := by first | rfl | simp [wp_norm, arm64_norm]) :
    DropAnchor s0 sf :=
  ⟨hsp.trans ha.sp, hlr.trans ha.lr, CalleeSavedPreserved.trans ha.cs hcs,
   ha.pres.trans (PureStepPreserved.of_proj_perm hproj hperm)⟩

section
arm64_proof_prelude

private theorem step_iv_partA {P : Program} {fnAddr storageAddr decryptorPtr target_pc : BitVec 64}
    {b : BitVec 64} {s0 : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hhead : hasInstrs P fnAddr (decodeWords dropHeadWords))
    (hadrp : P.fetch (fnAddr + 0x0c#64) = some (.adr true (.gpr 8#5) (adrpOff (fnAddr + 0x0c#64) storageAddr)))
    (hivA : hasInstrs P (fnAddr + 0x10#64) (decodeWords dropIvWordsA))
    (hpc : s0.pc = fnAddr) (hrun : s0.status = .Running) (hx0 : s0.readReg64 .x0 = decryptorPtr)
    (hnext : ∀ s1 : State, s1.pc = fnAddr + 0x48#64 → s1.status = .Running →
      DropAnchor s0 s1 → s1.readReg64 .x0 = decryptorPtr →
      s1.readReg64 (.gpr 8#5) = (storageAddr &&& 0xfffffffffffff000#64) →
      SepWP P target_pc s1 (((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 8 0#8) ∗ F) post oom) :
    SepWP P target_pc s0 (bytes8At (decryptorPtr + 0x3c0#64) b ∗ F) post oom := by
  have_instrs hhead 0 3
  dsimp only [bytes8At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps 1; wp_str8 hf_1 m0 hm0; wp_steps 1; wp_step
  have_instrs hivA 0 14
  wp_str8 hf_0 m1 hm1; wp_steps 1; wp_str8 hf_2 m2 hm2; wp_steps 1
  wp_str8 hf_4 m3 hm3; wp_steps 1; wp_str8 hf_6 m4 hm4; wp_steps 1
  wp_str8 hf_8 m5 hm5; wp_steps 1; wp_str8 hf_10 m6 hm6; wp_steps 1
  wp_str8 hf_12 m7 hm7; wp_steps 1
  rw [show (((decryptorPtr + 0x3c0#64) ↦₈ 0#8) ∗ ((decryptorPtr + 0x3c1#64) ↦₈ 0#8) ∗
       ((decryptorPtr + 0x3c2#64) ↦₈ 0#8) ∗ ((decryptorPtr + 0x3c3#64) ↦₈ 0#8) ∗
       ((decryptorPtr + 0x3c4#64) ↦₈ 0#8) ∗ ((decryptorPtr + 0x3c5#64) ↦₈ 0#8) ∗
       ((decryptorPtr + 0x3c6#64) ↦₈ 0#8) ∗ ((decryptorPtr + 0x3c7#64) ↦₈ 0#8)) ∗ F =
      ((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 8 0#8) ∗ F by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using congrArg (· ∗ F) (zero8_fold (decryptorPtr + 0x3c0#64))]
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    ⟨by simp [wp_norm, arm64_norm], by simp [wp_norm, arm64_norm],
     by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm],
     PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm])
       (by simp [wp_norm, arm64_norm, hm7, hm6, hm5, hm4, hm3, hm2, hm1, hm0])⟩
    (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm])

private theorem step_iv_partB {P : Program} {fnAddr storageAddr decryptorPtr target_pc : BitVec 64}
    {b : BitVec 64} {s0 s : State} {F : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hivB : hasInstrs P (fnAddr + 0x48#64) (decodeWords dropIvWordsB))
    (hpc : s.pc = fnAddr + 0x48#64) (hrun : s.status = .Running) (ha : DropAnchor s0 s)
    (hx0 : s.readReg64 .x0 = decryptorPtr)
    (hx8 : s.readReg64 (.gpr 8#5) = (storageAddr &&& 0xfffffffffffff000#64))
    (hnext : ∀ sf : State, sf.pc = fnAddr + 0x88#64 → sf.status = .Running →
      DropAnchor s0 sf → sf.readReg64 .x0 = decryptorPtr →
      sf.readReg64 (.gpr 8#5) = (storageAddr &&& 0xfffffffffffff000#64) →
      SepWP P target_pc sf (((decryptorPtr + 0x3c8#64) ↦ₛ List.replicate 8 0#8) ∗ F) post oom) :
    SepWP P target_pc s (bytes8At (decryptorPtr + 0x3c8#64) b ∗ F) post oom := by
  have_instrs hivB 0 16
  dsimp only [bytes8At]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_str8 hf_0 m0 hm0; wp_steps 1; wp_str8 hf_2 m1 hm1; wp_steps 1
  wp_str8 hf_4 m2 hm2; wp_steps 1; wp_str8 hf_6 m3 hm3; wp_steps 1
  wp_str8 hf_8 m4 hm4; wp_steps 1; wp_str8 hf_10 m5 hm5; wp_steps 1
  wp_str8 hf_12 m6 hm6; wp_steps 1; wp_str8 hf_14 m7 hm7; wp_steps 1
  rw [show (((decryptorPtr + 0x3c8#64) ↦₈ 0#8) ∗ ((decryptorPtr + 0x3c9#64) ↦₈ 0#8) ∗
       ((decryptorPtr + 0x3ca#64) ↦₈ 0#8) ∗ ((decryptorPtr + 0x3cb#64) ↦₈ 0#8) ∗
       ((decryptorPtr + 0x3cc#64) ↦₈ 0#8) ∗ ((decryptorPtr + 0x3cd#64) ↦₈ 0#8) ∗
       ((decryptorPtr + 0x3ce#64) ↦₈ 0#8) ∗ ((decryptorPtr + 0x3cf#64) ↦₈ 0#8)) ∗ F =
      ((decryptorPtr + 0x3c8#64) ↦ₛ List.replicate 8 0#8) ∗ F by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using congrArg (· ∗ F) (zero8_fold (decryptorPtr + 0x3c8#64))]
  exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
    (ha.step (hperm := by simp [wp_norm, arm64_norm, hm7, hm6, hm5, hm4, hm3, hm2, hm1, hm0]))
    (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm, hx8])

private theorem step_hw_loop {P : Program} {fnAddr decryptorPtr target_pc : BitVec 64}
    (hloop : hasInstrs P (fnAddr + 0x9c#64) (decodeWords dropHwLoopWords))
    (s0 : State) {post : State → SepProp → Prop} {oom : State → SepProp} :
    ∀ (n i : Nat) (s : State) (F : SepProp),
      i + (n + 1) = 0x1e0 → s.pc = fnAddr + 0x9c#64 → s.status = .Running → DropAnchor s0 s →
      s.readReg64 .x0 = decryptorPtr → s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 i →
      (∀ sf : State, sf.pc = fnAddr + 0xb0#64 → sf.status = .Running → DropAnchor s0 sf →
        SepWP P target_pc sf (((decryptorPtr + BitVec.ofNat 64 i) ↦ₛ List.replicate (n + 1) 0#8) ∗ F) post oom) →
      SepWP P target_pc s (memRegion (decryptorPtr + BitVec.ofNat 64 i) (n + 1) ∗ F) post oom := by
  intro n; induction n with
  | zero =>
    intro i s F hi hpc hrun ha hx0 hx8 hnext
    obtain rfl : i = 479 := by omega
    rw [memRegion_succ_off decryptorPtr 479 0 (by decide), memRegion_zero, sepConj_emp, sepExists_sepConj_left]
    apply SepWP.exists_elim; intro b
    have_instrs hloop 0 5; wp_steps 3; wp_str8 hf_3 m1 hm1; wp_steps 1
    rw [← pointsToBytes_singleton]
    exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (ha.step (hperm := by simp [wp_norm, arm64_norm, hm1]))
  | succ n' ih =>
    intro i s F hi hpc hrun ha hx0 hx8 hnext
    rw [memRegion_succ_off decryptorPtr i (n' + 1) (by omega), sepConj_assoc, sepExists_sepConj_left]
    apply SepWP.exists_elim; intro b
    have_instrs hloop 0 5; wp_steps 3; wp_str8 hf_3 m1 hm1; wp_steps 1
    wp_if hbr
    · rw [show ((decryptorPtr + BitVec.ofNat 64 i) ↦₈ 0#8) ∗
            (memRegion (decryptorPtr + BitVec.ofNat 64 (i + 1)) (n' + 1) ∗ F) =
          memRegion (decryptorPtr + BitVec.ofNat 64 (i + 1)) (n' + 1) ∗
            (((decryptorPtr + BitVec.ofNat 64 i) ↦₈ 0#8) ∗ F) by sep_ac_rfl]
      refine ih (i + 1) _ _ (by omega) (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun]) (ha.step (hperm := by simp [wp_norm, arm64_norm, hm1]))
        (by simp [wp_norm, arm64_norm, hx0]) (by simp [wp_norm, arm64_norm]; bv_omega)
        fun sf hpc_f hrun_f ha_f => ?_
      rw [show ((decryptorPtr + BitVec.ofNat 64 (i + 1)) ↦ₛ List.replicate (n' + 1) 0#8) ∗
            (((decryptorPtr + BitVec.ofNat 64 i) ↦₈ 0#8) ∗ F) =
          ((decryptorPtr + BitVec.ofNat 64 i) ↦ₛ List.replicate (n' + 2) 0#8) ∗ F by
        rw [show List.replicate (n' + 2) (0#8) = 0#8 :: List.replicate (n' + 1) 0#8 from rfl,
            pointsToBytes_cons, show decryptorPtr + BitVec.ofNat 64 i + 1#64 =
              decryptorPtr + BitVec.ofNat 64 (i + 1) by bv_omega]; sep_ac_rfl]
      exact hnext sf hpc_f hrun_f ha_f
    · have : i < 479 := by omega
      exfalso; bv_omega

private theorem step_sw_loop {P : Program} {fnAddr target_pc : BitVec 64}
    (hloop : hasInstrs P (fnAddr + 0xc4#64) (decodeWords dropSwLoopWords))
    (s0 : State) {post : State → SepProp → Prop} {oom : State → SepProp} :
    ∀ (k : Nat) (p : BitVec 64) (s : State) (F : SepProp),
      k < 120 → s.pc = fnAddr + 0xc4#64 → s.status = .Running → DropAnchor s0 s →
      s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (8 * (k + 1)) → s.readReg64 (.gpr 9#5) = p →
      (∀ sf : State, sf.pc = fnAddr + 0xd4#64 → sf.status = .Running → DropAnchor s0 sf →
        SepWP P target_pc sf ((p ↦ₛ List.replicate (8 * (k + 1)) 0#8) ∗ F) post oom) →
      SepWP P target_pc s (memRegion p (8 * (k + 1)) ∗ F) post oom := by
  intro k; induction k with
  | zero =>
    intro p s F _ hpc hrun ha hx8 hx9 hnext
    simp only [Nat.zero_add, Nat.mul_one] at hx8 ⊢
    rw [memRegion_eight p, sepExists_sepConj_left]; apply SepWP.exists_elim; intro w
    have_instrs hloop 0 4; wp_str64 hf_0 m1 hm1; wp_steps 3
    rw [pointsTo64_zero_eq_replicate]
    exact hnext _ (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun])
      (ha.step (hperm := by simp [wp_norm, arm64_norm, hm1]))
  | succ k' ih =>
    intro p s F hk hpc hrun ha hx8 hx9 hnext
    rw [show 8 * (k' + 1 + 1) = 8 + 8 * (k' + 1) by omega,
        memRegion_split p 8 (8 * (k' + 1)) (by omega), memRegion_eight p, sepConj_assoc, sepExists_sepConj_left]
    apply SepWP.exists_elim; intro w
    have_instrs hloop 0 4; wp_str64 hf_0 m1 hm1; wp_steps 3
    wp_if hbr
    · rw [show (p ↦₆₄ 0#64) ∗ (memRegion (p + BitVec.ofNat 64 8) (8 * (k' + 1)) ∗ F) =
          memRegion (p + 8#64) (8 * (k' + 1)) ∗ ((p ↦₆₄ 0#64) ∗ F) by sep_ac_rfl]
      refine ih (p + 8#64) _ _ (by omega) (by simp [wp_norm, arm64_norm, bv_lin_norm])
        (by simp [wp_norm, arm64_norm, hrun]) (ha.step (hperm := by simp [wp_norm, arm64_norm, hm1]))
        (by simp [wp_norm, arm64_norm]; bv_omega) (by simp [wp_norm, arm64_norm])
        fun sf hpc_f hrun_f ha_f => ?_
      rw [show ((p + 8#64) ↦ₛ List.replicate (8 * (k' + 1)) 0#8) ∗ ((p ↦₆₄ 0#64) ∗ F) =
          (p ↦ₛ List.replicate (8 * (k' + 1 + 1)) 0#8) ∗ F by
        rw [show 8 * (k' + 1 + 1) = 8 + 8 * (k' + 1) by omega,
            pointsTo64_zero_eq_replicate, List.replicate_add, pointsToBytes_append, List.length_replicate]
        sep_ac_rfl]
      exact hnext sf hpc_f hrun_f ha_f
    · have : 8 * (k' + 1 + 1) < 2 ^ 64 ∧ 8 * (k' + 1 + 1) ≠ 8 := by omega
      exfalso; bv_omega

/-! ## 5. Top-Level `subroutine_ok` Theorems -/

/-- Exact zeroization `subroutine_ok` theorem for `drop_glue<Decryptor<autodetect::Aes256>>`. -/
theorem dropDecryptorZero_subroutine_ok {P : Program} {fnAddr storageAddr : BitVec 64}
    (hc : hasInstrs P fnAddr (dropDecryptorInstrs fnAddr storageAddr)) :
    subroutine_ok P fnAddr (dropDecryptorZeroSpec storageAddr) := by
  have hseg := DropCodeSegs.of_hasInstrs hc
  apply subroutine_ok_of_sepWP_init
  rintro ⟨decryptorPtr, storageVal⟩ R s0 hpc hrun hpre hsp
  dsimp only [dropDecryptorZeroSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hx0, hpre⟩
  refine ⟨_, Satisfies.mono (sepConj_mono_left (dropPre_unpack decryptorPtr storageAddr storageVal s0.sp)) hpre, ?_⟩
  apply SepWP.exists_elim; intro ba; apply SepWP.exists_elim; intro bb; apply SepWP.exists_elim; intro stk
  rw [show bytes8At (decryptorPtr + 0x3c0#64) ba ∗ bytes8At (decryptorPtr + 0x3c8#64) bb ∗
        memRegion decryptorPtr 0x3c0 ∗ (storageAddr ↦₈ storageVal) ∗
        ((s0.sp - 16#64) ↦₆₄ stk.1) ∗ ((s0.sp - 8#64) ↦₆₄ stk.2) =
      bytes8At (decryptorPtr + 0x3c0#64) ba ∗
        (bytes8At (decryptorPtr + 0x3c8#64) bb ∗ memRegion decryptorPtr 0x3c0 ∗
         (storageAddr ↦₈ storageVal) ∗ ((s0.sp - 16#64) ↦₆₄ stk.1) ∗ ((s0.sp - 8#64) ↦₆₄ stk.2))
      by sep_ac_rfl]
  refine step_iv_partA hseg.head hseg.adrp hseg.ivA hpc hrun hx0 fun s1 hpc1 hrun1 ha1 hx0_1 hx8_1 => ?_
  rw [show ((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 8 0#8) ∗
        (bytes8At (decryptorPtr + 0x3c8#64) bb ∗ memRegion decryptorPtr 0x3c0 ∗
         (storageAddr ↦₈ storageVal) ∗ ((s0.sp - 16#64) ↦₆₄ stk.1) ∗ ((s0.sp - 8#64) ↦₆₄ stk.2)) =
      bytes8At (decryptorPtr + 0x3c8#64) bb ∗
        (((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 8 0#8) ∗ memRegion decryptorPtr 0x3c0 ∗
         (storageAddr ↦₈ storageVal) ∗ ((s0.sp - 16#64) ↦₆₄ stk.1) ∗ ((s0.sp - 8#64) ↦₆₄ stk.2))
      by sep_ac_rfl]
  refine step_iv_partB hseg.ivB hpc1 hrun1 ha1 hx0_1 hx8_1 fun s2 hpc2 hrun2 ha2 hx0_2 hx8_2 => ?_
  rw [show ((decryptorPtr + 0x3c8#64) ↦ₛ List.replicate 8 0#8) ∗
        (((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 8 0#8) ∗ memRegion decryptorPtr 0x3c0 ∗
         (storageAddr ↦₈ storageVal) ∗ ((s0.sp - 16#64) ↦₆₄ stk.1) ∗ ((s0.sp - 8#64) ↦₆₄ stk.2)) =
      ((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 0x10 0#8) ∗ memRegion decryptorPtr 0x3c0 ∗
        (storageAddr ↦₈ storageVal) ∗ ((s0.sp - 16#64) ↦₆₄ stk.1) ∗ ((s0.sp - 8#64) ↦₆₄ stk.2) by
    rw [show (0x10 : Nat) = 8 + 8 from rfl, List.replicate_add, pointsToBytes_append,
        List.length_replicate, show decryptorPtr + 0x3c0#64 + BitVec.ofNat 64 8 =
          decryptorPtr + 0x3c8#64 by bv_omega]; sep_ac_rfl]
  refine SepWP.step_ldr8 (hpc := hpc2) (hrun := hrun2) (hfetch := hseg.ldrb) (hsp := rfl)
    (haddr := show evalAddrMode s2 (.Offset (.gpr 8#5) (pageLo12 storageAddr)) = (storageAddr, none) by
      simp [evalAddrMode, pageLo12, hx8_2])
    (hload := SepLoad8.of_eq (by sep_ac_rfl)) (hexec := rfl) ?_
  have hbranch := hseg.branch; have_instrs hbranch 0 2; wp_steps 2
  wp_if hbr
  · have hsw : (storageVal == 1#8) = false := by simp; bv_omega
    have hswSetup := hseg.swSetup; have_instrs hswSetup 0 2; wp_steps 2
    rw [show ((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 0x10 0#8) ∗ memRegion decryptorPtr 0x3c0 ∗
          (storageAddr ↦₈ storageVal) ∗ ((s0.sp - 16#64) ↦₆₄ stk.1) ∗ ((s0.sp - 8#64) ↦₆₄ stk.2) =
        memRegion decryptorPtr (8 * (119 + 1)) ∗
          (((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 0x10 0#8) ∗
           (storageAddr ↦₈ storageVal) ∗ ((s0.sp - 16#64) ↦₆₄ stk.1) ∗ ((s0.sp - 8#64) ↦₆₄ stk.2)) by
      change ((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 0x10 0#8) ∗ memRegion decryptorPtr 0x3c0 ∗ _ =
        memRegion decryptorPtr 0x3c0 ∗ _; sep_ac_rfl]
    refine step_sw_loop hseg.swLoop s0 119 decryptorPtr _ _ (by decide)
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun2])
      ha2.step (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])
      fun s4 hpc4 hrun4 ha4 => ?_
    have hswEpi := hseg.swEpi; have_instrs hswEpi 0 2
    wp_steps 2
    apply SepWP.done (by simpa [wp_norm, arm64_norm] using ha4.lr) (by simp [wp_norm, arm64_norm, hrun4])
    refine ⟨fun hsat => ?_, by simp [wp_norm, arm64_norm, ha4.sp],
      CalleeSavedPreserved.trans ha4.cs (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨ha4.pres.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])),
      Satisfies.mono ?_ hsat⟩
    unfold dropDecryptorPostSpatial; simp only [hsw, Bool.false_eq_true, ↓reduceIte]
    refine sepConj_mono_left (Entails.trans (Entails.of_eq_explicit (show _ =
        ((decryptorPtr ↦ₛ List.replicate 0x3c0 0#8) ∗ ((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 0x10 0#8)) ∗
        (storageAddr ↦₈ storageVal) ∗ (((s0.sp - 16#64) ↦₆₄ stk.1) ∗ ((s0.sp - 8#64) ↦₆₄ stk.2)) by
      change ((decryptorPtr ↦ₛ List.replicate 0x3c0 0#8) ∗ _) = _; sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (stackFrameAt_16_pack s0.sp stk.1 stk.2))))
  · have hhw : (storageVal == 1#8) = true := by simp; bv_omega
    have hhwSetup := hseg.hwSetup; have_instrs hhwSetup 0 2
    have hsp2 : s2.sp = s0.sp - 16#64 := ha2.sp
    have hsp_align2 : (s0.sp - 16#64) &&& 15#64 = 0#64 := sp_sub16_and_15 hsp
    wp_steps 1
    refine step_str64_perm hf_1 (by simp [wp_norm, arm64_norm, bv_lin_norm])
      (by simp [wp_norm, arm64_norm, hrun2])
      (by simp [checkAddrSPAligned, wp_norm, arm64_norm, hsp2, hsp_align2])
      (show evalAddrMode _ _ = (s0.sp - 8#64, none) by simp [evalAddrMode, wp_norm, arm64_norm, hsp2])
      (show _ = decryptorPtr by simp [wp_norm, arm64_norm, hx0_2])
      (by wp_sep_access) rfl fun m_stk hm_stk => ?_
    rw [show (0x3c0 : Nat) = 0x1e0 + 0x1e0 from rfl,
        memRegion_split decryptorPtr 0x1e0 0x1e0 (by decide),
        show decryptorPtr + BitVec.ofNat 64 0x1e0 = decryptorPtr + 0x1e0#64 from rfl,
        show ((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 0x10 0#8) ∗
          (memRegion decryptorPtr 0x1e0 ∗ memRegion (decryptorPtr + 0x1e0#64) 0x1e0) ∗
          (storageAddr ↦₈ storageVal) ∗ ((s0.sp - 16#64) ↦₆₄ stk.1) ∗ ((s0.sp - 8#64) ↦₆₄ decryptorPtr) =
        memRegion (decryptorPtr + BitVec.ofNat 64 0) (479 + 1) ∗
          (memRegion (decryptorPtr + 0x1e0#64) 0x1e0 ∗
           ((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 0x10 0#8) ∗
           (storageAddr ↦₈ storageVal) ∗ ((s0.sp - 16#64) ↦₆₄ stk.1) ∗ ((s0.sp - 8#64) ↦₆₄ decryptorPtr)) by
          rw [show decryptorPtr + BitVec.ofNat 64 0 = decryptorPtr by bv_omega]
          change ((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 0x10 0#8) ∗
            (memRegion decryptorPtr 0x1e0 ∗ memRegion (decryptorPtr + 0x1e0#64) 0x1e0) ∗ _ =
            memRegion decryptorPtr 0x1e0 ∗ _; sep_ac_rfl]
    refine step_hw_loop hseg.hwLoop s0 479 0 _ _ (by decide)
      (by simp [wp_norm, arm64_norm, bv_lin_norm]) (by simp [wp_norm, arm64_norm, hrun2])
      (ha2.step (hperm := by simp [wp_norm, arm64_norm, hm_stk]))
      (by simp [wp_norm, arm64_norm, hx0_2]) (by simp [wp_norm, arm64_norm])
      fun s4 hpc4 hrun4 ha4 => ?_
    have hhwEpi := hseg.hwEpi; have_instrs hhwEpi 0 3
    wp_steps 3
    apply SepWP.done (by simpa [wp_norm, arm64_norm] using ha4.lr) (by simp [wp_norm, arm64_norm, hrun4])
    refine ⟨fun hsat => ?_, by simp [wp_norm, arm64_norm, ha4.sp],
      CalleeSavedPreserved.trans ha4.cs (by simp [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm])⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨ha4.pres.trans (PureStepPreserved.of_proj_perm (by simp [wp_norm, arm64_norm]) (by simp [wp_norm, arm64_norm])),
      Satisfies.mono ?_ hsat⟩
    unfold dropDecryptorPostSpatial; simp only [hhw, ↓reduceIte]
    rw [show decryptorPtr + BitVec.ofNat 64 0 = decryptorPtr by bv_omega]
    refine sepConj_mono_left (Entails.trans (Entails.of_eq_explicit (show _ =
        (((decryptorPtr ↦ₛ List.replicate 0x1e0 0#8) ∗ memRegion (decryptorPtr + 0x1e0#64) 0x1e0) ∗
         ((decryptorPtr + 0x3c0#64) ↦ₛ List.replicate 0x10 0#8)) ∗
        (storageAddr ↦₈ storageVal) ∗ (((s0.sp - 16#64) ↦₆₄ stk.1) ∗ ((s0.sp - 8#64) ↦₆₄ decryptorPtr)) by
      change ((decryptorPtr ↦ₛ List.replicate 0x1e0 0#8) ∗ _) = _; sep_ac_rfl))
      (sepConj_mono_right (sepConj_mono_right (stackFrameAt_16_pack s0.sp stk.1 decryptorPtr))))

/-- Region-preserving `subroutine_ok` theorem for `drop_glue<Decryptor<autodetect::Aes256>>`. -/
theorem dropDecryptor_subroutine_ok {P : Program} {fnAddr storageAddr : BitVec 64}
    (hc : hasInstrs P fnAddr (dropDecryptorInstrs fnAddr storageAddr)) :
    subroutine_ok P fnAddr (dropDecryptorSpec storageAddr) := by
  refine (dropDecryptorZero_subroutine_ok hc).conseq
    (fun _ _ => Entails.refl _) (fun ⟨decryptorPtr, storageVal⟩ _ _ => ?_)
    (fun _ _ _ => Entails.refl _) (fun _ _ _ _ => Entails.refl _)
  exact sepConj_mono_right (sepConj_mono_left
    (dropDecryptorPostSpatial_entails_memRegion decryptorPtr storageVal))

/-- Byte-slice `subroutine_ok` theorem for `drop_glue<Decryptor<autodetect::Aes256>>` (`0x3d0` B). -/
theorem dropDecryptorBytes_subroutine_ok {P : Program} {fnAddr storageAddr : BitVec 64}
    (hc : hasInstrs P fnAddr (dropDecryptorInstrs fnAddr storageAddr)) :
    subroutine_ok P fnAddr (dropDecryptorBytesSpec storageAddr) := by
  refine subroutine_ok_map (dropDecryptor_subroutine_ok hc) ?_
  rintro ⟨decryptorPtr, storageVal, bs⟩ R s0 hpre
  dsimp only [dropDecryptorBytesSpec, dropDecryptorSpec] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hlen⟩, hpre⟩
  refine ⟨(decryptorPtr, storageVal), R, ?_, fun sf hpost => ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hx0, ?_⟩
    have hm : (decryptorPtr ↦ₛ bs) ⊢ memRegion decryptorPtr 0x3d0 :=
      hlen ▸ pointsToBytes_entails_memRegion decryptorPtr bs
    exact Satisfies.mono (sepConj_mono_left (sepConj_mono_left hm)) hpre
  · rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1, by rw [← memRegion_eq_exists_bytes decryptorPtr 0x3d0 (by decide)]; exact hpost.2⟩

end
end
end LibsignalBinary.Proofs.HookDischarge.CryptoAes.Armv8.DropDecryptor
