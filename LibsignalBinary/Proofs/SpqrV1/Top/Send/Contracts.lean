/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesBridge1 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc -- proof-setup: allow-public-import
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import ProofLib
import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeGrow
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Chain.FromPb
import LibsignalBinary.Proofs.SpqrV1.Chain.IntoPb
import LibsignalBinary.Proofs.SpqrV1.Chain.SendKey
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceOk
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Proof
import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.Proof
import LibsignalBinary.Proofs.SpqrV1.States.IntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk1
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendChunk2
import LibsignalBinary.Proofs.SpqrV1.Top.ChainFromVersionNegotiation.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Proof
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainResolve
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.TripleRatchet.Bytes.Drops
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer

/-!
# Callee Contracts and `.rodata` Scaffolding for `spqr::send::<HookRng>` (`0x3085c`)

**Checked by Lean.**

Wires `SpqrHooks` and allocator hook helpers across `tripleRatchetExterns` for
`spqr::send::<HookRng>`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk

/-! ## `.rodata` Bundle Introduction (`spqrSendRoAt`) -/

theorem optProtoInnerStateAt_canonical_eq_drop_send (A : RustAlloc) (a : BitVec 64)
    (opt : Option V1State.InnerState) :
    DecodeState.optProtoInnerStateAt canonicalV1InnerHeap A a opt =
      Drop.optProtoInnerStateAt A a opt :=
  optProtoInnerStateAt_canonical_eq_drop A a opt

/-! ## `SpqrSendContracts` Assembly -/

theorem spqrHooks_tripleRatchetExterns {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {K : MlKem}
    {abs : String → Option (State → State)}
    (hSH : SpqrHooks C A K abs) :
    SpqrHooks C A K (tripleRatchetExterns C ctl abs) where
  fromSeed := hSH.fromSeed
  pk1 := hSH.pk1
  pk2 := hSH.pk2
  encaps1 := hSH.encaps1
  encaps2 := hSH.encaps2
  decaps := hSH.decaps
  validatePk := hSH.validatePk
  hmac := hSH.hmac

theorem hookSat_allocZeroed_tripleRatchetExterns {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hZero : HookSat abs allocZeroedName (rustAllocZeroedSpec A)) :
    HookSat (tripleRatchetExterns C ctl abs) allocZeroedName (rustAllocZeroedSpec A) :=
  hZero

section ChainResolveExt

set_option linter.unusedVariables false
open ProofLib.ProgramReflection CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
private theorem stackAt_callee_split_ext (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide) :
    stackAt sp spqrSendCalleeStack = memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ stackAt sp n := by
  have hbd : n + (spqrSendCalleeStack - n) ≤ 2 ^ 64 := by have : n ≤ 123008 := hle; change n + (123008 - n) ≤ 2 ^ 64; omega
  have h := ProofLib.stackAt_split_bottom sp n (spqrSendCalleeStack - n) hbd; rwa [Nat.add_sub_of_le hle] at h

private theorem panic_frame_anyHeap_ext {m : Memory} {φ₁ φ₂ : Prop} {F Fr : SepProp}
    (himp : φ₁ → φ₂) (hm : m ⊨ ((⌜φ₁⌝ ∗ anyHeap) ∗ F) ∗ Fr) : m ⊨ (⌜φ₂⌝ ∗ anyHeap) ∗ Fr := by
  have h1 : ((⌜φ₁⌝ ∗ anyHeap) ∗ F) ∗ Fr ⊢ ⌜φ₁⌝ ∗ ((anyHeap ∗ F) ∗ Fr) := Entails.of_eq (by ac_rfl)
  have hm' := Satisfies.mono h1 hm; rw [satisfies_pure_sepConj] at hm'
  exact Satisfies.mono (sepConj_mono_left (Entails.pure_right (himp hm'.1) (entails_anyHeap _))) hm'.2

private theorem panic_not_exited_ext {m : Memory} {R : SepProp} (h : m ⊨ ⌜False⌝ ∗ R) : False :=
  ((satisfies_pure_sepConj _ _ _).mp h).1

private theorem readReg32_of_readReg64_eq_ext {s1 s2 : State} {r : Reg} (h : s1.readReg64 r = s2.readReg64 r) : s1.readReg32 r = s2.readReg32 r := by unfold State.readReg32; rw [h]
private theorem flag_preserve_ext {s1 s2 : State} (h : s1.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s1.readReg32 .x20 = 0#32)
    (hx20 : s2.readReg64 .x20 = s1.readReg64 .x20) (hx21 : s2.readReg64 .x21 = s1.readReg64 .x21) :
    s2.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s2.readReg32 .x20 = 0#32 :=
  h.imp (hx21.trans ·) ((readReg32_of_readReg64_eq_ext hx20).trans ·)
private theorem flag_of_csinc_ext {s : State} {x21 : BitVec 64} (hx21 : s.readReg64 .x21 = x21)
    (hx20 : s.readReg32 .x20 = (if (x21 + 1#64 != 0#64) = true then 0#32 else 1#32)) :
    s.readReg64 .x21 = LibsignalTripleRatchetRepr.noneCap ∨ s.readReg32 .x20 = 0#32 := by
  by_cases h : x21 = LibsignalTripleRatchetRepr.noneCap
  · exact Or.inl (hx21.trans h)
  · refine Or.inr (hx20.trans ?_)
    have hne : (x21 + 1#64 != 0#64) = true := by unfold LibsignalTripleRatchetRepr.noneCap at h; simp only [bne_iff_ne, ne_eq]; intro h0; apply h; bv_omega
    simp [hne]
private theorem memRegion_1260_88_eq_32_56_ext (sp : BitVec 64) : memRegion (sp + 0x1260#64) 88 = memRegion (sp + 0x1260#64) 32 ∗ memRegion (sp + 0x1280#64) 56 := ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 32) (k := 56) (b' := sp + 0x1280#64) rfl (by bv_omega) (by decide)
private theorem memRegion_1260_88_eq_40_48_ext (sp : BitVec 64) : memRegion (sp + 0x1260#64) 88 = memRegion (sp + 0x1260#64) 40 ∗ memRegion (sp + 0x1288#64) 48 := ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 40) (k := 48) (b' := sp + 0x1288#64) rfl (by bv_omega) (by decide)
private theorem memRegion_590_88_eq_80_8_ext (sp : BitVec 64) : memRegion (sp + 0x590#64) 88 = memRegion (sp + 0x590#64) 80 ∗ memRegion (sp + 0x5e0#64) 8 := ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 80) (k := 8) (b' := sp + 0x5e0#64) rfl (by bv_omega) (by decide)
private theorem memRegion_590_88_eq_24_64_ext (sp : BitVec 64) : memRegion (sp + 0x590#64) 88 = memRegion (sp + 0x590#64) 24 ∗ memRegion (sp + 0x5a8#64) 64 := ProofLib.memRegion_split' (b := sp + 0x590#64) (n := 24) (k := 64) (b' := sp + 0x5a8#64) rfl (by bv_omega) (by decide)
private theorem memRegion_1060_80_eq_24_56_ext (sp : BitVec 64) : memRegion (sp + 0x1060#64) 80 = memRegion (sp + 0x1060#64) 24 ∗ memRegion (sp + 0x1078#64) 56 := ProofLib.memRegion_split' (b := sp + 0x1060#64) (n := 24) (k := 56) (b' := sp + 0x1078#64) rfl (by bv_omega) (by decide)
private theorem addsPState64_noneCap_z_ext : (addsPState64 LibsignalTripleRatchetRepr.noneCap 1#64).z = true := by unfold addsPState64 AddWithCarry64 LibsignalTripleRatchetRepr.noneCap; decide
private theorem addsPState64_z_false_of_ne_noneCap_ext {x21 : BitVec 64} (hne : x21 ≠ LibsignalTripleRatchetRepr.noneCap) : (addsPState64 x21 1#64).z = false := by
  unfold addsPState64 AddWithCarry64 LibsignalTripleRatchetRepr.noneCap at *; simp only [Bool.false_eq_true, ↓reduceIte, beq_eq_false_iff_ne]; intro h; apply hne; bv_omega
private theorem setPC_preserves_ext {s1 s : State} {pc : BitVec 64} (h : s1 = s.setPC pc) :
    s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧ (∀ r, s1.readReg64 r = s.readReg64 r) := by subst h; exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
private theorem optEpochSecretRegSlotAt_some_ne_ext (A : RustAlloc) (sp x21 x27 : BitVec 64) (es : EpochSecret) :
    optEpochSecretRegSlotAt A sp x21 x27 (some es) ⊢ ⌜x21 ≠ LibsignalTripleRatchetRepr.noneCap⌝ ∗ optEpochSecretRegSlotAt A sp x21 x27 (some es) := by
  dsimp only [optEpochSecretRegSlotAt]; apply Entails.pure_left; intro hne; exact Entails.pure_right hne (Entails.pure_right hne (Entails.refl _))
end ChainResolveExt

end CryptoVerification.SpqrV1.Top.Send
