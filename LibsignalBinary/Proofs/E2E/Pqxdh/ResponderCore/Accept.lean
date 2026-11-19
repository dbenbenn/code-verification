/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.AllocAndVec -- proof-setup: allow-public-import
import all Init.Data.String.Defs
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# Shared Layouts and Pure Helpers for `<Pqxdh as Handshake>::accept`

Defines memory layouts, error postcondition predicates, and pure/separation-logic helpers
shared across the relocatable `Pqxdh::accept` proofs.
-/

public section
set_option autoImplicit false
set_option maxHeartbeats 48000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
namespace CryptoVerification.E2E.Pqxdh.ResponderCore
open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh CryptoVerification.E2E.Pqxdh.Initiator
abbrev Bytes := CryptoVerification.E2E.Pqxdh.Initiator.Bytes
abbrev memRegion_cells := @CryptoVerification.E2E.Pqxdh.Initiator.memRegion_cells
abbrev stackAt_split_cells := @CryptoVerification.E2E.Pqxdh.Initiator.stackAt_split_cells
abbrev memRegion_eight := @ProofLib.memRegion_eight
abbrev kyberDecapsStub : String := "libcrux_ml_kem::mlkem1024::kyber::decapsulate"
@[expose] def dalekMontToEdOutAt (P : Primitives) (outPtr : BitVec 64) (inBytes : Bytes) (signBit : UInt8) :
    SepProp :=
  match P.montToEd inBytes signBit with
  | some edPt => outPtr ↦ₛ (u64le 1#64 ++ fitBv8 160 edPt)
  | none      => (outPtr ↦₆₄ 0#64) ∗ memRegion (outPtr + 8#64) 160
@[expose] def dalekMontToEdStubSpec (P : Primitives) (_img : Unit :=
    ()) : Spec DalekMontToEdGhost where
  pre := fun g s => ⌜s.readReg64 .x0 = g.inPtr ∧ (s.readReg64 .x1).setWidth 8 =
    BitVec.ofNat 8 g.signBit.toNat ∧ s.readReg64 .x8 = g.outPtr ∧ g.inBytes.length = 32⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ memRegion g.outPtr 168 ∗ stackAt s.sp pqxdhHookStack
  post := fun g s0 sf => ⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      dalekMontToEdOutAt P g.outPtr g.inBytes (g.signBit &&& 1) ∗ stackAt s0.sp pqxdhHookStack
abbrev PqxdhHookContracts : Type := Unit
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre readReg_setPC_pre readReg_setMem_setPC_pre
macro "cells_pre_unfold_fast" : tactic =>
  `(tactic| (
    conv => arg 4; simp (config := { maxSteps := 1000000 }) only [
      cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.add_assoc,
        BitVec.reduceAdd, BitVec.reduceSub]))
macro "wp_simp_pre_fast " "[" rules:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (conv => arg 4; simp only [$rules,*]))
macro "wp_extract_exists" : tactic =>
  `(tactic| (
    (conv =>
      arg 4
      simp (config := { maxSteps := 1000000 }) only [
        sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc])
    repeat' (apply SepWP.exists_elim; intro _)
    try (apply SepWP.pure_elim; intro _)))
abbrev Model.DRKey := CryptoVerification.E2E.Pqxdh.Initiator.DRKey
abbrev Model.encodeEC := CryptoVerification.E2E.Pqxdh.Initiator.encodeEC
abbrev Model.encodeKEM := CryptoVerification.E2E.Pqxdh.Initiator.encodeKEM
abbrev Model.decodeEC := CryptoVerification.E2E.Pqxdh.Initiator.decodeEC
abbrev Model.decodeKEM := CryptoVerification.E2E.Pqxdh.Initiator.decodeKEM
abbrev calculateAgreementStack : Nat := 160 + allocHookStack
abbrev createChainStack : Nat := 576 + calculateAgreementStack
@[expose] def pqxdhCalculateAgreementResultAt (P : Primitives) (A : RustAlloc) (r : BitVec 64) (ourSk32
    theirPk32 : Bytes) : SepProp := if P.x25519 ourSk32 theirPk32 = List.replicate 32 0 then
    (r ↦₆₄ 1#64) ∗ (∃∗ hi : BitVec 56, (r + 8#64) ↦₆₄ (hi ++ 3#8)) ∗ (∃∗ u2 : BitVec 64, (r +
      16#64) ↦₆₄ u2)
  else (r ↦₆₄ 0#64) ∗ boxSliceU8 A (r + 8#64) (bytesToBv8 (P.x25519 ourSk32 theirPk32))
@[local simp, local arm64_norm, local wp_norm] theorem extractLsb_hi56_3 (hi : BitVec 56) :
    (hi ++ 3#8).extractLsb' 0 8 = 3#8 := by bv_bits
@[local simp, local arm64_norm, local wp_norm] theorem and_ff_hi56_3 (hi : BitVec 56) :
    (hi ++ 3#8) &&& 0xff#64 = 3#64 := by bv_bits
@[local simp, local arm64_norm, local wp_norm] theorem and_ff32_hi56_3 (hi : BitVec 56) :
    BitVec.truncate 32 (hi ++ 3#8) &&& 0xff#32 = 3#32 := by bv_bits
@[local simp, local arm64_norm, local wp_norm]
theorem zext64_trunc32_hi56_3_and_ff (hi : BitVec 56) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (hi ++ 3#8)) &&& 255#64 = 3#64 := by bv_bits
theorem boxSliceU8_32_entails (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) (hlen :
    bs.length = 32) : boxSliceU8 A a bs ⊢
      ∃∗ ptr : BitVec 64, (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ 32#64) ∗ (ptr ↦ₛ bs) ∗ A.live ptr 32 1 := by
  dsimp only [boxSliceU8]; rw [hlen, BitVec.ofNat_eq_ofNat]
  refine Entails.sepExists_elim fun ptr => ?_; refine Entails.pure_left fun _ => ?_
  exact Entails.sepExists_right ptr (Entails.refl _)
theorem SepWPp.rw_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp} {Q Qp : State
    → SepProp → Prop} (hP : P = P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := hP ▸ h
macro "sep_elim_exists" : tactic =>
  `(tactic| (
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    repeat' (first | (apply SepWPp.exists_elim; intro _) | (apply SepWP.exists_elim; intro _))))
theorem SepWPp.split_alloc {prog : Program} {ret : BitVec 64} {s : State} {A : RustAlloc} {sp sp' :
    BitVec 64} {tr : List TraceEvent} {size align : Nat} {F : SepProp} {Q Qp : State → SepProp →
    Prop} (hsp : sp = sp') (hnull : s.readReg64 (.gpr 0#5) = 0#64 → s.trace = tr ++
    [allocFailedEvent] → SepWPp prog ret s (A.pool ∗ stackAt sp' allocHookStack ∗ F) Q Qp)
    (hok : s.readReg64 (.gpr 0#5) ≠ 0#64 → (s.readReg64 (.gpr 0#5)).toNat % align = 0 → s.trace =
      tr → SepWPp prog ret s (A.pool ∗ stackAt sp' allocHookStack ∗
        A.live (s.readReg64 (.gpr 0#5)) size align ∗ memRegion (s.readReg64 (.gpr 0#5)) size ∗
        F) Q Qp) : SepWPp prog ret s (A.pool ∗ stackAt sp allocHookStack ∗
      (if s.readReg64 (.gpr 0#5) = 0 then ⌜s.trace = tr ++ [allocFailedEvent]⌝
        else ⌜(s.readReg64 (.gpr 0#5)).toNat % align = 0 ∧ s.trace = tr⌝ ∗
        A.live (s.readReg64 (.gpr 0#5)) size align ∗ memRegion (s.readReg64 (.gpr 0#5)) size) ∗
        F) Q Qp := by
  subst hsp; by_cases h0 : s.readReg64 (.gpr 0#5) = 0
  · simp only [h0, ↓reduceIte]; intro R hm
    have hm' : s.mem ⊨ ⌜s.trace = tr ++ [allocFailedEvent]⌝ ∗ ((A.pool ∗ stackAt sp allocHookStack ∗
      F) ∗ R) := (by ac_nf at hm ⊢); rw [satisfies_pure_sepConj] at hm'
    exact hnull h0 hm'.1 R hm'.2
  · simp only [h0, ↓reduceIte]; intro R hm
    have hm' : s.mem ⊨ ⌜(s.readReg64 (.gpr 0#5)).toNat % align = 0 ∧ s.trace = tr⌝ ∗ ((A.pool ∗
      stackAt sp allocHookStack ∗ A.live (s.readReg64 (.gpr 0#5)) size align ∗
      memRegion (s.readReg64 (.gpr 0#5)) size ∗ F) ∗ R) := by ac_nf at hm ⊢
    rw [satisfies_pure_sepConj] at hm'; exact hok h0 hm'.1.1 hm'.1.2 R hm'.2
theorem allocFailedIn_panicked_of_append {s0 sf : State} (htr : sf.trace = s0.trace ++
    [allocFailedEvent]) :
    allocFailedIn s0 (Rust.panicked sf) ∧ s0.trace <+: (Rust.panicked sf).trace := by
  simp [allocFailedIn, Rust.panicked, htr]
@[expose] def ecPubKeyIsCanonicalCallSpec (P : Primitives) : Spec KeyCanonicalGhost where
  pre := fun g s => ⌜s.readReg64 .x0 = g.keyPtr ∧ g.keyBytes.length = 32⌝ ∗
    (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗ stackAt s.sp (pqxdhHookStack + 400)
  post := fun g s0 sf => ⌜sf.trace = s0.trace ∧ (sf.readReg64 .x0).setWidth 8 =
      (if P.isCanonicalEC g.keyBytes then 1#8 else 0#8)⌝ ∗ (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗
      stackAt s0.sp (pqxdhHookStack + 400)
@[expose] def toSignalPqxdhPrimitives (P : Primitives) : SignalPqxdh.Primitives where
  x25519 := P.x25519; x25519Base := P.x25519Base; isCanonical := P.isCanonical
  sigPkGen := P.sigPkGen; sigSign := P.sigSign; sigVerify := P.sigVerify; sha512 := P.sha512
  scalarMul := P.scalarMul; scalarAdd := P.scalarAdd
  scalarFromBytesModOrder := P.scalarFromBytesModOrder; scalarFromWide := P.scalarFromWide
  montToEd := fun u s =>
    (P.montToEd u s).map LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.unpackEdBytes
  isTorsionFree := fun pt =>
    P.isTorsionFree (LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.packEdBytes pt)
  edNeg := fun pt =>
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.unpackEdBytes
      (P.edNeg (LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.packEdBytes pt))
  doubleScalarMulBasepoint := fun h a s =>
    LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.unpackEdBytes
      (P.doubleScalarMulBasepoint h
        (LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.packEdBytes a) s)
  compress := fun pt =>
    P.compress (LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.packEdBytes pt)
  kemKeyGen := P.kemKeyGen; kemEncaps := P.kemEncaps; kemDecaps := P.kemDecaps
  hkdfDerive96 := fun s =>
    let dk := P.hkdfDerive96 s
    ⟨dk.rootKey, dk.chainKey, dk.pqrKey⟩
  rootCreateChain := P.rootCreateChain; chainKdfSeed := P.chainKdfSeed
  chainKdfNext := P.chainKdfNext
  spqrInitSend := fun k c => P.spqrInitSend k c
  spqrInitRecv := fun k m => P.spqrInitRecv k m
  deriveMsgKeys := fun s salt =>
    let mk := P.deriveMsgKeys s salt
    ⟨mk.cipherKey, mk.macKey, mk.iv⟩
  aeadEnc := fun mk ad pt => P.aeadEnc ⟨mk.cipherKey, mk.macKey, mk.iv⟩ ad pt
  aeadDec := fun mk ad ct => P.aeadDec ⟨mk.cipherKey, mk.macKey, mk.iv⟩ ad ct
  pow8 := P.pow8; isValidDhTriple := P.isValidDhTriple; sha256Compress := P.sha256Compress
  sha512Compress := P.sha512Compress; aesEncBlock := P.aesEncBlock; aesDecBlock := P.aesDecBlock

theorem toSignalPqxdhPrimitives_montToEdBytes_eq (P : Primitives)
    (hmontLen : ∀ u s pt, P.montToEd u s = some pt → pt.length = 160)
    (u : Bytes) (s : UInt8) :
    (toSignalPqxdhPrimitives P).montToEdBytes u s = P.montToEd u s := by
  unfold _root_.SignalPqxdh.Primitives.montToEdBytes toSignalPqxdhPrimitives
  dsimp only
  rcases h : P.montToEd u s with _ | edPt
  · rfl
  · simp [LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.packEdBytes_unpackEdBytes
      (hmontLen u s edPt h)]

theorem toSignalPqxdhPrimitives_dalekMontToEdOutAt_eq (P : Primitives)
    (hmontLen : ∀ u s pt, P.montToEd u s = some pt → pt.length = 160)
    (outPtr : BitVec 64) (inBytes : Bytes) (signBit : UInt8) :
    CryptoVerification.E2E.Pqxdh.Shared.dalekMontToEdOutAt
      (toSignalPqxdhPrimitives P) outPtr inBytes signBit =
      dalekMontToEdOutAt P outPtr inBytes signBit := by
  unfold CryptoVerification.E2E.Pqxdh.Shared.dalekMontToEdOutAt dalekMontToEdOutAt
  rw [toSignalPqxdhPrimitives_montToEdBytes_eq P hmontLen]
  rfl

theorem toSignalPqxdhPrimitives_isTorsionFreeBytes_eq (P : Primitives)
    (bs : Bytes) (hbs : bs.length = 160) :
    (toSignalPqxdhPrimitives P).isTorsionFreeBytes bs = P.isTorsionFree bs := by
  unfold _root_.SignalPqxdh.Primitives.isTorsionFreeBytes toSignalPqxdhPrimitives
  dsimp only
  rw [LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.packEdBytes_unpackEdBytes hbs]

theorem toSignalPqxdhPrimitives_montToEd_lt (P : Primitives)
    (u : Bytes) (s : UInt8) (pt : VerifiedLibraries.Common.EdPoint)
    (h : (toSignalPqxdhPrimitives P).montToEd u s = some pt) :
    pt.x < 256 ^ 80 ∧ pt.y < 256 ^ 80 := by
  rcases Option.map_eq_some_iff.mp h with ⟨edPt, _, rfl⟩
  exact LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.unpackEdBytes_coords_lt edPt

theorem toSignalPqxdhPrimitives_isCanonicalRef_eq (P : Primitives)
    (hmontLen : ∀ u s pt, P.montToEd u s = some pt → pt.length = 160)
    (pk : Bytes) :
    SignalPqxdh.isCanonicalRef (toSignalPqxdhPrimitives P) pk = isCanonicalRef P pk := by
  unfold SignalPqxdh.isCanonicalRef isCanonicalRef toSignalPqxdhPrimitives
  dsimp only
  rw [show SignalPqxdh.scalarIsInRange pk = scalarIsInRange pk from rfl]
  split
  · rcases hm : P.montToEd pk 0 with _ | edPt
    · rfl
    · simp [LibsignalBinary.Proofs.SpecLemmas.SignalSession.PqxdhHooksLegacy.packEdBytes_unpackEdBytes
        (hmontLen pk 0 edPt hm)]
  · rfl

@[expose] def incomingWord0 : BitVec 64 := 0x676e696d6f636e69#64 -- "incoming"
@[expose] def incomingWord1 : BitVec 64 := 0x656b206573616220#64 -- " base ke"
@[expose] def incomingWord2 : BitVec 64 := 0x73692079656b2065#64 -- "e key is" (bytes 12..20)
@[expose] def incomingWord3 : BitVec 64 := 0x64696c61766e6920#64 -- " invalid" (bytes 20..28)
theorem incomingBaseKeyInvalidBytes_split1_eq : incomingBaseKeyInvalidBytes =
      unpack64 incomingWord0 ++ (unpack64 incomingWord1 ++ incomingBaseKeyInvalidBytes.drop 16) :=
        by decide +kernel
theorem incomingBaseKeyInvalidBytes_split2_eq : incomingBaseKeyInvalidBytes =
      incomingBaseKeyInvalidBytes.take 12 ++ (unpack64 incomingWord2 ++ unpack64 incomingWord3) :=
        by decide +kernel
theorem rodata_incoming_split1 (a : BitVec 64) : (a ↦ᵣ incomingBaseKeyInvalidBytes) =
      ((a ↦₆₄ᵣ incomingWord0) ∗ ((a + 8#64) ↦₆₄ᵣ incomingWord1) ∗ ((a +
        16#64) ↦ᵣ (incomingBaseKeyInvalidBytes.drop 16))) := by
  rw [incomingBaseKeyInvalidBytes_split1_eq, pointsToBytesRO_append, ←
    pointsTo64RO_eq_pointsToBytesRO, unpack64_length, pointsToBytesRO_append, ←
    pointsTo64RO_eq_pointsToBytesRO, unpack64_length, show a + BitVec.ofNat 64 8 +
      BitVec.ofNat 64 8 = a + 16#64 by bv_omega]; ac_rfl
theorem rodata_incoming_split2 (a : BitVec 64) : (a ↦ᵣ incomingBaseKeyInvalidBytes) =
      ((a ↦ᵣ incomingBaseKeyInvalidBytes.take 12) ∗ ((a + 12#64) ↦₆₄ᵣ incomingWord2) ∗ ((a +
        20#64) ↦₆₄ᵣ incomingWord3)) := by
  rw [incomingBaseKeyInvalidBytes_split2_eq, pointsToBytesRO_append, pointsToBytesRO_append, ←
    pointsTo64RO_eq_pointsToBytesRO, ← pointsTo64RO_eq_pointsToBytesRO,
      show (incomingBaseKeyInvalidBytes.take 12).length = 12 by decide, unpack64_length, show a +
        BitVec.ofNat 64 12 = a + 12#64 by bv_omega, show a + 12#64 + BitVec.ofNat 64 8 = a +
        20#64 by bv_omega]; ac_rfl
theorem rodata_incoming_1_to_2 (a : BitVec 64) : (a ↦₆₄ᵣ incomingWord0) ∗ ((a +
    8#64) ↦₆₄ᵣ incomingWord1) ∗ ((a + 16#64) ↦ᵣ (incomingBaseKeyInvalidBytes.drop 16)) =
    (a ↦ᵣ incomingBaseKeyInvalidBytes.take 12) ∗ ((a + 12#64) ↦₆₄ᵣ incomingWord2) ∗ ((a +
      20#64) ↦₆₄ᵣ incomingWord3) := by rw [← rodata_incoming_split1, rodata_incoming_split2]
theorem incoming_alloc_split (p : BitVec 64) : memRegion p 28 = (∃∗ u0 : BitVec 64, p ↦₆₄ u0) ∗ (∃∗
      u1 : BitVec 64, (p + 8#64) ↦₆₄ u1) ∗ memRegion (p + 16#64) 12 := by
  rw [show (28 : Nat) = 8 + (8 + 12) by decide, memRegion_split p 8 20 (by decide),
    memRegion_split (p + 8#64) 8 12 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem incoming_overlap_prep (p w0 w1 : BitVec 64) : (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗
    memRegion (p + 16#64) 12 ⊢ memRegion p 12 ∗ (∃∗ u2 : BitVec 64, (p + 12#64) ↦₆₄ u2) ∗ (∃∗
      u3 : BitVec 64, (p + 20#64) ↦₆₄ u3) := by
  have hm0 : (p ↦₆₄ w0) ⊢ memRegion p 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right w0 (Entails.refl _)
  have hm1 : ((p + 8#64) ↦₆₄ w1) ⊢ memRegion (p + 8#64) 8 := by
    rw [ProofLib.memRegion_eight]; exact Entails.sepExists_right w1 (Entails.refl _)
  refine Entails.trans (sepConj_mono hm0 (sepConj_mono_left hm1)) ?_
  have heq : memRegion p 8 ∗ (memRegion (p + 8#64) 8 ∗ memRegion (p + 16#64) 12) =
      memRegion p 12 ∗ (∃∗ u2 : BitVec 64, (p + 12#64) ↦₆₄ u2) ∗ (∃∗ u3 : BitVec 64, (p +
        20#64) ↦₆₄ u3) := by
    rw [show p + 16#64 = p + 8#64 + BitVec.ofNat 64 8 by bv_omega, ←
      memRegion_split (p + 8#64) 8 12 (by decide), show p + 8#64 = p + BitVec.ofNat 64 8
      by bv_omega, ← memRegion_split p 8 20 (by decide), show (8 + 20 : Nat) = 12 + (8 +
        8) by decide, memRegion_split p 12 16 (by decide), memRegion_split (p +
        BitVec.ofNat 64 12) 8 8 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq heq
theorem uint8_ofNat_shift_mod_toBitVec (w : BitVec 64) (s : Nat) :
    BitVec.ofNat 8 (UInt8.ofNat ((w.toNat >>> s) % 256)).toNat = w.extractLsb' s 8 := by
  apply BitVec.eq_of_toNat_eq; simp [UInt8.ofNat, BitVec.toNat_ofNat, BitVec.extractLsb']
theorem bytesToBv8_encodeU64LE (w : BitVec 64) : bytesToBv8 (encodeU64LE w) = unpack64 w := by
  simp only [encodeU64LE, bytesToBv8, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    Nat.mul_zero, Nat.mul_succ, List.map_cons, List.map_nil, uint8_ofNat_shift_mod_toBitVec,
    unpack64]
theorem pointsToBytes_encodeU64LE (a w : BitVec 64) :
    (a ↦ₛ bytesToBv8 (encodeU64LE w)) = (a ↦₆₄ w) := by
  rw [bytesToBv8_encodeU64LE, ← pointsTo64_eq_pointsToBytes]
theorem bytesToBv8_head_tail (a : BitVec 64) (bs : List (BitVec 8)) (h : 1 ≤ bs.length) :
    (a ↦ₛ bs) = (a ↦₈ bs.getD 0 0#8) ∗ ((a + 1#64) ↦ₛ bs.drop 1) := by
  rcases bs with _ | ⟨b0, tail⟩
  · simp at h
  · simp [pointsToBytes_cons]
theorem opkBSk_getD_length {inp : AcceptKeysInput} (h : WellSizedAcceptKeysInput inp) :
    (inp.opkBSk?.getD (List.replicate 32 0)).length = 32 := by
  rcases h with ⟨_, _, _, _, hopk, _, _, _, _, _⟩
  cases hopk_eq : inp.opkBSk? with
  | none => simp | some sk => exact hopk sk hopk_eq
theorem bytesToBv8_fitBytes_length (n : Nat) (bs : Bytes) :
    (bytesToBv8 (fitBytes n bs)).length = n := by simp [bytesToBv8]
theorem bytesToBv8_encodeU64LE_length (w : BitVec 64) :
    (bytesToBv8 (encodeU64LE w)).length = 8 := by rw [bytesToBv8_encodeU64LE, unpack64_length]
theorem pointsToBytes_split_at (a : BitVec 64) (xs ys : Bytes) (n : Nat) (h : (bytesToBv8 xs).length
    = n) : (a ↦ₛ bytesToBv8 (xs ++ ys)) =
      (a ↦ₛ bytesToBv8 xs) ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bytesToBv8 ys) := by
  rw [bytesToBv8_append, pointsToBytes_append, h]
theorem outPtr_err104_split (outPtr : BitVec 64) : memRegion outPtr 104 = (∃∗ v0 : BitVec 32,
      outPtr ↦₃₂ v0) ∗ memRegion (outPtr + 4#64) 4 ∗ (∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗
        w3 : BitVec 64, ∃∗ w4 : BitVec 64, ((outPtr + 8#64) ↦₆₄ w1) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
        ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4)) ∗ (∃∗
        b40 : BitVec 8, (outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 := by
  rw [show (104 : Nat) = 4 + (4 + (32 + (1 + 63))) by decide, memRegion_split outPtr 4 100
    (by decide), memRegion_split (outPtr + 4#64) 4 96 (by decide), memRegion_split (outPtr + 4#64 +
    4#64) 32 64 (by decide), memRegion_split (outPtr + 4#64 + 4#64 + 32#64) 1 63 (by decide),
      memRegion_four outPtr, (memRegion_cells (outPtr + 4#64 + 4#64) 4 (by decide) :
        memRegion (outPtr + 4#64 + 4#64) 32 = cells (outPtr + 4#64 + 4#64) 4),
        memRegion_one (outPtr + 4#64 + 4#64 + 32#64)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
theorem pointsTo32_one_entails_tag_ne_zero (a : BitVec 64) : (a ↦₃₂ 1#32) ⊢
      (∃∗ tag : BitVec 8, ⌜tag ≠ 0#8⌝ ∗ (a ↦₈ tag)) ∗ memRegion (a + 1#64) 3 := by
  rw [pointsTo32_eq_pointsToBytes]; have hu : unpack32 1#32 = [1#8, 0#8, 0#8, 0#8] := rfl
  rw [hu, pointsToBytes_cons]
  have htag : (a ↦₈ 1#8) ⊢ ∃∗ tag : BitVec 8, ⌜tag ≠ 0#8⌝ ∗ (a ↦₈ tag) := by
    have hne : (1#8 : BitVec 8) ≠ 0#8 := (by decide); rw [← pure_sepConj_of_true hne (a ↦₈ 1#8)]
    exact Entails.sepExists_right 1#8 (Entails.refl _)
  exact sepConj_mono htag (pointsToBytes_entails_memRegion (a + 1#64) [0#8, 0#8, 0#8])
theorem outPtr_err104_merge (outPtr w1 w2 w3 w4 : BitVec 64) (b40 : BitVec 8) : (outPtr ↦₃₂ 1#32) ∗
    memRegion (outPtr + 4#64) 4 ∗ ((outPtr + 8#64) ↦₆₄ w1) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr +
      24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗ ((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr +
      41#64) 63 ⊢
      (∃∗ tag : BitVec 8, ⌜tag ≠ 0#8⌝ ∗ (outPtr ↦₈ tag)) ∗ memRegion (outPtr + 1#64) 103 := by
  have hc4 := cells_4_merge (outPtr + 8#64) w1 w2 w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hc4
  rw [← (memRegion_cells (outPtr + 8#64) 4 (by decide) : memRegion (outPtr + 8#64) 32 =
    cells (outPtr + 8#64) 4)] at hc4
  have hb40 : ((outPtr + 40#64) ↦₈ b40) ⊢ memRegion (outPtr + 40#64) 1 := by
    rw [memRegion_one]; exact Entails.sepExists_right b40 (Entails.refl _)
  have h1 := pointsTo32_one_entails_tag_ne_zero outPtr
  have hm103 : memRegion (outPtr + 1#64) 3 ∗ (memRegion (outPtr + 4#64) 4 ∗ (memRegion (outPtr +
    8#64) 32 ∗ (memRegion (outPtr + 40#64) 1 ∗ memRegion (outPtr + 41#64) 63))) =
      memRegion (outPtr + 1#64) 103 := by
    rw [show outPtr + 41#64 = outPtr + 40#64 + BitVec.ofNat 64 1 by bv_omega, ←
      memRegion_split (outPtr + 40#64) 1 63 (by decide), show outPtr + 40#64 = outPtr + 8#64 +
      BitVec.ofNat 64 32 by bv_omega, ← memRegion_split (outPtr + 8#64) 32 64 (by decide),
        show outPtr + 8#64 = outPtr + 4#64 + BitVec.ofNat 64 4 by bv_omega, ←
        memRegion_split (outPtr + 4#64) 4 96 (by decide),
        show outPtr + 4#64 = outPtr + 1#64 + BitVec.ofNat 64 3 by bv_omega, ←
          memRegion_split (outPtr + 1#64) 3 100 (by decide)]
  rw [← hm103]; refine Entails.trans (sepConj_mono_left h1) ?_; rw [sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  have hswap : ((outPtr + 8#64) ↦₆₄ w1) ∗ (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗
    (((outPtr + 32#64) ↦₆₄ w4) ∗ (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63)))) =
      (((outPtr + 8#64) ↦₆₄ w1) ∗ (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗
        ((outPtr + 32#64) ↦₆₄ w4)))) ∗ (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr +
        41#64) 63) := by ac_rfl
  rw [hswap]; exact sepConj_mono hc4 (sepConj_mono_left hb40)
theorem outPtr_ok104_split (outPtr : BitVec 64) : memRegion outPtr 104 = (∃∗ v0 : BitVec 32,
      outPtr ↦₃₂ v0) ∗ cells (outPtr + 4#64) 12 ∗ (∃∗ v100 : BitVec 32,
        (outPtr + 100#64) ↦₃₂ v100) := by
  rw [show (104 : Nat) = 4 + 100 by decide, memRegion_split outPtr 4 100 (by decide),
    memRegion_four outPtr, memRegion_out_derive (outPtr + 4#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem outPtr_ok104_eq (outPtr : BitVec 64) (dk : DRKey) : (outPtr ↦₃₂ 0#32) ∗ ((outPtr +
    4#64) ↦ₛ bytesToBv8 (handshakeKeysBytes100 dk)) =
      (outPtr ↦ₛ bytesToBv8 (handshakeKeysResultOk104 dk)) := by
  unfold handshakeKeysResultOk104
  rw [bytesToBv8_append, pointsToBytes_append, pointsTo32_eq_pointsToBytes]; rfl
theorem sp_sub4912_orr_one {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 4912#64) ||| 1#64 = sp - 4911#64 := by revert h; bv_bits
theorem sp_sub1744_orr_one {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    (sp - 1744#64) ||| 1#64 = sp - 1743#64 := by revert h; bv_bits
theorem subStack_to_alloc (sp : BitVec 64) : stackAt (sp - 4944#64) (pqxdhHookStack + 400) =
      memRegion (sp - 9440#64) 400 ∗ stackAt (sp - 4944#64) allocHookStack := by
  simp only [stackAt, pqxdhHookStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - 4944#64 - BitVec.ofNat 64 4496) (n := 400) (k := 4096)
    (b' := sp - 4944#64 - BitVec.ofNat 64 4096) rfl (by bv_omega) (by decide)]
  have h1 : sp - 4944#64 - BitVec.ofNat 64 4496 = sp - 9440#64 := (by bv_omega); rw [h1]
theorem subStack_to_calc (sp : BitVec 64) : stackAt (sp - 4944#64) (pqxdhHookStack + 400) =
      memRegion (sp - 9440#64) 240 ∗ stackAt (sp - 4944#64) calculateAgreementStack := by
  simp only [stackAt, pqxdhHookStack, calculateAgreementStack, allocHookStack]
  rw [ProofLib.memRegion_split' (b := sp - 4944#64 - BitVec.ofNat 64 4496) (n := 240) (k := 4256)
    (b' := sp - 4944#64 - BitVec.ofNat 64 4256) rfl (by bv_omega) (by decide)]
  have h1 : sp - 4944#64 - BitVec.ofNat 64 4496 = sp - 9440#64 := (by bv_omega); rw [h1]
theorem subStack_to_vecAppend (sp : BitVec 64) : stackAt (sp - 4944#64) (pqxdhHookStack + 400) =
      memRegion (sp - 9440#64) 4448 ∗ cells (sp - 4992#64) 6 := by
  simp only [stackAt, pqxdhHookStack]
  rw [ProofLib.memRegion_split' (b := sp - 4944#64 - BitVec.ofNat 64 4496) (n := 4448) (k := 48)
    (b' := sp - 4992#64) rfl (by bv_omega) (by decide), (memRegion_cells (sp - 4992#64) 6
      (by decide) : memRegion (sp - 4992#64) 48 = cells (sp - 4992#64) 6)]
  have h1 : sp - 4944#64 - BitVec.ofNat 64 4496 = sp - 9440#64 := (by bv_omega); rw [h1]
theorem stackAt_pqxdh_accept_top (sp : BitVec 64) : stackAt sp pqxdhEntryStack = memRegion (sp -
      16384#64) 6944 ∗ stackAt (sp - 4944#64) (pqxdhHookStack + 400) ∗ cells (sp - 4944#64) 4 ∗
        memRegion (sp - 4912#64) 3168 ∗ memRegion (sp - 1744#64) 1568 ∗ memRegion (sp -
        176#64) 96 ∗ cells (sp - 80#64) 10 := by
  simp only [stackAt, pqxdhEntryStack, pqxdhHookStack]
  rw [ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 16384) (n := 6944) (k := 9440) (b' :=
        sp - 9440#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 9440#64) (n := 4496) (k := 4944) (b' :=
        sp - 4944#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 4944#64) (n := 32) (k := 4912) (b' :=
        sp - 4912#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 4912#64) (n := 3168) (k := 1744) (b' :=
        sp - 1744#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 1744#64) (n := 1568) (k := 176) (b' :=
        sp - 176#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 176#64) (n := 96) (k := 80) (b' :=
        sp - 80#64) rfl (by bv_omega) (by decide), (memRegion_cells (sp - 4944#64) 4 (by decide) :
        memRegion (sp - 4944#64) 32 = cells (sp - 4944#64) 4), (memRegion_cells (sp - 80#64) 10
        (by decide) : memRegion (sp - 80#64) 80 = cells (sp - 80#64) 10)]
  have h1 : sp - 4944#64 - BitVec.ofNat 64 4496 = sp - 9440#64 := by bv_omega
  have h2 : sp - BitVec.ofNat 64 16384 = sp - 16384#64 := rfl; rw [h1, h2]
theorem pqsk_region_phaseA_split (sp : BitVec 64) : memRegion (sp - 4912#64) 3168 = memRegion (sp -
      4912#64) 24 ∗ memRegion (sp - 4888#64) 712 ∗ (∃∗ v_probe : BitVec 64, (sp -
        4176#64) ↦₆₄ v_probe) ∗ memRegion (sp - 4168#64) 2424 := by
  rw [ProofLib.memRegion_split' (b := sp - 4912#64) (n := 24) (k := 3144) (b' :=
        sp - 4888#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 4888#64) (n := 712) (k := 2432) (b' :=
        sp - 4176#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 4176#64) (n := 8) (k := 2424) (b' :=
        sp - 4168#64) rfl (by bv_omega) (by decide), memRegion_eight (sp - 4176#64)]
theorem pqsk_region_phaseA_merge (sp v_probe : BitVec 64) : memRegion (sp - 4912#64) 24 ∗
    memRegion (sp - 4888#64) 712 ∗ ((sp - 4176#64) ↦₆₄ v_probe) ∗ memRegion (sp - 4168#64) 2424 ⊢
      memRegion (sp - 4912#64) 3168 := by
  rw [pqsk_region_phaseA_split sp]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_left ?_))
  exact Entails.sepExists_right v_probe (Entails.refl _)
theorem pqsk_region_phaseA_cells_merge (sp w0 w1 w2 v_probe : BitVec 64) : ((sp - 4912#64) ↦₆₄ w0) ∗
    ((sp - 4904#64) ↦₆₄ w1) ∗ ((sp - 4896#64) ↦₆₄ w2) ∗ memRegion (sp - 4888#64) 712 ∗ ((sp -
      4176#64) ↦₆₄ v_probe) ∗ memRegion (sp - 4168#64) 2424 ⊢ memRegion (sp - 4912#64) 3168 := by
  have hc3 := cells_3_merge (sp - 4912#64) w0 w1 w2
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hc3
  rw [← (memRegion_cells (sp - 4912#64) 3 (by decide) : memRegion (sp - 4912#64) 24 = cells (sp -
    4912#64) 3)] at hc3; refine Entails.trans ?_ (pqsk_region_phaseA_merge sp v_probe)
  have hassoc : ((sp - 4912#64) ↦₆₄ w0) ∗ (((sp - 4904#64) ↦₆₄ w1) ∗ (((sp - 4896#64) ↦₆₄ w2) ∗
    (memRegion (sp - 4888#64) 712 ∗ (((sp - 4176#64) ↦₆₄ v_probe) ∗ memRegion (sp -
    4168#64) 2424)))) =
      (((sp - 4912#64) ↦₆₄ w0) ∗ (((sp - 4904#64) ↦₆₄ w1) ∗ ((sp - 4896#64) ↦₆₄ w2))) ∗
        (memRegion (sp - 4888#64) 712 ∗ (((sp - 4176#64) ↦₆₄ v_probe) ∗ memRegion (sp -
        4168#64) 2424)) := by ac_rfl
  rw [hassoc]; exact sepConj_mono_left hc3
theorem pqsk_region_phaseB_split (sp : BitVec 64) : memRegion (sp - 4912#64) 3168 =
      (∃∗ b0 : BitVec 8, (sp - 4912#64) ↦₈ b0) ∗ memRegion (sp - 4911#64) 3167 := by
  rw [ProofLib.memRegion_split' (b := sp - 4912#64) (n := 1) (k := 3167) (b' :=
        sp - 4911#64) rfl (by bv_omega) (by decide), memRegion_one (sp - 4912#64)]
theorem kemct_region_phaseB_split (sp : BitVec 64) : memRegion (sp - 1744#64) 1568 =
      (∃∗ b0 : BitVec 8, (sp - 1744#64) ↦₈ b0) ∗ memRegion (sp - 1743#64) 1567 := by
  rw [ProofLib.memRegion_split' (b := sp - 1744#64) (n := 1) (k := 1567) (b' :=
        sp - 1743#64) rfl (by bv_omega) (by decide), memRegion_one (sp - 1744#64)]
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
theorem pointsTo64_4_allOnes_eq_F_X25519 (a : BitVec 64) : (a ↦₆₄ 0xffffffffffffffff#64) ∗ ((a +
    8#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((a + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((a +
      24#64) ↦₆₄ 0xffffffffffffffff#64) = (a ↦ₛ bytesToBv8 F_X25519) := by
  have hf : bytesToBv8 F_X25519 =
      unpack64 0xffffffffffffffff#64 ++ (unpack64 0xffffffffffffffff#64 ++
        (unpack64 0xffffffffffffffff#64 ++ unpack64 0xffffffffffffffff#64)) := by decide +kernel
  rw [hf, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, unpack64_length, ←
    pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes]; simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem cells4_eq (a : BitVec 64) : cells a 4 = ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗
      u2 : BitVec 64, ∃∗ u3 : BitVec 64, (a ↦₆₄ u0) ∗ ((a +
        8#64) ↦₆₄ u1) ∗ ((a + 16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3) := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
theorem memRegion_192_init_split (a : BitVec 64) : memRegion a 192 = (∃∗ u0 : BitVec 64, ∃∗
      u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, (a ↦₆₄ u0) ∗ ((a + 8#64) ↦₆₄ u1) ∗ ((a +
        16#64) ↦₆₄ u2) ∗ ((a + 24#64) ↦₆₄ u3)) ∗ memRegion (a + 32#64) 32 ∗ memRegion (a +
        64#64) 32 ∗ memRegion (a + 96#64) 32 ∗ memRegion (a +
        128#64) 32 ∗ memRegion (a + 160#64) 32 := by
  rw [show (192 : Nat) = 32 + (32 + (32 + (32 + (32 + 32)))) by decide, memRegion_split a 32 160
    (by decide), memRegion_split (a + 32#64) 32 128 (by decide), memRegion_split (a + 32#64 +
    32#64) 32 96 (by decide), memRegion_split (a + 32#64 + 32#64 + 32#64) 32 64 (by decide),
      memRegion_split (a + 32#64 + 32#64 + 32#64 + 32#64) 32 32 (by decide), (memRegion_cells a 4
        (by decide) : memRegion a 32 = cells a 4), cells4_eq a]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem pointsToBytes_append_at (a : BitVec 64) (xs ys : Bytes) (n : Nat) (h : (bytesToBv8
    xs).length = n) : (a ↦ₛ bytesToBv8 xs) ∗ ((a + BitVec.ofNat 64 n) ↦ₛ bytesToBv8 ys) =
      (a ↦ₛ bytesToBv8 (xs ++ ys)) := (pointsToBytes_split_at a xs ys n h).symm
theorem hmacState_merge_sub1744 (P : Primitives) (sp : BitVec 64) (prk : Bytes) {w0 w1 w2 w3 w4 w5
    w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 : BitVec 64} (hhmac : PqxdhHmacGood P prk w0 w1 w2
    w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17) : (((sp - 1744#64) ↦₆₄ w0) ∗ ((sp -
    1736#64) ↦₆₄ w1) ∗ ((sp - 1728#64) ↦₆₄ w2) ∗ ((sp - 1720#64) ↦₆₄ w3) ∗ ((sp - 1712#64) ↦₆₄ w4) ∗
      ((sp - 1704#64) ↦₆₄ w5) ∗ ((sp - 1696#64) ↦₆₄ w6) ∗ ((sp - 1688#64) ↦₆₄ w7) ∗ ((sp -
      1680#64) ↦₆₄ w8) ∗ ((sp - 1672#64) ↦₆₄ w9) ∗ ((sp - 1664#64) ↦₆₄ w10) ∗ ((sp -
      1656#64) ↦₆₄ w11) ∗ ((sp - 1648#64) ↦₆₄ w12) ∗ ((sp - 1640#64) ↦₆₄ w13) ∗ ((sp -
      1632#64) ↦₆₄ w14) ∗ ((sp - 1624#64) ↦₆₄ w15) ∗ ((sp - 1616#64) ↦₆₄ w16) ∗ ((sp -
        1608#64) ↦₆₄ w17)) ⊢ pqxdhHmacStateAt P (sp - 1744#64) prk := by
  have hmrg := hmacCore_merge P (sp - 1744#64) prk hhmac
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hmrg; exact hmrg
theorem acceptKeys_eq_none_of_not_canonical (P : Primitives) (inp : AcceptKeysInput) (htrust :
    inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = false) :
    Model.acceptKeys P inp = none := by
  simp only [Model.acceptKeys, htrust, hreplay, hik, hek, hcanon, beq_self_eq_true,
    Bool.false_eq_true, «guard», bind, pure, ↓reduceIte]; rfl
theorem acceptKeys_eq_none_of_dh1_zero (P : Primitives) (inp : AcceptKeysInput) (htrust :
    inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = true)
    (hdh1 : P.x25519 inp.spkBSk inp.hdr.ikAPk = List.replicate 32 0) :
    Model.acceptKeys P inp = none := by
  simp only [Model.acceptKeys, htrust, hreplay, hik, hek, hcanon, hdh1, beq_self_eq_true,
    bne_self_eq_false, Bool.false_eq_true, «guard», bind, pure, ↓reduceIte]; rfl
theorem acceptKeys_eq_none_of_dh2_zero (P : Primitives) (inp : AcceptKeysInput) (htrust :
    inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = true)
    (hdh1 : P.x25519 inp.spkBSk inp.hdr.ikAPk ≠ List.replicate 32 0)
    (hdh2 : P.x25519 inp.ikBSk inp.hdr.ekAPk = List.replicate 32 0) :
    Model.acceptKeys P inp = none := by
  have hdh1_bne : (P.x25519 inp.spkBSk inp.hdr.ikAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh1
  simp only [Model.acceptKeys, htrust, hreplay, hik, hek, hcanon, hdh1_bne, hdh2, beq_self_eq_true,
    bne_self_eq_false, Bool.false_eq_true, «guard», bind, pure, ↓reduceIte]; rfl
theorem acceptKeys_eq_some_of_opk_none (P : Primitives) (inp : AcceptKeysInput) (ss : Bytes)
    (htrust : inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = true)
    (hdh1 : P.x25519 inp.spkBSk inp.hdr.ikAPk ≠ List.replicate 32 0)
    (hdh2 : P.x25519 inp.ikBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hdh3 : P.x25519 inp.spkBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hopk_eq : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome) (hopk : inp.opkBSk? = none)
    (hkem : P.kemDecaps inp.pqspkBSk inp.hdr.kemCt = some ss) : Model.acceptKeys P inp =
      some (Model.deriveDRKeys P (buildSecrets (P.x25519 inp.spkBSk inp.hdr.ikAPk) (P.x25519
        inp.ikBSk inp.hdr.ekAPk) (P.x25519 inp.spkBSk inp.hdr.ekAPk) none ss)) := by
  have hopkId : inp.hdr.opkId? = none := by cases h : inp.hdr.opkId? <;> simp_all
  have hdh1_bne : (P.x25519 inp.spkBSk inp.hdr.ikAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh1
  have hdh2_bne : (P.x25519 inp.ikBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh2
  have hdh3_bne : (P.x25519 inp.spkBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh3
  simp only [Model.acceptKeys, Model.deriveDRKeys, dhOptNonZero, htrust, hreplay, hik, hek, hcanon,
    hdh1_bne, hdh2_bne, hdh3_bne, hopk, hopkId, hkem, beq_self_eq_true, «guard», bind, pure,
    ↓reduceIte]; rfl
theorem acceptKeys_eq_some_of_opk_some (P : Primitives) (inp : AcceptKeysInput) (opkSk ss : Bytes)
    (htrust : inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = true)
    (hdh1 : P.x25519 inp.spkBSk inp.hdr.ikAPk ≠ List.replicate 32 0)
    (hdh2 : P.x25519 inp.ikBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hdh3 : P.x25519 inp.spkBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hopk_eq : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome) (hopk : inp.opkBSk? = some opkSk)
    (hdh4 : P.x25519 opkSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hkem : P.kemDecaps inp.pqspkBSk inp.hdr.kemCt = some ss) : Model.acceptKeys P inp =
      some (Model.deriveDRKeys P (buildSecrets (P.x25519 inp.spkBSk inp.hdr.ikAPk) (P.x25519
        inp.ikBSk inp.hdr.ekAPk) (P.x25519 inp.spkBSk inp.hdr.ekAPk)
        (some (P.x25519 opkSk inp.hdr.ekAPk)) ss)) := by
  obtain ⟨opkId, hopkId⟩ : ∃ id, inp.hdr.opkId? = some id := by
    cases h : inp.hdr.opkId? with
    | none => simp [h, hopk] at hopk_eq | some id => exact ⟨id, rfl⟩
  have hdh1_bne : (P.x25519 inp.spkBSk inp.hdr.ikAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh1
  have hdh2_bne : (P.x25519 inp.ikBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh2
  have hdh3_bne : (P.x25519 inp.spkBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh3
  have hdh4_bne : (P.x25519 opkSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh4
  simp only [Model.acceptKeys, Model.deriveDRKeys, dhOptNonZero, htrust, hreplay, hik, hek, hcanon,
    hdh1_bne, hdh2_bne, hdh3_bne, hopk, hopkId, hkem, beq_self_eq_true, «guard», bind, pure,
    ↓reduceIte]
  change (if (P.x25519 opkSk inp.hdr.ekAPk != List.replicate 32 0) =
    true then some () else failure).bind _ = _
  rw [hdh4_bne]; rfl
theorem err28_anyHeap_intro (A : RustAlloc) (ptr w2 w3 : BitVec 64) : memRegion ptr 12 ∗ ((ptr +
    12#64) ↦₆₄ w2) ∗ ((ptr + 20#64) ↦₆₄ w3) ∗ A.live ptr 28 1 ⊢ anyHeap := ent_anyHeap _
theorem emp_entails_anyHeap : emp ⊢ anyHeap := ent_anyHeap emp
theorem cells_sub4944_4_merge (sp v0 v1 v2 v3 : BitVec 64) : ((sp - 4944#64) ↦₆₄ v0) ∗ ((sp -
    4936#64) ↦₆₄ v1) ∗ ((sp - 4928#64) ↦₆₄ v2) ∗ ((sp - 4920#64) ↦₆₄ v3) ⊢
      cells (sp - 4944#64) 4 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using cells_4_merge (sp - 4944#64) v0 v1 v2 v3
theorem cells_sub80_10_merge (sp c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) : ((sp -
    80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗ ((sp - 56#64) ↦₆₄ c3) ∗
      ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗ ((sp - 32#64) ↦₆₄ c6) ∗ ((sp -
      24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗ ((sp - 8#64) ↦₆₄ c9) ⊢ cells (sp - 80#64) 10 := by
  simpa only [bv_sub_add_lit', BitVec.reduceSub] using cells_10_merge (sp -
    80#64) c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
theorem SepWP.pure_left_elim {prog : Program} {target : BitVec 64} {s : State} {φ : Prop} {P Q :
    SepProp} {post : State → SepProp → Prop} (h : φ → SepWP prog target s (P ∗ Q) post) :
    SepWP prog target s ((⌜φ⌝ ∗ P) ∗ Q) post := by rw [sepConj_assoc]; exact SepWP.pure_elim h
theorem SepWP.exists_left_elim {α : Type} {prog : Program} {target : BitVec 64} {s : State} {P : α →
    SepProp} {Q : SepProp} {post : State → SepProp → Prop} (h : ∀ x, SepWP prog target s (P x ∗
    Q) post) : SepWP prog target s ((∃∗ x, P x) ∗ Q) post := by
  rw [sepExists_sepConj_left]; exact SepWP.exists_elim h
theorem SepWPp.exists_left_elim {α : Type} {prog : Program} {ret : BitVec 64} {s : State} {P : α →
    SepProp} {Q : SepProp} {Qok Qp : State → SepProp → Prop} (h : ∀ x, SepWPp prog ret s (P x ∗
    Q) Qok Qp) : SepWPp prog ret s ((∃∗ x, P x) ∗ Q) Qok Qp := by
  rw [sepExists_sepConj_left]; exact SepWPp.exists_elim h
macro "sep_elim_exists'" : tactic =>
  `(tactic| (
    try (conv => arg 4; arg 1; simp only [sepExists_sepConj_left, sepExists_sepConj_right])
    repeat' (first
      | (with_reducible apply SepWPp.exists_left_elim; intro _)
      | (with_reducible apply SepWP.exists_left_elim; intro _)
      | (with_reducible apply SepWPp.exists_elim; intro _)
      | (with_reducible apply SepWP.exists_elim; intro _))))
theorem cells10_sub80_eq (sp : BitVec 64) : cells (sp - 80#64) 10 = ∃∗ c0 : BitVec 64, ∃∗
      c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗
        c6 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ((sp -
        80#64) ↦₆₄ c0) ∗ ((sp - 72#64) ↦₆₄ c1) ∗ ((sp - 64#64) ↦₆₄ c2) ∗ ((sp - 56#64) ↦₆₄ c3) ∗
        ((sp - 48#64) ↦₆₄ c4) ∗ ((sp - 40#64) ↦₆₄ c5) ∗ ((sp - 32#64) ↦₆₄ c6) ∗ ((sp -
        24#64) ↦₆₄ c7) ∗ ((sp - 16#64) ↦₆₄ c8) ∗ ((sp - 8#64) ↦₆₄ c9) := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
theorem cells4_sub4944_eq (sp : BitVec 64) : cells (sp - 4944#64) 4 = ∃∗ v0 : BitVec 64, ∃∗
      v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64, ((sp - 4944#64) ↦₆₄ v0) ∗ ((sp -
        4936#64) ↦₆₄ v1) ∗ ((sp - 4928#64) ↦₆₄ v2) ∗ ((sp - 4920#64) ↦₆₄ v3) := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
theorem spAligned_sub_4944 {sp sp' : BitVec 64} (halign : (sp &&& 15#64 == 0#64) = true)
    (hsp : sp' = sp - 4944#64) : (sp' &&& 15#64 == 0#64) = true := by
  subst hsp; revert halign; bv_bits
theorem allocFailedIn_of_trace_eq {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  rcases h with ⟨ha, hp⟩; unfold allocFailedIn at ha ⊢; rw [← htr]; exact ⟨ha, hp⟩
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
theorem acceptKeys_eq_none_of_dh3_zero (P : Primitives) (inp : AcceptKeysInput) (htrust :
    inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = true)
    (hdh1 : P.x25519 inp.spkBSk inp.hdr.ikAPk ≠ List.replicate 32 0)
    (hdh2 : P.x25519 inp.ikBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hdh3 : P.x25519 inp.spkBSk inp.hdr.ekAPk = List.replicate 32 0) :
    Model.acceptKeys P inp = none := by
  have hdh1_bne : (P.x25519 inp.spkBSk inp.hdr.ikAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh1
  have hdh2_bne : (P.x25519 inp.ikBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh2
  simp only [Model.acceptKeys, htrust, hreplay, hik, hek, hcanon, hdh1_bne, hdh2_bne, hdh3,
    beq_self_eq_true, bne_self_eq_false, Bool.false_eq_true, «guard», bind, pure, ↓reduceIte]; rfl
theorem acceptKeys_eq_none_of_dh4_zero (P : Primitives) (inp : AcceptKeysInput) (opkSk : Bytes)
    (htrust : inp.trustedPeer = true) (hreplay : inp.replayOk = true) (hik : inp.hdr.ikAPk.length =
    32) (hek : inp.hdr.ekAPk.length = 32) (hcanon : P.isCanonical inp.hdr.ekAPk = true)
    (hdh1 : P.x25519 inp.spkBSk inp.hdr.ikAPk ≠ List.replicate 32 0)
    (hdh2 : P.x25519 inp.ikBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hdh3 : P.x25519 inp.spkBSk inp.hdr.ekAPk ≠ List.replicate 32 0)
    (hopk_eq : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome) (hopk : inp.opkBSk? = some opkSk)
    (hdh4 : P.x25519 opkSk inp.hdr.ekAPk = List.replicate 32 0) :
    Model.acceptKeys P inp = none := by
  obtain ⟨opkId, hopkId⟩ : ∃ id, inp.hdr.opkId? = some id := by
    cases h : inp.hdr.opkId? with
    | none => simp [h, hopk] at hopk_eq | some id => exact ⟨id, rfl⟩
  have hdh1_bne : (P.x25519 inp.spkBSk inp.hdr.ikAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh1
  have hdh2_bne : (P.x25519 inp.ikBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh2
  have hdh3_bne : (P.x25519 inp.spkBSk inp.hdr.ekAPk != List.replicate 32 0) = true :=
    bne_iff_ne.mpr hdh3
  simp only [Model.acceptKeys, dhOptNonZero, htrust, hreplay, hik, hek, hcanon, hdh1_bne, hdh2_bne,
    hdh3_bne, hopk, hopkId, hdh4, beq_self_eq_true, «guard», bind, pure, ↓reduceIte]; rfl
theorem cells3_sub4912_to_memRegion24 (sp w0 w1 w2 : BitVec 64) : ((sp - 4912#64) ↦₆₄ w0) ∗ ((sp -
    4904#64) ↦₆₄ w1) ∗ ((sp - 4896#64) ↦₆₄ w2) ⊢ memRegion (sp - 4912#64) 24 := by
  have hc3 := cells_3_merge (sp - 4912#64) w0 w1 w2
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hc3
  rw [← (memRegion_cells (sp - 4912#64) 3 (by decide) : memRegion (sp - 4912#64) 24 = cells (sp -
    4912#64) 3)] at hc3; exact hc3
theorem alloc_to_calc_stack (sp : BitVec 64) : memRegion (sp - 9440#64) 400 ∗ stackAt (sp -
    4944#64) allocHookStack = memRegion (sp - 9440#64) 240 ∗ stackAt (sp -
      4944#64) calculateAgreementStack := (subStack_to_alloc sp).symm.trans (subStack_to_calc sp)
theorem calc_to_alloc_stack (sp : BitVec 64) : memRegion (sp - 9440#64) 240 ∗ stackAt (sp -
    4944#64) calculateAgreementStack = memRegion (sp - 9440#64) 400 ∗ stackAt (sp -
      4944#64) allocHookStack := (subStack_to_calc sp).symm.trans (subStack_to_alloc sp)
theorem vec_err_dh1_merge (a : BitVec 64) : (a ↦ₛ bytesToBv8 F_X25519) ∗ memRegion (a + 32#64) 32 ∗
    memRegion (a + 64#64) 32 ∗ memRegion (a + 96#64) 32 ∗ memRegion (a + 128#64) 32 ∗ memRegion (a +
      160#64) 32 ⊢ memRegion a 192 := by
  have h32 : (bytesToBv8 F_X25519).length = 32 := by decide
  refine Entails.trans (sepConj_mono_left (h32 ▸
    pointsToBytes_entails_memRegion a (bytesToBv8 F_X25519))) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 32) (k := 160) (b' :=
    a + 32#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := a + 32#64) (n :=
    32) (k := 128) (b' := a + 64#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      a + 64#64) (n := 32) (k := 96) (b' :=
        a + 96#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := a + 96#64) (n :=
        32) (k := 64) (b' := a + 128#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 128#64) (n := 32) (k := 32) (b' :=
        a + 160#64) rfl (by bv_omega) (by decide)]; exact Entails.refl _
theorem vec_err_dh2_merge (a : BitVec 64) {bs : Bytes} (hbs : bs.length = 64) :
    (a ↦ₛ bytesToBv8 bs) ∗ memRegion (a + 64#64) 32 ∗ memRegion (a + 96#64) 32 ∗ memRegion (a +
      128#64) 32 ∗ memRegion (a + 160#64) 32 ⊢ memRegion a 192 := by
  have h64 : (bytesToBv8 bs).length = 64 := by simp [bytesToBv8, hbs]
  refine Entails.trans (sepConj_mono_left (h64 ▸
    pointsToBytes_entails_memRegion a (bytesToBv8 bs))) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 64) (k := 128) (b' :=
    a + 64#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := a + 64#64) (n :=
    32) (k := 96) (b' := a + 96#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      a + 96#64) (n := 32) (k := 64) (b' :=
        a + 128#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := a + 128#64) (n :=
        32) (k := 32) (b' := a + 160#64) rfl (by bv_omega) (by decide)]; exact Entails.refl _
theorem vec_err_dh3_merge (a : BitVec 64) {bs : Bytes} (hbs : bs.length = 96) :
    (a ↦ₛ bytesToBv8 bs) ∗ memRegion (a + 96#64) 32 ∗ memRegion (a + 128#64) 32 ∗ memRegion (a +
      160#64) 32 ⊢ memRegion a 192 := by
  have h96 : (bytesToBv8 bs).length = 96 := by simp [bytesToBv8, hbs]
  refine Entails.trans (sepConj_mono_left (h96 ▸
    pointsToBytes_entails_memRegion a (bytesToBv8 bs))) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 96) (k := 96) (b' :=
    a + 96#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := a + 96#64) (n :=
    32) (k := 64) (b' := a + 128#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
      a + 128#64) (n := 32) (k := 32) (b' := a + 160#64) rfl (by bv_omega) (by decide)]
  exact Entails.refl _
theorem vec_err_dh4_merge (a : BitVec 64) {bs : Bytes} (hbs : bs.length = 128) :
    (a ↦ₛ bytesToBv8 bs) ∗ memRegion (a + 128#64) 32 ∗ memRegion (a + 160#64) 32 ⊢
      memRegion a 192 := by
  have h128 : (bytesToBv8 bs).length = 128 := by simp [bytesToBv8, hbs]
  refine Entails.trans (sepConj_mono_left (h128 ▸
    pointsToBytes_entails_memRegion a (bytesToBv8 bs))) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 128) (k := 64) (b' :=
    a + 128#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := a + 128#64) (n :=
    32) (k := 32) (b' := a + 160#64) rfl (by bv_omega) (by decide)]; exact Entails.refl _
theorem calcErr_entails_at_sub4912 (sp : BitVec 64) : ((sp - 4912#64) ↦₆₄ 1#64) ∗ (∃∗
    hi : BitVec 56, (sp - 4904#64) ↦₆₄ (hi ++ 3#8)) ∗ (∃∗ u2 : BitVec 64, (sp - 4896#64) ↦₆₄ u2) ⊢
      ∃∗ u2 : BitVec 64, ∃∗ hi : BitVec 56, ((sp - 4912#64) ↦₆₄ 1#64) ∗ ((sp - 4904#64) ↦₆₄ (hi ++
        3#8)) ∗ ((sp - 4896#64) ↦₆₄ u2) := by
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; exact Entails.refl _
theorem boxSliceU8_32_entails_at_sub4912 (A : RustAlloc) (sp : BitVec 64) {bs : List (BitVec 8)}
    (hbs : bs.length = 32) : ((sp - 4912#64) ↦₆₄ 0#64) ∗ boxSliceU8 A (sp - 4904#64) bs ⊢ ∃∗
      dh_ptr : BitVec 64, ((sp - 4912#64) ↦₆₄ 0#64) ∗ ((sp - 4904#64) ↦₆₄ dh_ptr) ∗ ((sp -
        4896#64) ↦₆₄ 32#64) ∗ (dh_ptr ↦ₛ bs) ∗ A.live dh_ptr 32 1 := by
  refine Entails.trans (sepConj_mono_right (boxSliceU8_32_entails A (sp - 4904#64) bs hbs)) ?_
  rw [sepExists_sepConj_right]
  refine Entails.sepExists_elim fun dh_ptr => Entails.sepExists_right dh_ptr ?_
  simp only [bv_sub_add_lit', BitVec.reduceSub]; exact Entails.of_eq (by ac_rfl)
theorem calc_to_vecAppend_stack (sp : BitVec 64) : memRegion (sp - 9440#64) 240 ∗ stackAt (sp -
    4944#64) calculateAgreementStack = memRegion (sp - 9440#64) 4448 ∗ cells (sp - 4992#64) 6 :=
  (subStack_to_calc sp).symm.trans (subStack_to_vecAppend sp)
theorem vecAppend_to_alloc_stack (sp : BitVec 64) : memRegion (sp - 9440#64) 4448 ∗ cells (sp -
    4992#64) 6 = memRegion (sp - 9440#64) 400 ∗ stackAt (sp - 4944#64) allocHookStack :=
  (subStack_to_vecAppend sp).symm.trans (subStack_to_alloc sp)
theorem vec_ok_160_merge (a : BitVec 64) {bs : Bytes} (hbs : bs.length = 160) :
    (a ↦ₛ bytesToBv8 bs) ∗ memRegion (a + 160#64) 32 ⊢ memRegion a 192 := by
  have h160 : (bytesToBv8 bs).length = 160 := by simp [bytesToBv8, hbs]
  refine Entails.trans (sepConj_mono_left (h160 ▸
    pointsToBytes_entails_memRegion a (bytesToBv8 bs))) ?_
  rw [ProofLib.memRegion_split' (b := a) (n := 160) (k := 32) (b' :=
    a + 160#64) rfl (by bv_omega) (by decide)]; exact Entails.refl _
theorem vec_ok_192_merge (a : BitVec 64) {bs : Bytes} (hbs : bs.length = 192) :
    (a ↦ₛ bytesToBv8 bs) ⊢ memRegion a 192 := by
  have h192 : (bytesToBv8 bs).length = 192 := by simp [bytesToBv8, hbs]
  exact h192 ▸ pointsToBytes_entails_memRegion a (bytesToBv8 bs)
theorem pqsk_head_tail_merge (sp : BitVec 64) {sk : Bytes} (h : sk.length = 3168) : ((sp -
    4912#64) ↦₈ (bytesToBv8 sk).getD 0 0#8) ∗ ((sp - 4911#64) ↦ₛ (bytesToBv8 sk).drop 1) ⊢
      ((sp - 4912#64) ↦ₛ bytesToBv8 sk) := by
  have h1 : sp - 4912#64 + 1#64 = sp - 4911#64 := by bv_omega
  rw [← h1, ← bytesToBv8_head_tail (sp - 4912#64) (bytesToBv8 sk) (by simp [bytesToBv8, h])]
  exact Entails.refl _
theorem kemct_head_tail_merge (sp : BitVec 64) {ct : Bytes} (h : ct.length = 1568) : ((sp -
    1744#64) ↦₈ (bytesToBv8 ct).getD 0 0#8) ∗ ((sp - 1743#64) ↦ₛ (bytesToBv8 ct).drop 1) ⊢
      ((sp - 1744#64) ↦ₛ bytesToBv8 ct) := by
  have h1 : sp - 1744#64 + 1#64 = sp - 1743#64 := by bv_omega
  rw [← h1, ← bytesToBv8_head_tail (sp - 1744#64) (bytesToBv8 ct) (by simp [bytesToBv8, h])]
  exact Entails.refl _
theorem sub176_split_32_64 (sp : BitVec 64) : memRegion (sp - 176#64) 96 = memRegion (sp -
      176#64) 32 ∗ (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗
        u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64, ((sp -
        144#64) ↦₆₄ u0) ∗ ((sp - 136#64) ↦₆₄ u1) ∗ ((sp - 128#64) ↦₆₄ u2) ∗ ((sp - 120#64) ↦₆₄ u3) ∗
        ((sp - 112#64) ↦₆₄ u4) ∗ ((sp - 104#64) ↦₆₄ u5) ∗ ((sp - 96#64) ↦₆₄ u6) ∗
        ((sp - 88#64) ↦₆₄ u7)) := by
  rw [ProofLib.memRegion_split' (b := sp - 176#64) (n := 32) (k := 64) (b' :=
        sp - 144#64) rfl (by bv_omega) (by decide), (memRegion_cells (sp - 144#64) 8 (by decide) :
        memRegion (sp - 144#64) 64 = cells (sp - 144#64) 8)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
theorem pqsk_to_extract_region (sp : BitVec 64) {sk : Bytes} (h : sk.length = 3168) : ((sp -
    4912#64) ↦ₛ bytesToBv8 sk) ⊢ memRegion (sp - 4912#64) 176 ∗ memRegion (sp - 4736#64) 2992 := by
  have hlen : (bytesToBv8 sk).length = 3168 := by simp [bytesToBv8, h]
  refine Entails.trans (hlen ▸ pointsToBytes_entails_memRegion (sp - 4912#64) (bytesToBv8 sk)) ?_
  rw [ProofLib.memRegion_split' (b := sp - 4912#64) (n := 176) (k := 2992) (b' :=
        sp - 4736#64) rfl (by bv_omega) (by decide)]; exact Entails.refl _
theorem kemct_to_hmac18_region (sp : BitVec 64) {ct : Bytes} (h : ct.length = 1568) : ((sp -
    1744#64) ↦ₛ bytesToBv8 ct) ⊢ (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗
      u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64, ∃∗
        u8 : BitVec 64, ∃∗ u9 : BitVec 64, ∃∗ u10 : BitVec 64, ∃∗ u11 : BitVec 64, ∃∗
       u12 : BitVec 64, ∃∗ u13 : BitVec 64, ∃∗ u14 : BitVec 64, ∃∗ u15 : BitVec 64, ∃∗
       u16 : BitVec 64, ∃∗ u17 : BitVec 64, ((sp - 1744#64) ↦₆₄ u0) ∗ ((sp - 1736#64) ↦₆₄ u1) ∗
       ((sp - 1728#64) ↦₆₄ u2) ∗ ((sp - 1720#64) ↦₆₄ u3) ∗ ((sp - 1712#64) ↦₆₄ u4) ∗ ((sp -
       1704#64) ↦₆₄ u5) ∗ ((sp - 1696#64) ↦₆₄ u6) ∗ ((sp - 1688#64) ↦₆₄ u7) ∗ ((sp -
       1680#64) ↦₆₄ u8) ∗ ((sp - 1672#64) ↦₆₄ u9) ∗ ((sp - 1664#64) ↦₆₄ u10) ∗ ((sp -
        1656#64) ↦₆₄ u11) ∗ ((sp - 1648#64) ↦₆₄ u12) ∗ ((sp - 1640#64) ↦₆₄ u13) ∗ ((sp -
        1632#64) ↦₆₄ u14) ∗ ((sp - 1624#64) ↦₆₄ u15) ∗ ((sp - 1616#64) ↦₆₄ u16) ∗ ((sp -
        1608#64) ↦₆₄ u17)) ∗ memRegion (sp - 1600#64) 1424 := by
  have hlen : (bytesToBv8 ct).length = 1568 := by simp [bytesToBv8, h]
  refine Entails.trans (hlen ▸ pointsToBytes_entails_memRegion (sp - 1744#64) (bytesToBv8 ct)) ?_
  rw [ProofLib.memRegion_split' (b := sp - 1744#64) (n := 144) (k := 1424) (b' :=
        sp - 1600#64) rfl (by bv_omega) (by decide), (memRegion_cells (sp - 1744#64) 18
        (by decide) : memRegion (sp - 1744#64) 144 = cells (sp - 1744#64) 18)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
  exact Entails.refl _
theorem sub1680_split_32_48 (sp : BitVec 64) : memRegion (sp - 1680#64) 80 = (∃∗ u0 : BitVec 64, ∃∗
      u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ((sp - 1680#64) ↦₆₄ u0) ∗ ((sp -
        1672#64) ↦₆₄ u1) ∗ ((sp - 1664#64) ↦₆₄ u2) ∗ ((sp -
        1656#64) ↦₆₄ u3)) ∗ memRegion (sp - 1648#64) 48 := by
  rw [ProofLib.memRegion_split' (b := sp - 1680#64) (n := 32) (k := 48) (b' :=
        sp - 1648#64) rfl (by bv_omega) (by decide), (memRegion_cells (sp - 1680#64) 4 (by decide) :
        memRegion (sp - 1680#64) 32 = cells (sp - 1680#64) 4)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
theorem sub4912_post_kdf_merge (sp : BitVec 64) (p0 p1 p2 p3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
    w12 w13 w14 w15 w16 w17 : BitVec 64) : ((sp - 4912#64) ↦₆₄ p0) ∗ ((sp - 4904#64) ↦₆₄ p1) ∗
    ((sp - 4896#64) ↦₆₄ p2) ∗ ((sp - 4888#64) ↦₆₄ p3) ∗ ((sp - 4880#64) ↦₆₄ w0) ∗ ((sp -
      4872#64) ↦₆₄ w1) ∗ ((sp - 4864#64) ↦₆₄ w2) ∗ ((sp - 4856#64) ↦₆₄ w3) ∗ ((sp -
      4848#64) ↦₆₄ w4) ∗ ((sp - 4840#64) ↦₆₄ w5) ∗ ((sp - 4832#64) ↦₆₄ w6) ∗ ((sp -
      4824#64) ↦₆₄ w7) ∗ ((sp - 4816#64) ↦₆₄ w8) ∗ ((sp - 4808#64) ↦₆₄ w9) ∗ ((sp -
        4800#64) ↦₆₄ w10) ∗ ((sp - 4792#64) ↦₆₄ w11) ∗ ((sp - 4784#64) ↦₆₄ w12) ∗ ((sp -
        4776#64) ↦₆₄ w13) ∗ ((sp - 4768#64) ↦₆₄ w14) ∗ ((sp - 4760#64) ↦₆₄ w15) ∗ ((sp -
        4752#64) ↦₆₄ w16) ∗ ((sp - 4744#64) ↦₆₄ w17) ∗ memRegion (sp - 4736#64) 2992 ⊢
      memRegion (sp - 4912#64) 3168 := by
  have hc4 := cells_4_merge (sp - 4912#64) p0 p1 p2 p3
  have hc8 := cells_8_merge (sp - 4880#64) w0 w1 w2 w3 w4 w5 w6 w7
  have hc10 := cells_10_merge (sp - 4816#64) w8 w9 w10 w11 w12 w13 w14 w15 w16 w17
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hc4 hc8 hc10
  rw [← (memRegion_cells (sp - 4912#64) 4 (by decide) : memRegion (sp - 4912#64) 32 = cells (sp -
    4912#64) 4)] at hc4
  rw [← (memRegion_cells (sp - 4880#64) 8 (by decide) : memRegion (sp - 4880#64) 64 = cells (sp -
    4880#64) 8)] at hc8
  rw [← (memRegion_cells (sp - 4816#64) 10 (by decide) : memRegion (sp - 4816#64) 80 = cells (sp -
    4816#64) 10)] at hc10
  rw [ProofLib.memRegion_split' (b := sp - 4912#64) (n := 32) (k := 3136) (b' :=
    sp - 4880#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := sp - 4880#64) (n :=
    64) (k := 3072) (b' := sp - 4816#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 4816#64) (n := 80) (k := 2992) (b' :=
        sp - 4736#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans ?_ (sepConj_mono_left hc4)
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left hc8))
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hc10)))
  exact Entails.of_eq (by ac_rfl)
theorem sub1744_post_kdf_merge (sp : BitVec 64) (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 : BitVec 64)
    : ((sp - 1744#64) ↦₆₄ u0) ∗ ((sp - 1736#64) ↦₆₄ u1) ∗ ((sp - 1728#64) ↦₆₄ u2) ∗ ((sp -
      1720#64) ↦₆₄ u3) ∗ ((sp - 1712#64) ↦₆₄ u4) ∗ ((sp - 1704#64) ↦₆₄ u5) ∗ ((sp -
      1696#64) ↦₆₄ u6) ∗ ((sp - 1688#64) ↦₆₄ u7) ∗ ((sp - 1680#64) ↦₆₄ u8) ∗ ((sp -
      1672#64) ↦₆₄ u9) ∗ ((sp - 1664#64) ↦₆₄ u10) ∗ ((sp - 1656#64) ↦₆₄ u11) ∗ memRegion (sp -
        1648#64) 48 ∗ memRegion (sp - 1600#64) 1424 ⊢ memRegion (sp - 1744#64) 1568 := by
  have hc12 := cells_12_merge (sp - 1744#64) u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hc12
  rw [← (memRegion_cells (sp - 1744#64) 12 (by decide) : memRegion (sp - 1744#64) 96 = cells (sp -
    1744#64) 12)] at hc12
  rw [ProofLib.memRegion_split' (b := sp - 1744#64) (n := 96) (k := 1472) (b' :=
    sp - 1648#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b := sp - 1648#64) (n :=
    48) (k := 1424) (b' := sp - 1600#64) rfl (by bv_omega) (by decide)]
  refine Entails.trans ?_ (sepConj_mono_left hc12); exact Entails.of_eq (by ac_rfl)
theorem sub176_post_kdf_merge (sp : BitVec 64) (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64) :
    ((sp - 176#64) ↦₆₄ w0) ∗ ((sp - 168#64) ↦₆₄ w1) ∗ ((sp - 160#64) ↦₆₄ w2) ∗ ((sp -
      152#64) ↦₆₄ w3) ∗ ((sp - 144#64) ↦₆₄ w4) ∗ ((sp - 136#64) ↦₆₄ w5) ∗ ((sp - 128#64) ↦₆₄ w6) ∗
      ((sp - 120#64) ↦₆₄ w7) ∗ ((sp - 112#64) ↦₆₄ w8) ∗ ((sp - 104#64) ↦₆₄ w9) ∗ ((sp -
      96#64) ↦₆₄ w10) ∗ ((sp - 88#64) ↦₆₄ w11) ⊢ memRegion (sp - 176#64) 96 := by
  have hc12 := cells_12_merge (sp - 176#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  simp only [bv_sub_add_lit', BitVec.reduceSub] at hc12
  rw [← (memRegion_cells (sp - 176#64) 12 (by decide) : memRegion (sp - 176#64) 96 = cells (sp -
    176#64) 12)] at hc12; exact hc12
theorem kyberDecaps_some_and_fitBv8_eq {P : Primitives} (hWF : StructuralPrims P) {sk ct : Bytes}
    (hsk : sk.length = 3168) (hct : ct.length = 1568) : ∃ ss : Bytes, P.kemDecaps sk ct = some ss ∧
    ss.length = 32 ∧ fitBv8 32 (kyberDecapsOutBytes P sk ct) = bytesToBv8 ss := by
  have his := hWF.kemDecaps_isSome sk ct hsk hct
  cases h : P.kemDecaps sk ct with
  | none => simp [h] at his
  | some ss =>
    have hlen := hWF.kemDecaps_len sk ct ss h
    exact ⟨ss, rfl, hlen, fitBv8_kyberDecapsOutBytes_eq h hlen⟩
theorem outPtr_ok104_cells_split (outPtr : BitVec 64) : memRegion outPtr 104 = (∃∗ v0 : BitVec 32,
      outPtr ↦₃₂ v0) ∗ (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
        ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗
       c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64, ((outPtr +
       4#64) ↦₆₄ c0) ∗ ((outPtr + 12#64) ↦₆₄ c1) ∗ ((outPtr + 20#64) ↦₆₄ c2) ∗ ((outPtr +
       28#64) ↦₆₄ c3) ∗ ((outPtr + 36#64) ↦₆₄ c4) ∗ ((outPtr + 44#64) ↦₆₄ c5) ∗ ((outPtr +
       52#64) ↦₆₄ c6) ∗ ((outPtr + 60#64) ↦₆₄ c7) ∗ ((outPtr + 68#64) ↦₆₄ c8) ∗ ((outPtr +
        76#64) ↦₆₄ c9) ∗ ((outPtr + 84#64) ↦₆₄ c10) ∗ ((outPtr + 92#64) ↦₆₄ c11)) ∗ (∃∗
        v100 : BitVec 32, (outPtr + 100#64) ↦₃₂ v100) := by
  rw [outPtr_ok104_split outPtr]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
theorem outPtr_ok104_cells_merge {P : Primitives} {secrets : Bytes} (outPtr : BitVec 64) {w0 w1 w2
    w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec 64} (hout : ∀ a : BitVec 64,
      (a ↦ₛ bytesToBv8 (handshakeKeysBytes100 (Model.deriveDRKeys P secrets))) = (a ↦₆₄ w0) ∗ ((a +
        8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w8) ∗ ((a +
        40#64) ↦₆₄ w9) ∗ ((a + 48#64) ↦₆₄ w10) ∗ ((a + 56#64) ↦₆₄ w11) ∗ ((a + 64#64) ↦₆₄ w4) ∗
        ((a + 72#64) ↦₆₄ w5) ∗ ((a + 80#64) ↦₆₄ w6) ∗ ((a + 88#64) ↦₆₄ w7) ∗ ((a +
        96#64) ↦₃₂ 0#32)) : (outPtr ↦₃₂ 0#32) ∗ ((outPtr + 4#64) ↦₆₄ w0) ∗ ((outPtr +
    12#64) ↦₆₄ w1) ∗ ((outPtr + 20#64) ↦₆₄ w2) ∗ ((outPtr + 28#64) ↦₆₄ w3) ∗ ((outPtr +
      36#64) ↦₆₄ w8) ∗ ((outPtr + 44#64) ↦₆₄ w9) ∗ ((outPtr + 52#64) ↦₆₄ w10) ∗ ((outPtr +
      60#64) ↦₆₄ w11) ∗ ((outPtr + 68#64) ↦₆₄ w4) ∗ ((outPtr + 76#64) ↦₆₄ w5) ∗ ((outPtr +
      84#64) ↦₆₄ w6) ∗ ((outPtr + 92#64) ↦₆₄ w7) ∗ ((outPtr + 100#64) ↦₃₂ 0#32) ⊢
      (outPtr ↦ₛ bytesToBv8 (handshakeKeysResultOk104 (Model.deriveDRKeys P secrets))) := by
  have h := hout (outPtr + 4#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [← outPtr_ok104_eq outPtr (Model.deriveDRKeys P secrets), h]; exact Entails.of_eq (by ac_rfl)
theorem ss_sub176_eq (sp : BitVec 64) {ss : Bytes} {s0_w s1_w s2_w s3_w : BitVec 64} (hss_cells : ∀
    a : BitVec 64, (a ↦ₛ bytesToBv8 ss) = (a ↦₆₄ s0_w) ∗ ((a + 8#64) ↦₆₄ s1_w) ∗ ((a +
        16#64) ↦₆₄ s2_w) ∗ ((a + 24#64) ↦₆₄ s3_w)) : ((sp - 176#64) ↦ₛ bytesToBv8 ss) = ((sp -
      176#64) ↦₆₄ s0_w) ∗ ((sp - 168#64) ↦₆₄ s1_w) ∗ ((sp - 160#64) ↦₆₄ s2_w) ∗ ((sp -
        152#64) ↦₆₄ s3_w) := by
  have h := hss_cells (sp - 176#64); simp only [bv_sub_add_lit', BitVec.reduceSub] at h; exact h
theorem ss_vec_add128_merge (vec_ptr : BitVec 64) {ss : Bytes} {s0_w s1_w s2_w s3_w : BitVec 64}
    (hss_cells : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 ss) = (a ↦₆₄ s0_w) ∗ ((a + 8#64) ↦₆₄ s1_w) ∗
        ((a + 16#64) ↦₆₄ s2_w) ∗ ((a + 24#64) ↦₆₄ s3_w)) : ((vec_ptr + 128#64) ↦₆₄ s0_w) ∗
    ((vec_ptr + 136#64) ↦₆₄ s1_w) ∗ ((vec_ptr + 144#64) ↦₆₄ s2_w) ∗ ((vec_ptr + 152#64) ↦₆₄ s3_w) ⊢
      ((vec_ptr + 128#64) ↦ₛ bytesToBv8 ss) := by
  have h := hss_cells (vec_ptr + 128#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [h]; exact Entails.refl _
theorem ss_vec_add160_merge (vec_ptr : BitVec 64) {ss : Bytes} {s0_w s1_w s2_w s3_w : BitVec 64}
    (hss_cells : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 ss) = (a ↦₆₄ s0_w) ∗ ((a + 8#64) ↦₆₄ s1_w) ∗
        ((a + 16#64) ↦₆₄ s2_w) ∗ ((a + 24#64) ↦₆₄ s3_w)) : ((vec_ptr + 160#64) ↦₆₄ s0_w) ∗
    ((vec_ptr + 168#64) ↦₆₄ s1_w) ∗ ((vec_ptr + 176#64) ↦₆₄ s2_w) ∗ ((vec_ptr + 184#64) ↦₆₄ s3_w) ⊢
      ((vec_ptr + 160#64) ↦ₛ bytesToBv8 ss) := by
  have h := hss_cells (vec_ptr + 160#64); simp only [BitVec.add_assoc, BitVec.reduceAdd] at h
  rw [h]; exact Entails.refl _
theorem prk_sub4912_eq (sp : BitVec 64) {prk : Bytes} {p0 p1 p2 p3 : BitVec 64} (hprk : ∀ a : BitVec
    64, (a ↦ₛ bytesToBv8 prk) = (a ↦₆₄ p0) ∗ ((a + 8#64) ↦₆₄ p1) ∗ ((a + 16#64) ↦₆₄ p2) ∗ ((a +
        24#64) ↦₆₄ p3)) : ((sp - 4912#64) ↦ₛ bytesToBv8 prk) ⊢ ((sp - 4912#64) ↦₆₄ p0) ∗ ((sp -
      4904#64) ↦₆₄ p1) ∗ ((sp - 4896#64) ↦₆₄ p2) ∗ ((sp - 4888#64) ↦₆₄ p3) := by
  have h := hprk (sp - 4912#64); simp only [bv_sub_add_lit', BitVec.reduceSub] at h
  rw [h]; exact Entails.refl _
theorem okm_sub176_eq (sp : BitVec 64) {okm : Bytes} {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 : BitVec
    64} (hokm : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 okm) = (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a +
        16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a +
        48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗
        ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11)) : ((sp - 176#64) ↦ₛ bytesToBv8 okm) ⊢
      ((sp - 176#64) ↦₆₄ w0) ∗ ((sp - 168#64) ↦₆₄ w1) ∗ ((sp - 160#64) ↦₆₄ w2) ∗ ((sp -
        152#64) ↦₆₄ w3) ∗ ((sp - 144#64) ↦₆₄ w4) ∗ ((sp - 136#64) ↦₆₄ w5) ∗ ((sp - 128#64) ↦₆₄ w6) ∗
        ((sp - 120#64) ↦₆₄ w7) ∗ ((sp - 112#64) ↦₆₄ w8) ∗
      ((sp - 104#64) ↦₆₄ w9) ∗ ((sp - 96#64) ↦₆₄ w10) ∗ ((sp - 88#64) ↦₆₄ w11) := by
  have h := hokm (sp - 176#64); simp only [bv_sub_add_lit', BitVec.reduceSub] at h
  rw [h]; exact Entails.refl _
theorem cells4_to_memRegion32 (a v0 v1 v2 v3 : BitVec 64) : (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a +
    16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ⊢ memRegion a 32 := by
  rw [(memRegion_cells a 4 (by decide) : memRegion a 32 = cells a 4)]
  exact cells_4_merge a v0 v1 v2 v3
theorem hmacCore_split_sub4880 (P : Primitives) (sp : BitVec 64) (prk : Bytes) : pqxdhHmacStateAt P
    (sp - 4880#64) prk ⊢ ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64, ∃∗ w8 : BitVec 64,
        ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ w11 : BitVec 64, ∃∗ w12 : BitVec 64, ∃∗
      w13 : BitVec 64, ∃∗ w14 : BitVec 64, ∃∗ w15 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗
        w17 : BitVec 64,
        ⌜PqxdhHmacGood P prk w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17⌝ ∗ ((sp -
        4880#64) ↦₆₄ w0) ∗ ((sp - 4872#64) ↦₆₄ w1) ∗ ((sp - 4864#64) ↦₆₄ w2) ∗ ((sp -
        4856#64) ↦₆₄ w3) ∗ ((sp - 4848#64) ↦₆₄ w4) ∗ ((sp - 4840#64) ↦₆₄ w5) ∗ ((sp -
        4832#64) ↦₆₄ w6) ∗ ((sp - 4824#64) ↦₆₄ w7) ∗ ((sp - 4816#64) ↦₆₄ w8) ∗ ((sp -
        4808#64) ↦₆₄ w9) ∗ ((sp - 4800#64) ↦₆₄ w10) ∗ ((sp - 4792#64) ↦₆₄ w11) ∗ ((sp -
        4784#64) ↦₆₄ w12) ∗ ((sp - 4776#64) ↦₆₄ w13) ∗ ((sp - 4768#64) ↦₆₄ w14) ∗ ((sp -
        4760#64) ↦₆₄ w15) ∗ ((sp - 4752#64) ↦₆₄ w16) ∗ ((sp - 4744#64) ↦₆₄ w17) := by
  have h := hmacCore_split P (sp - 4880#64) prk; simp only [bv_sub_add_lit', BitVec.reduceSub] at h
  exact h
theorem ss_and_vec128_split (ss_ptr vec_ptr : BitVec 64) : memRegion ss_ptr 32 ∗
    memRegion (vec_ptr + 128#64) 32 = (∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗
      d3 : BitVec 64, (ss_ptr ↦₆₄ d0) ∗ ((ss_ptr + 8#64) ↦₆₄ d1) ∗ ((ss_ptr + 16#64) ↦₆₄ d2) ∗
        ((ss_ptr + 24#64) ↦₆₄ d3)) ∗ (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗
        e3 : BitVec 64, ((vec_ptr + 128#64) ↦₆₄ e0) ∗ ((vec_ptr + 136#64) ↦₆₄ e1) ∗ ((vec_ptr +
        144#64) ↦₆₄ e2) ∗ ((vec_ptr + 152#64) ↦₆₄ e3)) := by
  rw [(memRegion_cells ss_ptr 4 (by decide) : memRegion ss_ptr 32 = cells ss_ptr 4),
    cells4_eq ss_ptr, (memRegion_cells (vec_ptr + 128#64) 4 (by decide) : memRegion (vec_ptr +
    128#64) 32 = cells (vec_ptr + 128#64) 4), cells4_eq (vec_ptr + 128#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem ss_and_vec160_split (ss_ptr vec_ptr : BitVec 64) : memRegion ss_ptr 32 ∗
    memRegion (vec_ptr + 160#64) 32 = (∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗
      d3 : BitVec 64, (ss_ptr ↦₆₄ d0) ∗ ((ss_ptr + 8#64) ↦₆₄ d1) ∗ ((ss_ptr + 16#64) ↦₆₄ d2) ∗
        ((ss_ptr + 24#64) ↦₆₄ d3)) ∗ (∃∗ e0 : BitVec 64, ∃∗ e1 : BitVec 64, ∃∗ e2 : BitVec 64, ∃∗
        e3 : BitVec 64, ((vec_ptr + 160#64) ↦₆₄ e0) ∗ ((vec_ptr + 168#64) ↦₆₄ e1) ∗ ((vec_ptr +
        176#64) ↦₆₄ e2) ∗ ((vec_ptr + 184#64) ↦₆₄ e3)) := by
  rw [(memRegion_cells ss_ptr 4 (by decide) : memRegion ss_ptr 32 = cells ss_ptr 4),
    cells4_eq ss_ptr, (memRegion_cells (vec_ptr + 160#64) 4 (by decide) : memRegion (vec_ptr +
    160#64) 32 = cells (vec_ptr + 160#64) 4), cells4_eq (vec_ptr + 160#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem SepWP.rw_pre {prog : Program} {ret : BitVec 64} {s : State} {P P' : SepProp} {Q : State →
    SepProp → Prop} (hP : P = P') (h : SepWP prog ret s P' Q) :
    SepWP prog ret s P Q := hP ▸ h
theorem stack_to_kdf (sp : BitVec 64) : memRegion (sp - 16384#64) 6944 ∗ memRegion (sp -
    9440#64) 400 = memRegion (sp - 16384#64) 3248 ∗ memRegion (sp - 13136#64) 3936 ∗ memRegion (sp -
        9200#64) 160 := by
  rw [← ProofLib.memRegion_split' (b := sp - 16384#64) (n := 6944) (k := 400) (b' :=
        sp - 9440#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 16384#64) (n := 3248) (k := 4096) (b' :=
        sp - 13136#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_split' (b :=
        sp - 13136#64) (n := 3936) (k := 160) (b' := sp - 9200#64) rfl (by bv_omega) (by decide)]
theorem subStack_to_alloc_of_eq (sp sp' : BitVec 64) (h : sp' = sp - 4944#64) : memRegion (sp -
    9440#64) 400 ∗ stackAt sp' allocHookStack ⊢ stackAt (sp - 4944#64) (pqxdhHookStack + 400) := by
  rw [h, ← subStack_to_alloc sp]; exact Entails.refl _
theorem alloc_to_calc_stack_of_eq (sp sp' : BitVec 64) (h : sp' = sp - 4944#64) : memRegion (sp -
    9440#64) 400 ∗ stackAt sp' allocHookStack ⊢
      memRegion (sp - 9440#64) 240 ∗ stackAt (sp - 4944#64) calculateAgreementStack := by
  rw [h, alloc_to_calc_stack sp]; exact Entails.refl _
theorem alloc_to_alloc_stack_of_eq (sp sp' : BitVec 64) (h : sp' = sp - 4944#64) :
    stackAt sp' allocHookStack ⊢ stackAt (sp - 4944#64) allocHookStack := by
  rw [h]; exact Entails.refl _
theorem vecAppend_to_alloc_stack_of_eq (sp sp' : BitVec 64) (h : sp' = sp - 4992#64) :
    memRegion (sp - 9440#64) 4448 ∗ cells sp' 6 ⊢
      memRegion (sp - 9440#64) 400 ∗ stackAt (sp - 4944#64) allocHookStack := by
  rw [h, vecAppend_to_alloc_stack sp]; exact Entails.refl _
theorem pointsToBytes_append_at_dh3 (p : BitVec 64) (b1 b2 b3 : Bytes) (h : (F_X25519 ++ b1 ++
    b2).length = 96) : (p ↦ₛ bytesToBv8 (F_X25519 ++ (b1 ++ b2))) ∗ ((p + 96#64) ↦ₛ bytesToBv8 b3) =
      (p ↦ₛ bytesToBv8 (F_X25519 ++ b1 ++ b2 ++ b3)) := by
  rw [← List.append_assoc F_X25519 b1 b2]
  exact pointsToBytes_append_at p (F_X25519 ++ b1 ++ b2) b3 96 (by simp only [bytesToBv8,
    List.length_map, h])
attribute [-arm64_norm] List.append_assoc
abbrev pqxdhAcceptErrStrongAt (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₃₂ 1#32) ∗ memRegion (outPtr + 4#64) 4 ∗ (∃∗ w1 : BitVec 64, ⌜w1 ≠ pollReadyOkWord⌝ ∗
    ((outPtr + 8#64) ↦₆₄ w1)) ∗ memRegion (outPtr + 16#64) 88
theorem outPtr_err104_strong_merge (outPtr w1 w2 w3 w4 : BitVec 64) (b40 : BitVec 8) (hw1 : w1 ≠
    pollReadyOkWord) : (outPtr ↦₃₂ 1#32) ∗ memRegion (outPtr + 4#64) 4 ∗ ((outPtr + 8#64) ↦₆₄ w1) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗ ((outPtr +
      40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 ⊢ pqxdhAcceptErrStrongAt outPtr := by
  unfold pqxdhAcceptErrStrongAt; refine sepConj_mono_right (sepConj_mono_right ?_)
  have hw1_ent : ((outPtr + 8#64) ↦₆₄ w1) ⊢
      ∃∗ w1' : BitVec 64, ⌜w1' ≠ pollReadyOkWord⌝ ∗ ((outPtr + 8#64) ↦₆₄ w1') := by
    rw [← pure_sepConj_of_true hw1 ((outPtr + 8#64) ↦₆₄ w1)]
    exact Entails.sepExists_right w1 (Entails.refl _)
  have hc3 : ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ⊢
      memRegion (outPtr + 16#64) 24 := by
    rw [show (24 : Nat) = 8 + (8 + 8) by decide, memRegion_split (outPtr + 16#64) 8 16 (by decide),
      memRegion_split (outPtr + 16#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ w2) (sepConj_mono
      (pointsTo64_entails_memRegion _ w3) (pointsTo64_entails_memRegion _ w4))
  have hb40 : ((outPtr + 40#64) ↦₈ b40) ⊢ memRegion (outPtr + 40#64) 1 := by
    rw [memRegion_one]; exact Entails.sepExists_right b40 (Entails.refl _)
  have hm88 : memRegion (outPtr + 16#64) 24 ∗ (memRegion (outPtr + 40#64) 1 ∗ memRegion (outPtr +
    41#64) 63) = memRegion (outPtr + 16#64) 88 := by
    rw [show outPtr + 41#64 = outPtr + 40#64 + BitVec.ofNat 64 1 by bv_omega, ←
      memRegion_split (outPtr + 40#64) 1 63 (by decide), show outPtr + 40#64 = outPtr + 16#64 +
      BitVec.ofNat 64 24 by bv_omega, ← memRegion_split (outPtr + 16#64) 24 64 (by decide)]
  rw [← hm88]; refine sepConj_mono hw1_ent ?_
  have hswap : ((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
    (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63))) =
      (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4))) ∗
        (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63) := (by ac_rfl); rw [hswap]
  exact sepConj_mono hc3 (sepConj_mono_left hb40)
theorem pqxdhAcceptErrStrongAt_entails (outPtr : BitVec 64) : pqxdhAcceptErrStrongAt outPtr ⊢
      (∃∗ tag : BitVec 8, ⌜tag ≠ 0#8⌝ ∗ (outPtr ↦₈ tag)) ∗ memRegion (outPtr + 1#64) 103 := by
  have h1 := pointsTo32_one_entails_tag_ne_zero outPtr
  have hw1 : (∃∗ w1 : BitVec 64, ⌜w1 ≠ pollReadyOkWord⌝ ∗ ((outPtr + 8#64) ↦₆₄ w1)) ⊢
      memRegion (outPtr + 8#64) 8 := Entails.sepExists_elim fun w1 => Entails.pure_left fun _ =>
      pointsTo64_entails_memRegion (outPtr + 8#64) w1
  have hm103 : memRegion (outPtr + 1#64) 3 ∗ (memRegion (outPtr + 4#64) 4 ∗ (memRegion (outPtr +
    8#64) 8 ∗ memRegion (outPtr + 16#64) 88)) = memRegion (outPtr + 1#64) 103 := by
    rw [show outPtr + 16#64 = outPtr + 8#64 + BitVec.ofNat 64 8 by bv_omega, ←
      memRegion_split (outPtr + 8#64) 8 88 (by decide), show outPtr + 8#64 = outPtr + 4#64 +
      BitVec.ofNat 64 4 by bv_omega, ← memRegion_split (outPtr + 4#64) 4 96 (by decide),
        show outPtr + 4#64 = outPtr + 1#64 + BitVec.ofNat 64 3 by bv_omega, ←
        memRegion_split (outPtr + 1#64) 3 100 (by decide)]
  unfold pqxdhAcceptErrStrongAt; rw [← hm103]; refine Entails.trans (sepConj_mono_left h1) ?_
  rw [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hw1)))
theorem subroutine_ok_weaken_post {α : Type} {prog : Program} {entry : BitVec 64} {spec1 spec2 :
    Spec α} (hpre : ∀ x s, spec2.pre x s = spec1.pre x s) (hpost : ∀ x s0 sf,
    spec1.post x s0 sf ⊢ spec2.post x s0 sf) (hpanic : ∀ x s0 sf, spec1.onPanic x s0 sf =
    spec2.onPanic x s0 sf) (hexit : ∀ x code s0 sf, spec1.onExit x code s0 sf =
    spec2.onExit x code s0 sf) (h : subroutine_ok prog entry spec1)
    (hoom : ∀ x s0 sf, spec1.onOom x s0 sf = spec2.onOom x s0 sf := by intros; rfl) :
    subroutine_ok prog entry spec2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre0 hsp => ?_
  rw [hpre] at hpre0
  refine h.mono_outcome x R s0 hpc hrun hpre0 hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨hoom_st, hq⟩
  · exact Or.inl ⟨hret, hcc, Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq⟩
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩); rwa [← hpanic]
  · refine Or.inr (Or.inr (Or.inl ⟨code, hex, ?_⟩)); rwa [← hexit]
  · refine Or.inr (Or.inr (Or.inr ⟨hoom_st, ?_⟩)); rwa [← hoom]
@[expose] def pqxdhAcceptErrStrong2At (outPtr : BitVec 64) : SepProp :=
  (outPtr ↦₃₂ 1#32) ∗ memRegion (outPtr + 4#64) 4 ∗ (∃∗ w1 : BitVec 64, ⌜w1 ≠ pollReadyOkWord ∧ w1 ≠
    0xfffffffffffffffd#64⌝ ∗ ((outPtr + 8#64) ↦₆₄ w1)) ∗ memRegion (outPtr + 16#64) 88
theorem outPtr_err104_strong2_merge (outPtr w1 w2 w3 w4 : BitVec 64) (b40 : BitVec 8) (hw1 : w1 ≠
    pollReadyOkWord ∧ w1 ≠ 0xfffffffffffffffd#64) : (outPtr ↦₃₂ 1#32) ∗ memRegion (outPtr +
    4#64) 4 ∗ ((outPtr + 8#64) ↦₆₄ w1) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr + 24#64) ↦₆₄ w3) ∗
      ((outPtr + 32#64) ↦₆₄ w4) ∗ ((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63 ⊢
      pqxdhAcceptErrStrong2At outPtr := by
  unfold pqxdhAcceptErrStrong2At; refine sepConj_mono_right (sepConj_mono_right ?_)
  have hw1_ent : ((outPtr + 8#64) ↦₆₄ w1) ⊢
      ∃∗ w1' : BitVec 64, ⌜w1' ≠ pollReadyOkWord ∧ w1' ≠ 0xfffffffffffffffd#64⌝ ∗ ((outPtr +
        8#64) ↦₆₄ w1') := by
    rw [← pure_sepConj_of_true hw1 ((outPtr + 8#64) ↦₆₄ w1)]
    exact Entails.sepExists_right w1 (Entails.refl _)
  have hc3 : ((outPtr + 16#64) ↦₆₄ w2) ∗ ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ⊢
      memRegion (outPtr + 16#64) 24 := by
    rw [show (24 : Nat) = 8 + (8 + 8) by decide, memRegion_split (outPtr + 16#64) 8 16 (by decide),
      memRegion_split (outPtr + 16#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ w2) (sepConj_mono
      (pointsTo64_entails_memRegion _ w3) (pointsTo64_entails_memRegion _ w4))
  have hb40 : ((outPtr + 40#64) ↦₈ b40) ⊢ memRegion (outPtr + 40#64) 1 := by
    rw [memRegion_one]; exact Entails.sepExists_right b40 (Entails.refl _)
  have hm88 : memRegion (outPtr + 16#64) 24 ∗ (memRegion (outPtr + 40#64) 1 ∗ memRegion (outPtr +
    41#64) 63) = memRegion (outPtr + 16#64) 88 := by
    rw [show outPtr + 41#64 = outPtr + 40#64 + BitVec.ofNat 64 1 by bv_omega, ←
      memRegion_split (outPtr + 40#64) 1 63 (by decide), show outPtr + 40#64 = outPtr + 16#64 +
      BitVec.ofNat 64 24 by bv_omega, ← memRegion_split (outPtr + 16#64) 24 64 (by decide)]
  rw [← hm88]; refine sepConj_mono hw1_ent ?_
  have hswap : ((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
    (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63))) =
      (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4))) ∗
        (((outPtr + 40#64) ↦₈ b40) ∗ memRegion (outPtr + 41#64) 63) := (by ac_rfl); rw [hswap]
  exact sepConj_mono hc3 (sepConj_mono_left hb40)
@[expose] def pqxdhAcceptFieldsAt (basePtr pqskPtr ctSlicePtr ctBufPtr : BitVec 64) (inp : AcceptKeysInput) :
    SepProp :=
  ((basePtr + 32#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗ ((basePtr + 96#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
    ((basePtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗ ((basePtr +
    160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((basePtr + 208#64) ↦₆₄ pqskPtr) ∗ ((basePtr +
    216#64) ↦₆₄ 3168#64) ∗ ((basePtr + 224#64) ↦₆₄ ctSlicePtr) ∗ ((basePtr +
    232#64) ↦₈ (if (match inp.opkBSk? with
    | some _ => true | none => false) = true then 1#8 else 0#8)) ∗
  ((basePtr + 265#64) ↦ₛ bytesToBv8 (inp.opkBSk?.getD (List.replicate 32 0))) ∗
    (pqskPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗ ((pqskPtr +
    1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗ (ctSlicePtr ↦₆₄ ctBufPtr) ∗ ((ctSlicePtr +
    8#64) ↦₆₄ 1569#64) ∗ (ctBufPtr ↦₈ 8#8) ∗ ((ctBufPtr +
    1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗ ((ctBufPtr +
    2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1)
structure AcceptFieldsCallGhost where
  inp : AcceptKeysInput
  argPtr : BitVec 64
  pqskPtr : BitVec 64
  ctSlicePtr : BitVec 64
  ctBufPtr : BitVec 64
  outPtr : BitVec 64
open Model
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff
@[expose] def pqxdhAcceptOptFieldsAt (basePtr pqskPtr ctSlicePtr ctBufPtr : BitVec 64) (inp : AcceptKeysInput)
    : SepProp :=
  ((basePtr + 32#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗ ((basePtr + 96#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
    ((basePtr + 128#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗ ((basePtr +
    160#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((basePtr + 208#64) ↦₆₄ pqskPtr) ∗ ((basePtr +
    216#64) ↦₆₄ 3168#64) ∗ ((basePtr + 224#64) ↦₆₄ ctSlicePtr) ∗ ((basePtr +
    232#64) ↦₈ (if (match inp.opkBSk? with
    | some _ => true | none => false) = true then 1#8 else 0#8)) ∗
  (match inp.opkBSk? with | some opkSk => (basePtr + 265#64) ↦ₛ bytesToBv8 opkSk | none => .emp) ∗
    (pqskPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗ ((pqskPtr +
    1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗ (ctSlicePtr ↦₆₄ ctBufPtr) ∗ ((ctSlicePtr +
    8#64) ↦₆₄ 1569#64) ∗ (ctBufPtr ↦₈ 8#8) ∗ ((ctBufPtr +
    1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗ ((ctBufPtr +
    2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1)

section Ext

export CryptoVerification.E2E.Pqxdh.Initiator
  (pqxdhHookStackExt pqxdhEntryStackExt pqxdhHkdfStackExt)

abbrev calculateAgreementSubStackExt : Nat := 64 + pqxdhHookStackExt
abbrev calculateAgreementStackExt : Nat := 160 + calculateAgreementSubStackExt

@[expose] def ecPubKeyIsCanonicalCallSpecExt (P : Primitives) : Spec KeyCanonicalGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.keyPtr ∧ g.keyBytes.length = 32⌝ ∗
      (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗ stackAt s.sp (pqxdhHookStackExt + 400)
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace ∧
      (sf.readReg64 .x0).setWidth 8 = (if P.isCanonicalEC g.keyBytes then 1#8 else 0#8)⌝ ∗
      (g.keyPtr ↦ₛ bytesToBv8 g.keyBytes) ∗ stackAt s0.sp (pqxdhHookStackExt + 400)

/-- Fast-path contract for `<Vec<u8>>::append_elements` with stacked
`memcpy` (`allocHookStack = 4096` B below `s.sp - 48`). -/
@[expose] def pqxdhVecAppendElementsFastSpecExt :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (vecHdr, vecPtr, srcPtr, bs) s =>
    ⌜s.readReg64 .x0 = vecHdr ∧ s.readReg64 .x1 = srcPtr ∧
      s.readReg64 .x2 = 32#64 ∧ bs.length = 32⌝ ∗
    (vecHdr ↦₆₄ 192#64) ∗ ((vecHdr + 8#64) ↦₆₄ vecPtr) ∗ ((vecHdr + 16#64) ↦₆₄ 128#64) ∗
    memRegion (vecPtr + 128#64) bs.length ∗ (srcPtr ↦ₛ bs) ∗
    stackAt (s.sp - 48#64) allocHookStack ∗ cells (s.sp - 48#64) 6
  post := fun (vecHdr, vecPtr, srcPtr, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (vecHdr ↦₆₄ 192#64) ∗ ((vecHdr + 8#64) ↦₆₄ vecPtr) ∗ ((vecHdr + 16#64) ↦₆₄ 160#64) ∗
    ((vecPtr + 128#64) ↦ₛ bs) ∗ (srcPtr ↦ₛ bs) ∗
    stackAt (s0.sp - 48#64) allocHookStack ∗ cells (s0.sp - 48#64) 6

end Ext

end CryptoVerification.E2E.Pqxdh.ResponderCore
