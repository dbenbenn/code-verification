/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.PreKey -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.VecDequeHeap -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
import LibsignalBinary.Proofs.Common.InImageKit
import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Specifications.AsmConstants
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.Placed.Bridge
import LibsignalBinary.Proofs.Placed.PlacedCallSym

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

/-! ## Code layout & stack/region splitting helpers -/

theorem memRegion_bound_of_pointsTo64 {m : Memory} {b a v : BitVec 64} {n : Nat} {R : SepProp}
    (h : m ⊨ memRegion b n ∗ ((a ↦₆₄ v) ∗ R)) : n ≤ 2 ^ 64 := by
  by_cases hn0 : n = 0
  · omega
  · have hd := disjointRegions_of_coversRegion (Nat.pos_of_ne_zero hn0) (by decide)
      (IsBlock.memRegion b n).covers (IsBlock.pointsTo64 a v).covers h
    have h1 := hd.1
    omega

theorem stackAt_sub_split (sp : BitVec 64) {subStk topStk : Nat}
    (hle : subStk ≤ topStk) (hhi : topStk ≤ 2 ^ 64) :
    stackAt sp topStk =
      memRegion (sp - BitVec.ofNat 64 topStk) (topStk - subStk) ∗ stackAt sp subStk := by
  have heq : topStk = subStk + (topStk - subStk) := by omega
  conv_lhs => rw [heq]
  rw [ProofLib.stackAt_split_bottom sp subStk (topStk - subStk) (by omega), ← heq]

theorem stackAt_kpkPoll_frame (sp : BitVec 64) {calleeStk : Nat}
    (hhi : calleeStk + 432 ≤ 2 ^ 64) :
    stackAt sp (calleeStk + 432) =
      stackAt (sp - 432#64) calleeStk ∗ cells (sp - 432#64) 54 :=
  ProofLib.stackAt_split_cells sp calleeStk 54 hhi

/-- Six consecutive 64-bit words (`48` bytes) starting at `a`. -/
@[expose] def words6At (a w0 w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
  ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)

/-- Eleven consecutive 64-bit words (`88` bytes) starting at `a`. -/
@[expose] def words11At (a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) : SepProp :=
  (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
  ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
  ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗ ((a + 64#64) ↦₆₄ w8) ∗
  ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10)

theorem memRegion_16_cells (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64,
        (a ↦₆₄ v1) ∗ ((a + 8#64) ↦₆₄ v0)) := by
  rw [show (16 : Nat) = 8 + 8 by rfl, memRegion_split a 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        (a ↦₆₄ v2) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v0)) := by
  rw [show (24 : Nat) = 8 + 16 by rfl, memRegion_split a 8 16 (by decide),
    ProofLib.memRegion_eight, memRegion_16_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_32_cells (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        (a ↦₆₄ v3) ∗ ((a + 8#64) ↦₆₄ v2) ∗ ((a + 16#64) ↦₆₄ v1) ∗ ((a + 24#64) ↦₆₄ v0)) := by
  rw [show (32 : Nat) = 8 + 24 by rfl, memRegion_split a 8 24 (by decide),
    ProofLib.memRegion_eight, memRegion_24_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_40_cells (a : BitVec 64) :
    memRegion a 40 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64,
        (a ↦₆₄ v4) ∗ ((a + 8#64) ↦₆₄ v3) ∗ ((a + 16#64) ↦₆₄ v2) ∗
        ((a + 24#64) ↦₆₄ v1) ∗ ((a + 32#64) ↦₆₄ v0)) := by
  rw [show (40 : Nat) = 8 + 32 by rfl, memRegion_split a 8 32 (by decide),
    ProofLib.memRegion_eight, memRegion_32_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion_48_words6 (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        words6At a w0 w1 w2 w3 w4 w5) := by
  rw [show (48 : Nat) = 8 + 40 by rfl, memRegion_split a 8 40 (by decide),
    ProofLib.memRegion_eight, memRegion_40_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  rfl

theorem memRegion_88_words11 (a : BitVec 64) :
    memRegion a 88 =
      (∃∗ w10 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w8 : BitVec 64, ∃∗ w7 : BitVec 64,
       ∃∗ w6 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        words11At a w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10) := by
  rw [show (88 : Nat) = 48 + 40 by rfl, memRegion_split a 48 40 (by decide),
    memRegion_48_words6, memRegion_40_cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, words6At, words11At,
    sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]

theorem words4_entails_memRegion_32 (a w0 w1 w2 w3 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ⊢
      memRegion a 32 := by
  rw [memRegion_32_cells]
  exact Entails.sepExists_right w3 (Entails.sepExists_right w2
    (Entails.sepExists_right w1 (Entails.sepExists_right w0 (Entails.refl _))))

theorem words5_entails_memRegion_40 (a w0 w1 w2 w3 w4 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ⊢ memRegion a 40 := by
  rw [memRegion_40_cells]
  exact Entails.sepExists_right w4 (Entails.sepExists_right w3
    (Entails.sepExists_right w2 (Entails.sepExists_right w1
      (Entails.sepExists_right w0 (Entails.refl _)))))

private theorem entails_of_eq {P Q : SepProp} (h : P = Q) : P ⊢ Q :=
  h ▸ Entails.refl P

private theorem entails_pure_right {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  have htrue : φ = True := propext ⟨fun _ => trivial, fun _ => hφ⟩
  rw [htrue, ProofLib.pure_true, emp_sepConj]
  exact h

theorem words11At_missing_entails (A : RustAlloc)
    (out w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) :
    words11At out 0xFFFFFFFFFFFFFFFF#64 0x800000000000000F#64
      w2 w3 w4 w5 w6 w7 w8 w9 w10 ⊢ kpkAnsAt A out .missing := by
  have herr : (0xFFFFFFFFFFFFFFFF#64 : BitVec 64) = errTag := by decide
  have hspe : (0x800000000000000F#64 : BitVec 64) = speWord 15 := by decide
  unfold words11At kpkAnsAt pkAnsAt
  rw [herr, hspe, show (88 - 16 : Nat) = 40 + 32 by rfl,
    memRegion_split (out + 0x10#64) 40 32 (by decide)]
  have h40 := words5_entails_memRegion_40 (out + 0x10#64) w2 w3 w4 w5 w6
  have h32 := words4_entails_memRegion_32 ((out + 0x10#64) + 40#64) w7 w8 w9 w10
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h40 h32 ⊢
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono h40 h32)))
  exact entails_of_eq (by ac_rfl)

/-! ## `vecU8Buf` borrowing, zero-capacity elimination, and deallocation -/

theorem vecU8Buf_zero_entails_emp (A : RustAlloc) (ptr : BitVec 64) (bs : List (BitVec 8)) :
    SpqrV1.Alloc.vecU8Buf A 0#64 ptr bs ⊢ emp := by
  unfold SpqrV1.Alloc.vecU8Buf
  exact (ProofLib.pure_extract_iff _ _ _).mpr fun _ => Entails.refl emp

private theorem vecU8Buf_cap_lt {A : RustAlloc} {cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {Q : SepProp} {m : Memory} (h : m ⊨ SpqrV1.Alloc.vecU8Buf A cap ptr bs ∗ Q) :
    cap.toNat < 2 ^ 63 := by
  unfold SpqrV1.Alloc.vecU8Buf at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.1

@[expose] def vecU8BufRest (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

private theorem vecU8Buf_split_raw (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    SpqrV1.Alloc.vecU8Buf A cap ptr bs ⊢ (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs := by
  unfold SpqrV1.Alloc.vecU8Buf vecU8BufRest
  refine (ProofLib.pure_extract_iff _ _ _).mpr fun hpure => ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero
      (Nat.eq_zero_of_le_zero (by simpa using hpure.1))
    subst hbs0
    rw [pointsToBytes_nil]
    refine Entails.trans (entails_pure_right hpure (Entails.refl _)) ?_
    exact entails_of_eq (ProofLib.emp_sepConj _).symm
  · simp only [hcap, ite_false]
    refine Entails.trans ?_ (sepConj_mono_right (entails_pure_right hpure (Entails.refl _)))
    exact entails_of_eq (by ac_rfl)

private theorem vecU8Buf_unsplit_raw (A : RustAlloc) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    (ptr ↦ₛ bs) ∗ vecU8BufRest A cap ptr bs ⊢ SpqrV1.Alloc.vecU8Buf A cap ptr bs := by
  unfold SpqrV1.Alloc.vecU8Buf vecU8BufRest
  rw [← sepConj_assoc, sepConj_comm (ptr ↦ₛ bs), sepConj_assoc]
  refine (ProofLib.pure_extract_iff _ _ _).mpr fun hpure => entails_pure_right hpure ?_
  by_cases hcap : cap = 0
  · subst hcap
    have hbs0 : bs = [] := List.eq_nil_of_length_eq_zero
      (Nat.eq_zero_of_le_zero (by simpa using hpure.1))
    subst hbs0
    rw [pointsToBytes_nil, ProofLib.emp_sepConj]
    exact Entails.refl _
  · simp only [hcap, ite_false]
    exact entails_of_eq (by ac_rfl)

private theorem bytesAt_false_eq (ptr : BitVec 64) (bs : List (BitVec 8)) :
    SpqrV1.ChainProofs.bytesAt false ptr bs = (ptr ↦ₛ bs) := rfl

/-- Wrapper contract for `__rust_dealloc(ptr, cap, 1)` freeing a non-empty-capacity `vecU8Buf`
while carrying `FsInv F0 T0` and `stackAt fsp calleeStk`. -/
abbrev DeallocBufGhost := BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64

@[expose] def deallocVecBufCellsSpec (A : RustAlloc) (F0 : FsFiles) (T0 : List TraceEvent)
    (calleeStk : Nat) : Spec DeallocBufGhost where
  pre := fun (cap, ptr, bs, fsp) s =>
    ⌜FsInv F0 T0 s ∧ cap ≠ 0#64 ∧
      s.readReg64 .x0 = ptr ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = 1#64 ∧
      s.sp = fsp⌝ ∗
    SpqrV1.Alloc.vecU8Buf A cap ptr bs ∗ stackAt fsp calleeStk ∗ A.pool
  post := fun (_cap, _ptr, _bs, fsp) s0 sf =>
    ⌜FsInv F0 T0 sf ∧ sf.trace = s0.trace⌝ ∗ stackAt fsp calleeStk ∗ A.pool

abbrev DecimalCellsGhost :=
  BitVec 32 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

@[expose] def decimalFsCellsSpec (A : RustAlloc) (F0 : FsFiles) (T0 : List TraceEvent)
    (calleeStk : Nat) : Spec DecimalCellsGhost where
  pre := fun (n, ret, o0, o1, o2, fsp) s =>
    ⌜FsInv F0 T0 s ∧ s.readReg64 .x0 = ret ∧ s.readReg32 .x1 = n ∧ s.sp = fsp⌝ ∗
    (ret ↦₆₄ o0) ∗ ((ret + 8#64) ↦₆₄ o1) ∗ ((ret + 16#64) ↦₆₄ o2) ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (n, ret, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ nCap : BitVec 64, ∃∗ nPtr : BitVec 64,
      ⌜FsInv F0 T0 sf ∧ sf.trace = s0.trace⌝ ∗
      (ret ↦₆₄ nCap) ∗ ((ret + 8#64) ↦₆₄ nPtr) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 (keyName n).length) ∗
      SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName n) ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Decomposed outcome of `Dir::get` at a 6-word (`48`-byte) stack slot `ret`. -/
@[expose] def dirGetPostProp (rd : ReadRule) (A : RustAlloc) (F0 : FsFiles) (T0 : List TraceEvent)
    (dir : DirGhost) (keyId : BitVec 32) (sf : State)
    (r : Except Unit (List (BitVec 8)))
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) : Prop :=
  match r with
  | .ok bs =>
    dir.get rd F0 (keyName keyId) = .ok bs ∧
    FsInv F0 T0 sf ∧
    sf.trace = T0 ∧
    w0 = 0xFFFFFFFFFFFFFFFE#64 ∧
    w3 = BitVec.ofNat 64 bs.length ∧
    H = SpqrV1.Alloc.vecU8Buf A w1 w2 bs
  | .error () =>
    w0 = 0x8000000000000001#64 ∧
    (dir.get rd F0 (keyName keyId) = .error () ∧ sf.trace = T0) ∧
    (∀ out t7 t8 t9 t10,
      words11At out 0xFFFFFFFFFFFFFFFF#64 0x8000000000000001#64
        w1 w2 w3 w4 w5 t7 t8 t9 t10 ∗ H ⊢ kpkAnsAt A out .readErr)

abbrev DirGetCellsGhost :=
  BitVec 64 × BitVec 64 × DirGhost × BitVec 32 × BitVec 64 × BitVec 64 ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

@[expose] def dirGetFsCellsSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (F0 : FsFiles) (T0 : List TraceEvent)
    (calleeStk : Nat) : Spec DirGetCellsGhost where
  pre := fun (ret, self, dir, keyId, nCap, nPtr, o0, o1, o2, o3, o4, o5, fsp) s =>
    ⌜FsInv F0 T0 s ∧ s.trace = T0 ∧ PkNameOk pathOk dir keyId ∧
      s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = self ∧ s.readReg64 .x2 = nPtr ∧
      s.readReg64 .x3 = BitVec.ofNat 64 (keyName keyId).length ∧ s.sp = fsp⌝ ∗
    dirAt A self dir ∗ SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName keyId) ∗
    words6At ret o0 o1 o2 o3 o4 o5 ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (ret, self, dir, keyId, nCap, nPtr, _o0, _o1, _o2, _o3, _o4, _o5, fsp) _s0 sf =>
    ∃∗ r : Except Unit (List (BitVec 8)),
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
    ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
    ∃∗ H : SepProp,
      ⌜dirGetPostProp rd A F0 T0 dir keyId sf r w0 w1 w2 w3 w4 w5 H⌝ ∗
      words6At ret w0 w1 w2 w3 w4 w5 ∗ H ∗
      dirAt A self dir ∗ SpqrV1.Alloc.vecU8Buf A nCap nPtr (keyName keyId) ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

private theorem kyberDeserialize_eq (bs : List (BitVec 8)) :
    KyberPreKeyRecord.deserialize bs =
      match SignedPreKeyRecordStructure.decode bs with
      | none => .error .invalidProtobufEncoding
      | some m => .ok ⟨m⟩ := by
  unfold KyberPreKeyRecord.deserialize
  cases SignedPreKeyRecordStructure.decode bs <;> rfl

/-- Decomposed outcome of `decode_kyber_pre_key` at an 11-word (`88`-byte) stack slot `ret`. -/
@[expose] def decodePostProp (A : RustAlloc) (F0 : FsFiles) (T0 : List TraceEvent)
    (bytes : List (BitVec 8)) (sf : State)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : BitVec 64) (H : SepProp) : Prop :=
  FsInv F0 T0 sf ∧ sf.trace = T0 ∧
  match KyberPreKeyRecord.deserialize bytes with
  | .ok r =>
    w0.toNat < 2 ^ 63 ∧
    (∀ out, words11At out w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗ H ⊢ kpkAnsAt A out (.found r))
  | .error e =>
    w0 = 0xFFFFFFFFFFFFFFFF#64 ∧
    (∀ out t7 t8 t9 t10,
      words11At out 0xFFFFFFFFFFFFFFFF#64 w1 w2 w3 w4 w5 w6 t7 t8 t9 t10 ∗ H ⊢
        kpkAnsAt A out (.decodeErr e))

abbrev DecodeCellsGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 ×
    BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64

@[expose] def decodeFsCellsSpec (A : RustAlloc) (F0 : FsFiles) (T0 : List TraceEvent)
    (calleeStk : Nat) : Spec DecodeCellsGhost where
  pre := fun (ret, bCap, bPtr, bytes, o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, fsp) s =>
    ⌜FsInv F0 T0 s ∧ s.trace = T0 ∧ 0 < bytes.length ∧ bytes.length < 2 ^ 32 ∧
      s.readReg64 .x0 = ret ∧ s.readReg64 .x1 = bPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 bytes.length ∧ s.sp = fsp⌝ ∗
    SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
    words11At ret o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 ∗
    stackAt fsp calleeStk ∗ A.pool
  post := fun (ret, bCap, bPtr, bytes, _o0, _o1, _o2, _o3, _o4, _o5, _o6, _o7, _o8, _o9, _o10, fsp)
      _s0 sf =>
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
    ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
    ∃∗ w8 : BitVec 64, ∃∗ w9 : BitVec 64, ∃∗ w10 : BitVec 64, ∃∗ H : SepProp,
      ⌜decodePostProp A F0 T0 bytes sf w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 H⌝ ∗
      words11At ret w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 ∗ H ∗
      SpqrV1.Alloc.vecU8Buf A bCap bPtr bytes ∗
      stackAt fsp calleeStk ∗ A.pool
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

@[expose] def cliKpkGetPollInnerSpec (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (calleeStk : Nat) : Spec KpkPollGhost where
  pre := fun x s =>
    ⌜FsInv s.fs.files s.trace s ∧
      s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧
      PkNameOk pathOk x.kg.oneTime x.id ∧ PkNameOk pathOk x.kg.lastResort x.id ∧
      PkSizeOk rd s.fs.files x.kg.oneTime x.id ∧ PkSizeOk rd s.fs.files x.kg.lastResort x.id⌝ ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 0#8) ∗
      dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
      memRegion x.out 88 ∗
      A.pool ∗ stackAt (s.sp - 432#64) calleeStk ∗ cells (s.sp - 432#64) 54
  post := fun x s0 sf =>
    (∃∗ ans : PkAns KyberPreKeyRecord,
      ⌜ans = kpkAnsOf
            (pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.oneTime.get rd s0.fs.files (keyName x.id)))
            (pkAnsOf KyberPreKeyRecord.deserialize
              (x.kg.lastResort.get rd s0.fs.files (keyName x.id))) ∧
          sf.trace = s0.trace⌝ ∗
      kpkAnsAt A x.out ans) ∗
      (x.fut ↦₆₄ x.self) ∗ ((x.fut + 8#64) ↦₃₂ x.id) ∗ ((x.fut + 0xc#64) ↦₈ 1#8) ∗
      dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
      A.pool ∗ stackAt (s0.sp - 432#64) calleeStk ∗ cells (s0.sp - 432#64) 54
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

end CryptoVerification.SignalSession.Cli.Store.KpkGetPoll.Helpers
