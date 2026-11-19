/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Decodes
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenVn
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `PqRatchetState::encode_to_vec`: Buffer Allocation, Epilogue, and Callee Wrappers

Empty-state encoded-length characterization, `vecU8At` byte/slice append helpers, stack-restore
epilogue (`0x6d720..0x6d74c`), initial `Vec<u8>` buffer allocation (`0x6d214..0x6d250`), and
exact-capacity callee call wrappers at `s.sp = sp - 144#64`.
-/

public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_lo_append64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by
  bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_hi_append64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by
  bv_kernel

/-! ## 1. Empty-State Encoded Length Characterization -/

theorem optVersionNegotiationPBFieldEncodedLen_pos (vn : VersionNegotiationPB) :
    0 < optVersionNegotiationPBFieldEncodedLen (some vn) := by
  dsimp [optVersionNegotiationPBFieldEncodedLen, versionNegotiationPBEncodedLen]
  have := (varintLen_bounds (BitVec.ofNat 64 (versionNegotiationPBEncodedLen vn))).1
  omega

theorem optChainPBFieldEncodedLen_pos (ch : ChainPB) :
    0 < optChainPBFieldEncodedLen (some ch) := by
  dsimp [optChainPBFieldEncodedLen]
  have := (varintLen_bounds (BitVec.ofNat 64 (chainPBEncodedLen ch))).1
  omega

theorem optPqRatchetInnerPBFieldEncodedLen_pos (in_ : PqRatchetState.Inner) :
    0 < optPqRatchetInnerPBFieldEncodedLen (some in_) := by
  cases in_ with
  | v1 v1s =>
    dsimp [optPqRatchetInnerPBFieldEncodedLen]
    have := (varintLen_bounds (BitVec.ofNat 64 (v1StatePBEncodedLen v1s))).1
    omega

theorem pqRatchetState_fields_none_of_encodedLen_zero {st : PqRatchetState}
    (h0 : pqRatchetStatePBEncodedLen st = 0) :
    st.versionNegotiation = none ∧ st.chain = none ∧ st.inner = none ∧
      PqRatchetState.encodeRaw st = [] := by
  have h0' := h0
  unfold pqRatchetStatePBEncodedLen at h0
  have hvn : st.versionNegotiation = none := by
    cases h : st.versionNegotiation with
    | none => rfl
    | some vn =>
      have hp := optVersionNegotiationPBFieldEncodedLen_pos vn
      rw [h] at h0; omega
  have hch : st.chain = none := by
    cases h : st.chain with
    | none => rfl
    | some ch =>
      have hp := optChainPBFieldEncodedLen_pos ch
      rw [h] at h0; omega
  have hin : st.inner = none := by
    cases h : st.inner with
    | none => rfl
    | some in_ =>
      have hp := optPqRatchetInnerPBFieldEncodedLen_pos in_
      rw [h] at h0; omega
  refine ⟨hvn, hch, hin, ?_⟩
  have hlen := pqRatchetStatePBEncodedLen_eq_proto st
  rw [h0'] at hlen
  exact List.eq_nil_of_length_eq_zero hlen

/-! ## 2. `vecU8At` Byte and Slice Manipulation Helpers -/

theorem vecU8At_expose_header (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          if cap = 0 then emp
          else
            A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
              memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  simp only [vecU8At, vecHeader, sepConj_assoc]

private theorem cap_ne_zero_of_pos {cap : BitVec 64} (h : 0 < cap.toNat) : cap ≠ 0 := by
  intro heq; subst heq; simp at h

theorem sepWPp_extract_vecU8At_bounds {A : RustAlloc} {v cap ptr : BitVec 64} {bs : List (BitVec 8)}
    {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = vecU8At A v cap ptr bs ∗ F)
    (h : bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hhm : s.mem ⊨
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ : SepProp) ∗
        ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) ∗ F ∗ R) := by
    rw [hP, vecU8At_expose_header] at hm
    convert hm using 1; ac_rfl
  rw [satisfies_pure_sepConj] at hhm
  exact h hhm.1.1 hhm.1.2.1 hhm.1.2.2 R hm hL

theorem vecU8At_expose_slice (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (n : Nat)
    (hle : bs.length + n ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63)
    (hptr : ptr ≠ 0) (hn_pos : 0 < n) :
    vecU8At A v cap ptr bs =
      ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) n ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 n)
          (cap.toNat - bs.length - n)) := by
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    eq_true ⟨by omega, hcap, hptr⟩
  have hcap_ne : cap ≠ 0 := cap_ne_zero_of_pos (by omega)
  rw [vecU8At_expose_header A v cap ptr bs, hpure, pure_true, emp_sepConj]
  simp only [hcap_ne, ↓reduceIte]
  rw [memRegion_split' (b := ptr + BitVec.ofNat 64 bs.length)
        (b' := ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 n)
        (n := n) (k := cap.toNat - bs.length - n)
        (by omega) rfl (by omega)]

theorem vecU8At_pack_slice (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs payload : List (BitVec 8))
    (hle : bs.length + payload.length ≤ cap.toNat)
    (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) (hne : payload ≠ []) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ payload) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length)
        (cap.toNat - bs.length - payload.length)) =
    vecU8At A v cap ptr (bs ++ payload) := by
  have hpos : 0 < payload.length := List.length_pos_of_ne_nil hne
  have hcap_ne : cap ≠ 0 := cap_ne_zero_of_pos (by omega)
  rw [vecU8At_expose_header A v cap ptr (bs ++ payload)]
  simp only [hcap_ne, ↓reduceIte]
  have hlen : (bs ++ payload).length = bs.length + payload.length := List.length_append
  have hbv : BitVec.ofNat 64 (bs.length + payload.length) =
      BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length := by
    simp [BitVec.ofNat_add]
  have hadd : ptr + (BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length) =
      ptr + BitVec.ofNat 64 bs.length + BitVec.ofNat 64 payload.length := by bv_omega
  have hsub : cap.toNat - (bs.length + payload.length) =
      cap.toNat - bs.length - payload.length := by omega
  have hpure : (bs.length + payload.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    eq_true ⟨hle, hcap, hptr⟩
  rw [hlen, hbv, hadd, hsub, pointsToBytes_append, hpure, pure_true, emp_sepConj]
  ac_rfl

theorem memRegion_one_eq (a : BitVec 64) : memRegion a 1 = ∃∗ y : BitVec 8, a ↦₈ y :=
  IsBlock.eq (IsBlock.memRegion a 1)
    (IsBlock.sepExists fun v => IsBlock.pointsTo8 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem memRegion_eight_eq (a : BitVec 64) : memRegion a 8 = ∃∗ v : BitVec 64, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem memRegion_24_eq (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ v2 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v0 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) := by
  rw [memRegion_split' (b := a) (b' := a + 8#64) (n := 8) (k := 16) (by decide) rfl (by decide),
    memRegion_split' (b := a + 8#64) (b' := a + 16#64) (n := 8) (k := 8) (by decide) (by bv_omega) (by decide),
    memRegion_eight_eq a, memRegion_eight_eq (a + 8#64), memRegion_eight_eq (a + 16#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem vecU8At_expose_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hlt : bs.length < cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    vecU8At A v cap ptr bs =
      ∃∗ y : BitVec 8,
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        ((ptr + BitVec.ofNat 64 bs.length) ↦₈ y) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1) := by
  rw [vecU8At_expose_slice A v cap ptr bs 1 (by omega) hcap hptr (by omega),
    memRegion_one_eq (ptr + BitVec.ofNat 64 bs.length)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem vecU8At_pack_one (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8))
    (byte : BitVec 8) (hlt : bs.length < cap.toNat) (hcap : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ (BitVec.ofNat 64 bs.length + 1#64)) ∗
      A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      ((ptr + BitVec.ofNat 64 bs.length) ↦₈ byte) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length + 1#64) (cap.toNat - bs.length - 1)) =
    vecU8At A v cap ptr (bs ++ [byte]) := by
  have h := vecU8At_pack_slice A v cap ptr bs [byte] (by simp; omega) hcap hptr (by simp)
  simpa only [List.length_singleton, BitVec.ofNat_eq_ofNat, pointsToBytes_singleton] using h

theorem vecU8At_empty_zero (A : RustAlloc) (v : BitVec 64) :
    ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) =
    vecU8At A v 0#64 1#64 [] := by
  have hpure : (([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0) = True :=
    eq_true ⟨by decide, by decide, by decide⟩
  rw [vecU8At_expose_header A v 0#64 1#64 [], hpure, pure_true, emp_sepConj]
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, ↓reduceIte, sepConj_emp]

theorem vecU8At_empty_of_alloc (A : RustAlloc) (v ptr : BitVec 64) (sz : Nat)
    (hpos : 0 < sz) (hsz : sz < 2 ^ 63) (hptr : ptr ≠ 0) :
    ((v ↦₆₄ BitVec.ofNat 64 sz) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
      A.live ptr sz 1 ∗ memRegion ptr sz) =
    vecU8At A v (BitVec.ofNat 64 sz) ptr [] := by
  have htoNat : (BitVec.ofNat 64 sz).toNat = sz := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_ne : BitVec.ofNat 64 sz ≠ 0 := cap_ne_zero_of_pos (by omega)
  have hpure : (([] : List (BitVec 8)).length ≤ (BitVec.ofNat 64 sz).toNat ∧
      (BitVec.ofNat 64 sz).toNat < 2 ^ 63 ∧ ptr ≠ 0) = True :=
    eq_true ⟨by simp, by omega, hptr⟩
  rw [vecU8At_expose_header A v (BitVec.ofNat 64 sz) ptr [], hpure, pure_true, emp_sepConj]
  simp only [hcap_ne, ↓reduceIte, htoNat, List.length_nil,
    BitVec.add_zero, Nat.sub_zero, pointsToBytes_nil, emp_sepConj]

theorem cap_beq_len_false_of_lt {cap : BitVec 64} {bsLen : Nat}
    (hlt : bsLen < cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    (cap == BitVec.ofNat 64 bsLen) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  omega

theorem elem_len_ult_spare_false_of_le {cap : BitVec 64} {bsLen elemLen : Nat}
    (hle : bsLen + elemLen ≤ cap.toNat) (hcap : cap.toNat < 2 ^ 63) :
    ((cap - BitVec.ofNat 64 bsLen).ult (BitVec.ofNat 64 elemLen)) = false := by
  have hle_bv : BitVec.ofNat 64 bsLen ≤ cap := by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, BitVec.toNat_sub_of_le hle_bv,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem calleeSavedPreserved_writeLr_setPC {s s' : State} {lr pc : BitVec 64}
    (h : CalleeSavedPreserved ((s.writeReg64 (Reg.gpr 30#5) lr).setPC pc) s') :
    s'.readReg64 .x19 = s.readReg64 .x19 ∧
    s'.readReg64 .x20 = s.readReg64 .x20 ∧
    s'.readReg64 .x21 = s.readReg64 .x21 ∧
    s'.readReg64 .x22 = s.readReg64 .x22 ∧
    s'.readReg64 .x23 = s.readReg64 .x23 ∧
    s'.readReg64 .x24 = s.readReg64 .x24 ∧
    s'.readReg64 .x25 = s.readReg64 .x25 ∧
    s'.readReg64 .x26 = s.readReg64 .x26 ∧
    s'.readReg64 .x27 = s.readReg64 .x27 ∧
    s'.readReg64 .x28 = s.readReg64 .x28 ∧
    s'.readReg64 .fp = s.readReg64 .fp ∧
    calleeSavedVRegs s' = calleeSavedVRegs s := by
  rcases h with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, hfp, hvregs⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simpa only [arm64_norm] using ‹_›

/-! ## 3. Callee Stack Contracts (`0x6d214..0x6d74c`) -/

/-- Stack-equipped no-op shim contract at `s.sp = sp - 144#64`. -/
@[expose] def shimStackSpecOf (resStack : Nat) : Spec Unit where
  pre := fun _ s => stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- Stack-equipped `__rust_alloc(sz, 1)` contract at `s.sp = sp - 144#64`. -/
@[expose] def rustAllocStackSpecOf (resStack : Nat) (A : RustAlloc) : Spec Nat where
  pre := fun sz s =>
    ⌜(s.readReg64 .x0).toNat = sz ∧ s.readReg64 .x1 = 1#64 ∧ 0 < sz ∧ sz < 2 ^ 63⌝ ∗
      A.pool ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun sz s0 sf =>
    (if sf.readReg64 .x0 = 0#64 then
      ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
     else
      ⌜sf.trace = s0.trace⌝ ∗ A.live (sf.readReg64 .x0) sz 1 ∗ memRegion (sf.readReg64 .x0) sz) ∗
      A.pool ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)

private theorem getLsbD_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem getElem_63_ofNat_eq_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false := by
  have htoNat : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.getElem_eq_testBit_toNat, htoNat]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_beq_zero_false_of_pos {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 63) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change n = 0 at ht
  omega

private theorem allocFailedIn_of_eq_trace {s0 sf : State}
    (h : sf.trace = s0.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  refine ⟨?_, ⟨[allocFailedEvent], h.symm⟩⟩
  simp [allocFailedIn, h]

theorem encodeToVecOnPanic_of_trace {s0 sf : State} {P R : SepProp}
    (htr : sf.trace = s0.trace ++ [allocFailedEvent])
    (hm : sf.mem ⊨ P ∗ R) :
    sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ R := by
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  unfold encodeToVecOnPanic
  have hp : (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) = True :=
    eq_true (allocFailedIn_of_eq_trace htr)
  rw [hp, pure_true, emp_sepConj]
  exact entails_anyHeap P

/-- Ghost state for exact-capacity `encode_varint [local#4]` (`0x4d710`) calls in `encode_to_vec`. -/
structure EtvEncodeVarintGhost where
  val : BitVec 64
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Exact-capacity `encode_varint [local#4]` (`0x4d710`) contract at `s.sp = sp - 144#64`:
requires `bs.length + (Proto.encodeVarint val).length ≤ cap.toNat` and preserves `(cap, ptr)`. -/
@[expose] def encodeVarintExactSpecOf (resStack : Nat) (A : RustAlloc) : Spec EtvEncodeVarintGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.val ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (Proto.encodeVarint x.val).length ≤ x.cap.toNat⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ Proto.encodeVarint x.val) ∗ A.pool ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

/-- Trace-preserving `memcpy` specification (definitionally equal to `sessionMemcpyRegionSpec`). -/
@[expose] def etvMemcpyRegionSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun ⟨dst, src, bs⟩ s =>
    ⌜s.readReg64 .x0 = dst ∧ s.readReg64 .x1 = src ∧ (s.readReg64 .x2).toNat = bs.length⌝ ∗
      memRegion dst bs.length ∗ (src ↦ₛ bs)
  post := fun ⟨dst, src, bs⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ₛ bs)

/-- Ghost state for exact-capacity `encode<ChainParams> [local#2]` (`0x52170`) calls in `encode_to_vec`. -/
structure EtvEncodeChainParamsGhost where
  tag : BitVec 32
  p : ChainParamsPB
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Exact-capacity `encode<ChainParams> [local#2]` (`0x52170`) contract at `s.sp = sp - 144#64`. -/
@[expose] def encodeChainParamsExactSpecOf (resStack : Nat) (A : RustAlloc) : Spec EtvEncodeChainParamsGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧
      s.readReg32 .x1 = x.p.maxJump ∧
      s.readReg32 .x2 = x.p.maxOooKeys ∧
      s.readReg64 .x3 = x.v ∧
      1 ≤ x.tag.toNat ∧ x.tag.toNat < 2 ^ 29 ∧
      x.bs.length + (Proto.encodeMessage ChainParamsPB.encodeRaw x.tag x.p).length ≤ x.cap.toNat⌝ ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ Proto.encodeMessage ChainParamsPB.encodeRaw x.tag x.p) ∗ A.pool ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

/-- `Epoch::encoded_len [local#2]` (`0x664fc`) contract at `s.sp = sp - 144#64`. -/
@[expose] def epochEncLenStackSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec (BitVec 64 × ChainEpochPBGhost × ChainEpochPB) where
  pre := fun ⟨a, g, ep⟩ s =>
    ⌜s.readReg64 .x0 = a ∧ chainEpochPBEncodedLen ep < 2 ^ 64⌝ ∗
      chainEpochPBPinnedAt A g a ep ∗ stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun ⟨a, g, ep⟩ s0 sf =>
    ⌜sf.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) ∧ sf.trace = s0.trace⌝ ∗
      chainEpochPBPinnedAt A g a ep ∗ stackAt s0.sp (encodeToVecCalleeStackOf resStack)

/-- Ghost state for exact-capacity `encode<EpochDirection> [local#2]` (`0x527c0`) calls. -/
structure EtvEncodeEpochDirectionGhost where
  tag : BitVec 32
  dirA : BitVec 64
  g : EpochDirectionPBGhost
  dir : EpochDirectionPB
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Exact-capacity `encode<EpochDirection> [local#2]` (`0x527c0`) contract at `s.sp = sp - 144#64`. -/
@[expose] def encodeEpochDirectionExactSpecOf (resStack : Nat) (A : RustAlloc) :
    Spec EtvEncodeEpochDirectionGhost where
  pre := fun x s =>
    ⌜s.readReg32 .x0 = x.tag ∧ s.readReg64 .x1 = x.dirA ∧ s.readReg64 .x2 = x.v ∧
      x.bs.length + (Proto.encodeMessage EpochDirectionPB.encodeRaw x.tag x.dir).length ≤ x.cap.toNat⌝ ∗
      epochDirectionPBPinnedAt A x.g x.dirA x.dir ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      epochDirectionPBPinnedAt A x.g x.dirA x.dir ∗
      vecU8At A x.v x.cap x.ptr
        (x.bs ++ Proto.encodeMessage EpochDirectionPB.encodeRaw x.tag x.dir) ∗ A.pool ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

/-- Ghost state for exact-capacity `encode<Authenticator> [local#2]` (`0x522c0`) calls. -/
structure EtvEncodeAuthGhost where
  authA : BitVec 64
  g : AuthenticatorPBGhost
  auth : AuthenticatorPB
  v : BitVec 64
  cap : BitVec 64
  ptr : BitVec 64
  bs : List (BitVec 8)

/-- Exact-capacity `encode<Authenticator> [local#2]` (`0x522c0`) contract at `s.sp = sp - 144#64`. -/
@[expose] def authEncodeExactSpecOf (resStack : Nat) (A : RustAlloc) : Spec EtvEncodeAuthGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.authA ∧ s.readReg64 .x1 = x.v ∧
      x.bs.length + (Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 x.auth).length ≤ x.cap.toNat⌝ ∗
      authenticatorPBPinnedAt A x.g x.authA x.auth ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗ A.pool ∗
      stackAt s.sp (encodeToVecCalleeStackOf resStack)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      authenticatorPBPinnedAt A x.g x.authA x.auth ∗
      vecU8At A x.v x.cap x.ptr
        (x.bs ++ Proto.encodeMessage ProtoAuthenticator.encodeRaw 2#32 x.auth) ∗ A.pool ∗
      stackAt s0.sp (encodeToVecCalleeStackOf resStack)
  onPanic := fun _ s0 sf => encodeToVecOnPanic s0 sf

theorem encodeVarint_length_pos (v : BitVec 64) : 0 < (Proto.encodeVarint v).length := by
  have h := protoEncodedLenVarint_eq_varintLen v
  unfold Proto.encodedLenVarint at h
  have hb := (varintLen_bounds v).1
  omega

theorem memRegion_four_eq (a : BitVec 64) : memRegion a 4 = ∃∗ v : BitVec 32, a ↦₃₂ v :=
  IsBlock.eq (IsBlock.memRegion a 4)
    (IsBlock.sepExists fun v => IsBlock.pointsTo32 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem exists_pointsTo64_eq_pointsTo32 (a : BitVec 64) :
    (∃∗ v : BitVec 64, a ↦₆₄ v) =
      (∃∗ v_hi : BitVec 32, ∃∗ v_lo : BitVec 32, (a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi)) := by
  rw [← memRegion_eight_eq a,
    memRegion_split' (b := a) (b' := a + 4#64) (n := 4) (k := 4) (by decide) rfl (by decide),
    memRegion_four_eq a, memRegion_four_eq (a + 4#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem pointsTo64_entails_pointsTo32_pair (a v : BitVec 64) :
    (a ↦₆₄ v) ⊢ ∃∗ v_hi : BitVec 32, ∃∗ v_lo : BitVec 32, (a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) := by
  rw [← exists_pointsTo64_eq_pointsTo32 a]
  exact Entails.sepExists_right v (Entails.refl _)

theorem pointsTo32_pair_entails_exists_pointsTo64 (a : BitVec 64) (v_lo v_hi : BitVec 32) :
    (a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) ⊢ ∃∗ v : BitVec 64, a ↦₆₄ v := by
  rw [exists_pointsTo64_eq_pointsTo32 a]
  exact Entails.sepExists_right v_hi (Entails.sepExists_right v_lo (Entails.refl _))

theorem sepWPp_split_pointsTo64 {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} (a v : BitVec 64) (F : SepProp)
    (hP : P = (a ↦₆₄ v) ∗ F)
    (h : ∀ v_lo v_hi : BitVec 32,
      SepWPp prog ret s ((a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hP
  refine SepWPp.weaken_pre (sepConj_mono_left (pointsTo64_entails_pointsTo32_pair a v)) ?_
  simp only [sepExists_sepConj_left]
  exact SepWPp.exists_elim fun v_hi => SepWPp.exists_elim fun v_lo =>
    SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (h v_lo v_hi)

theorem sepWPp_merge_pointsTo32 {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop} (a : BitVec 64) (v_lo v_hi : BitVec 32) (F : SepProp)
    (hP : P = (a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) ∗ F)
    (h : ∀ v : BitVec 64, SepWPp prog ret s ((a ↦₆₄ v) ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hP
  have hent : (a ↦₃₂ v_lo) ∗ ((a + 4#64) ↦₃₂ v_hi) ∗ F ⊢ (∃∗ v : BitVec 64, a ↦₆₄ v) ∗ F := by
    rw [← sepConj_assoc]
    exact sepConj_mono_left (pointsTo32_pair_entails_exists_pointsTo64 a v_lo v_hi)
  refine SepWPp.weaken_pre hent ?_
  simp only [sepExists_sepConj_left]
  exact SepWPp.exists_elim h

theorem vecU8Buf_eq_of_nonempty (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hne : bs.isEmpty = false) (hle : bs.length ≤ cap.toNat) :
    EncodedLen.vecU8Buf A cap ptr bs =
      (ptr ↦ₛ bs) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          A.live ptr cap.toNat 1 ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  have hpos : 0 < bs.length := List.length_pos_of_ne_nil (List.isEmpty_eq_false_iff.mp hne)
  have hcap_ne : cap ≠ 0 := by
    intro heq; subst heq; change bs.length ≤ 0 at hle; omega
  unfold EncodedLen.vecU8Buf
  simp only [hcap_ne, ↓reduceIte]
  ac_rfl

end CryptoVerification.SpqrV1.Prost.EncodeToVec
