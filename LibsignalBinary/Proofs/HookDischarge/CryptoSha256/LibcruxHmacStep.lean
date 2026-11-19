/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64
public import ProofLib
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclPure -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode -- proof-setup: allow-public-import
-- proof-setup: allow-public-import
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift
import LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacFetch
import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Pure HMAC equivalence and segment proofs for `libcrux_hmac::hmac`

Proves the pure functional equivalence and initial machine-code segments for block `6`
(`libcrux_hmac::hmac`, `w0 = 0` SHA-256 arm):

1. `libcruxHmacPure_eq_hmacWith`: matches `libcrux_hmac::hmac` (`Algorithm::Sha256`) against
   `CryptoGames.HMAC.hmacWith sha256CompressState` across all four cases of `key.length ≤ 64` vs
   `64 < key.length` and `data = []` vs `0 < data.length`.
2. Intermediate contracts and machine-code segment proofs parameterized over
   `HaclSubroutines P mpl`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacStep

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState sha256IV toBEBytes chunks64 sha256With hmacWith)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.Sha256Math (sha256CompressState)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclPure
  (sha256With_length haclUpdateLastState haclHash256Pure_eq_sha256With
   hmacInnerEmpty_eq_sha256With hmacInnerNonEmpty_eq_sha256With hmacOuter_eq_sha256With)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclCode
  (libcruxHmacLib HaclPlacement rustAllocShimSym rustAllocZeroedSym rustAllocSym rustDeallocSym
   memcpySym rustHandleErrorSym rustUnwrapFailedSym hash256Sym sha256InitSym
   sha256UpdateNblocksSym sha256UpdateLastSym sha256FinishSym)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.HaclContracts
  (HaclInProg HaclSubroutines withHaclPreserved sepWP_block_seg sepWPp_block_seg
   sepWPp_block_bl sepWPp_block_bl_panic sha256InitRawSpec sha256UpdateNblocksSpec
   sha256UpdateLastSpec sha256FinishRawSpec hash256Spec)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.StepsLift
  (ProcessFieldsPreserved_toHeapVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacFetch
  (haclPl6 haclPC6 haclPC6_eq_blockProgram haclPl6_base)
open CryptoVerification.RustHeap (RustAlloc vecU8 vecU8At vecHeader allocHookStack)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (rustAllocShimVmSpec allocMemcpyVmSpec rustHandleErrorPanicSpec rustHandleErrorPanic_of_extern
   RustStdAllocAuxEntries)

arm64_proof_prelude

/-! ## 1. Pure `libcrux_hmac::hmac` Equivalence (`libcruxHmacPure_eq_hmacWith`) -/

/-- Pure streaming model of `libcrux_hmac::hmac` (`Algorithm::Sha256`, `w0 = 0`):
1. Key preparation into 64-byte zeroed `k₀`: either `key ++ 0^(64 - key.length)` (`key.length ≤ 64`)
   or `hash_256(key) ++ 0^32` (`64 < key.length`).
2. `ipad = k₀.map (· ^^^ 0x36#8)`, `opad = k₀.map (· ^^^ 0x5c#8)`.
3. Inner SHA-256: `sha256_update_last(64, ipad, sha256IV)` when `data = []`, or
   `sha256_update_nblocks(64, ipad)` + `sha256_update_nblocks(nblk, data)` +
   `sha256_update_last(64 + data.length, data.drop nblk)` when `0 < data.length`.
4. Outer SHA-256: `sha256_update_nblocks(64, opad)` + `sha256_update_last(96, inner)`. -/
@[expose] def libcruxHmacKeyBlock (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) : List (BitVec 8) :=
  if 64 < key.length then
    let nbytes := 64 * (key.length / 64)
    (haclUpdateLastState F key.length (key.drop nbytes)
      ((chunks64 (key.take nbytes)).foldl F sha256IV)).toList.flatMap (toBEBytes 4) ++
      List.replicate 32 0#8
  else
    key ++ List.replicate (64 - key.length) 0#8

@[expose] def libcruxHmacInnerPure (F : ShaState → List (BitVec 8) → ShaState)
    (ipad data : List (BitVec 8)) : List (BitVec 8) :=
  if data.isEmpty then
    (haclUpdateLastState F 64 ipad sha256IV).toList.flatMap (toBEBytes 4)
  else
    let nblk := 64 * ((data.length - 1) / 64)
    (haclUpdateLastState F (64 + data.length) (data.drop nblk)
      ((chunks64 (data.take nblk)).foldl F (F sha256IV ipad))).toList.flatMap (toBEBytes 4)

@[expose] def libcruxHmacPure (F : ShaState → List (BitVec 8) → ShaState)
    (key data : List (BitVec 8)) : List (BitVec 8) :=
  let k₀ := libcruxHmacKeyBlock F key
  let ipad := k₀.map (· ^^^ 0x36#8)
  let opad := k₀.map (· ^^^ 0x5c#8)
  let inner := libcruxHmacInnerPure F ipad data
  (haclUpdateLastState F 96 inner (F sha256IV opad)).toList.flatMap (toBEBytes 4)

theorem libcruxHmacKeyBlock_eq (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) :
    libcruxHmacKeyBlock F key =
      (let k' := if 64 < key.length then sha256With F key else key
       k' ++ List.replicate (64 - k'.length) 0) := by
  unfold libcruxHmacKeyBlock
  have h0 : (0 : BitVec 8) = 0#8 := rfl
  rw [h0]
  by_cases hgt : 64 < key.length
  · simp only [hgt, ↓reduceIte]
    rw [haclHash256Pure_eq_sha256With F key, sha256With_length F key]
  · simp only [hgt, ↓reduceIte]

theorem libcruxHmacKeyBlock_length (F : ShaState → List (BitVec 8) → ShaState)
    (key : List (BitVec 8)) :
    (libcruxHmacKeyBlock F key).length = 64 := by
  unfold libcruxHmacKeyBlock
  by_cases hgt : 64 < key.length
  · simp only [hgt, ↓reduceIte, List.length_append, List.length_replicate]
    rw [haclHash256Pure_eq_sha256With F key, sha256With_length F key]
  · simp only [hgt, ↓reduceIte, List.length_append, List.length_replicate]
    omega

theorem libcruxHmacInnerPure_eq_sha256With (F : ShaState → List (BitVec 8) → ShaState)
    (ipad data : List (BitVec 8)) (hipad : ipad.length = 64) :
    libcruxHmacInnerPure F ipad data = sha256With F (ipad ++ data) := by
  unfold libcruxHmacInnerPure
  rcases data with _ | ⟨b, bs⟩
  · simp only [List.isEmpty_nil, ↓reduceIte]
    exact hmacInnerEmpty_eq_sha256With F ipad hipad
  · simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    exact hmacInnerNonEmpty_eq_sha256With F ipad (b :: bs) hipad (by simp)

/-- Pure equivalence for `libcrux_hmac::hmac` (`w0 = 0` SHA-256 arm) across all four
`(key.length ≤ 64` vs `64 < key.length) × (data = []` vs `0 < data.length)` cases. -/
theorem libcruxHmacPure_eq_hmacWith (key data : List (BitVec 8)) :
    libcruxHmacPure sha256CompressState key data =
      hmacWith sha256CompressState key data := by
  unfold libcruxHmacPure hmacWith
  dsimp only
  have hk0_len : (libcruxHmacKeyBlock sha256CompressState key).length = 64 :=
    libcruxHmacKeyBlock_length sha256CompressState key
  have hipad_len : ((libcruxHmacKeyBlock sha256CompressState key).map (· ^^^ 0x36#8)).length = 64 := by
    rw [List.length_map, hk0_len]
  have hopad_len : ((libcruxHmacKeyBlock sha256CompressState key).map (· ^^^ 0x5c#8)).length = 64 := by
    rw [List.length_map, hk0_len]
  rw [libcruxHmacInnerPure_eq_sha256With sha256CompressState _ data hipad_len]
  rw [hmacOuter_eq_sha256With sha256CompressState _ _ hopad_len
      (sha256With_length sha256CompressState _)]
  rw [libcruxHmacKeyBlock_eq sha256CompressState key]
  rfl

/-! ## 2. Stack Splitting, 224-Byte Frame, and SIMD / Byte-Slice Helpers -/

private theorem stackAt_split_const (sp : BitVec 64) (a b : Nat)
    (h : a + b ≤ 2 ^ 64) :
    stackAt sp (a + b) =
      stackAt sp a ∗ stackAt (sp - BitVec.ofNat 64 a) b := by
  rw [stackAt_eq_stackFrameAt sp (a + b) h,
      stackFrameAt_split sp a b h,
      ← stackAt_eq_stackFrameAt sp a (by omega),
      ← stackAt_eq_stackFrameAt (sp - BitVec.ofNat 64 a) b (by omega)]

/-- Split `extHookStack` (`16384` B) into Block 6's `224`-B local frame, a `4096`-B call area
(`allocHookStack`, which also dominates `hash_256`'s `480` B), and `12064` B of preserved slack. -/
theorem stackAt_split_hmac (sp : BitVec 64) :
    stackAt sp 16384 =
      stackAt sp 224 ∗ (stackAt (sp - 224#64) 4096 ∗ stackAt (sp - 4320#64) 12064) := by
  have h1 := stackAt_split_const sp 224 16160 (by decide)
  have h2 := stackAt_split_const (sp - 224#64) 4096 12064 (by decide)
  have hsub : sp - 224#64 - 4096#64 = sp - 4320#64 := by bv_omega
  change stackAt sp (224 + 16160) = _
  rw [h1, show (16160 : Nat) = 4096 + 12064 from rfl, h2]
  dsimp only [BitVec.ofNat] at hsub ⊢
  rw [hsub]

theorem stackAt_4096_split_480 (sp : BitVec 64) :
    stackAt sp 4096 = stackFrameAt sp 480 ∗ stackAt (sp - 480#64) 3616 := by
  rw [show (4096 : Nat) = 480 + 3616 from rfl, stackAt_split_const sp 480 3616 (by decide),
      stackAt_eq_stackFrameAt sp 480 (by decide)]

theorem stackAt_4096_split_352 (sp : BitVec 64) :
    stackAt sp 4096 = stackFrameAt sp 352 ∗ stackAt (sp - 352#64) 3744 := by
  rw [show (4096 : Nat) = 352 + 3744 from rfl, stackAt_split_const sp 352 3744 (by decide),
      stackAt_eq_stackFrameAt sp 352 (by decide)]

theorem stackAt_4096_split_224 (sp : BitVec 64) :
    stackAt sp 4096 = stackFrameAt sp 224 ∗ stackAt (sp - 224#64) 3872 := by
  rw [show (4096 : Nat) = 224 + 3872 from rfl, stackAt_split_const sp 224 3872 (by decide),
      stackAt_eq_stackFrameAt sp 224 (by decide)]

theorem stackAt_4096_split_16 (sp : BitVec 64) :
    stackAt sp 4096 = stackFrameAt sp 16 ∗ stackAt (sp - 16#64) 4080 := by
  rw [show (4096 : Nat) = 16 + 4080 from rfl, stackAt_split_const sp 16 4080 (by decide),
      stackAt_eq_stackFrameAt sp 16 (by decide)]

/-- Saved callee-saved GPR slots at `[sp1 + 128 .. sp1 + 224)` (`sp1 := s0.sp - 224#64`). -/
@[expose] def hmacSavedCalleeRegs (sp1 : BitVec 64) (s0 : State) (pad152 : BitVec 64) : SepProp :=
  ((sp1 + 128#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp1 + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp1 + 144#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp1 + 152#64) ↦₆₄ pad152) ∗
  ((sp1 + 160#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp1 + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp1 + 176#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp1 + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp1 + 192#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp1 + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp1 + 208#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp1 + 216#64) ↦₆₄ s0.readReg64 .x19)

private theorem pointsTo64_replicate8 (a : BitVec 64) (b : BitVec 8) (w : BitVec 64)
    (hw : unpack64 w = List.replicate 8 b) :
    (a ↦₆₄ w) = (a ↦ₛ List.replicate 8 b) := by
  rw [pointsTo64_eq_pointsToBytes, hw]

private theorem pointsTo64_4_replicate32 (a : BitVec 64) (b : BitVec 8) (w : BitVec 64)
    (hw : unpack64 w = List.replicate 8 b) :
    ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ w) ∗ ((a + 16#64) ↦₆₄ w) ∗ ((a + 24#64) ↦₆₄ w)) =
      (a ↦ₛ List.replicate 32 b) := by
  have h8 := fun p => pointsTo64_replicate8 p b w hw
  rw [h8 a, h8 (a + 8#64), h8 (a + 16#64), h8 (a + 24#64)]
  have hrep16 : List.replicate 16 b = List.replicate 8 b ++ List.replicate 8 b := rfl
  have hrep32 : List.replicate 32 b = List.replicate 16 b ++ List.replicate 16 b := rfl
  rw [hrep32, pointsToBytes_append, List.length_replicate,
      hrep16, pointsToBytes_append, pointsToBytes_append, List.length_replicate]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem pointsTo64_8_replicate64 (a : BitVec 64) (b : BitVec 8) (w : BitVec 64)
    (hw : unpack64 w = List.replicate 8 b) :
    ((a ↦₆₄ w) ∗ ((a + 8#64) ↦₆₄ w) ∗ ((a + 16#64) ↦₆₄ w) ∗ ((a + 24#64) ↦₆₄ w) ∗
     ((a + 32#64) ↦₆₄ w) ∗ ((a + 40#64) ↦₆₄ w) ∗ ((a + 48#64) ↦₆₄ w) ∗ ((a + 56#64) ↦₆₄ w)) =
      (a ↦ₛ List.replicate 64 b) := by
  have hlo := pointsTo64_4_replicate32 a b w hw
  have hhi := pointsTo64_4_replicate32 (a + 32#64) b w hw
  have hrep64 : List.replicate 64 b = List.replicate 32 b ++ List.replicate 32 b := rfl
  rw [hrep64, pointsToBytes_append, List.length_replicate]
  change _ = (a ↦ₛ List.replicate 32 b) ∗ ((a + 32#64) ↦ₛ List.replicate 32 b)
  rw [← hlo, ← hhi]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- The two `stp x8, x9` stores at `+0x444` and `+0x468` initialize `[sp1 + 64 .. sp1 + 96)` with
`CryptoVerification.LibsignalHmac.shaStateBytes sha256IV`. -/
theorem pointsTo64_4_sha256IV (a : BitVec 64) :
    ((a ↦₆₄ 0xbb67ae856a09e667#64) ∗
     ((a + 8#64) ↦₆₄ 0xa54ff53a3c6ef372#64) ∗
     ((a + 16#64) ↦₆₄ 0x9b05688c510e527f#64) ∗
     ((a + 24#64) ↦₆₄ 0x5be0cd191f83d9ab#64)) =
      (a ↦ₛ CryptoVerification.LibsignalHmac.shaStateBytes sha256IV) := by
  have hiv : CryptoVerification.LibsignalHmac.shaStateBytes sha256IV =
      unpack64 0xbb67ae856a09e667#64 ++ unpack64 0xa54ff53a3c6ef372#64 ++
      unpack64 0x9b05688c510e527f#64 ++ unpack64 0x5be0cd191f83d9ab#64 := by decide
  rw [hiv, List.append_assoc (unpack64 _ ++ unpack64 _), pointsToBytes_append]
  have h16 : (unpack64 0xbb67ae856a09e667#64 ++ unpack64 0xa54ff53a3c6ef372#64).length = 16 := by
    decide
  rw [h16, pointsToBytes_append, pointsToBytes_append,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
  simp only [unpack64_length, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ## 3. BitVec Arithmetic for `u32::try_from` and Non-Empty `data` Block Split -/

/-- `u32::try_from(key.len())` niche encoding at `+0x020..+0x048`:
`x25 = if (x2 >>> 32 != 0) then 0x201 else (0x200 ||| (x2 <<< 32))`.
Bit 0 is `1` iff `2 ^ 32 ≤ x2.toNat`; otherwise `x25 >>> 32 = x2`. -/
@[expose] def tryFromKeyNiche (x2 : BitVec 64) : BitVec 64 :=
  if (x2 >>> 32) != 0#64 then 513#64 else 512#64 ||| (x2 <<< 32)

theorem tryFromKeyNiche_bit0_iff (x2 : BitVec 64) :
    ((tryFromKeyNiche x2).setWidth 32 &&& 1#32 != 0#32) = decide (2 ^ 32 ≤ x2.toNat) := by
  unfold tryFromKeyNiche
  by_cases hhi : (x2 >>> 32) = 0#64
  · have hlt : x2.toNat < 2 ^ 32 := by bv_omega
    have hnot : ¬ (2 ^ 32 ≤ x2.toNat) := by omega
    simp only [hhi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hnot, decide_false]
    have h0 : (512#64 ||| x2 <<< 32).setWidth 32 &&& 1#32 = 0#32 := by bv_bits
    simp only [h0, bne_self_eq_false]
  · have hge : 2 ^ 32 ≤ x2.toNat := by bv_omega
    have htr : ((x2 >>> 32) != 0#64) = true := bne_iff_ne.mpr hhi
    simp only [htr, ↓reduceIte, hge, decide_true]
    decide

theorem tryFromKeyNiche_lsr32 (x2 : BitVec 64) (hlt : x2.toNat < 2 ^ 32) :
    tryFromKeyNiche x2 >>> 32 = x2 := by
  unfold tryFromKeyNiche
  have hhi : (x2 >>> 32) = 0#64 := by bv_omega
  simp only [hhi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  have hbits : (512#64 ||| x2 <<< 32) >>> 32 = (x2 <<< 32) >>> 32 := by bv_bits
  rw [hbits]
  bv_omega

/-- `u32::try_from(data.len())` niche encoding at `+0x0e4..+0x0f4`:
`x26 = if (x21 >>> 32 != 0) then 0x201 else (x21 <<< 32)`. -/
@[expose] def tryFromDataNiche (x21 : BitVec 64) : BitVec 64 :=
  if (x21 >>> 32) != 0#64 then 513#64 else x21 <<< 32

theorem tryFromDataNiche_bit0_iff (x21 : BitVec 64) :
    ((tryFromDataNiche x21).setWidth 32 &&& 1#32 != 0#32) = decide (2 ^ 32 ≤ x21.toNat) := by
  unfold tryFromDataNiche
  by_cases hhi : (x21 >>> 32) = 0#64
  · have hlt : x21.toNat < 2 ^ 32 := by bv_omega
    have hnot : ¬ (2 ^ 32 ≤ x21.toNat) := by omega
    simp only [hhi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hnot, decide_false]
    have h0 : (x21 <<< 32).setWidth 32 &&& 1#32 = 0#32 := by bv_bits
    simp only [h0, bne_self_eq_false]
  · have hge : 2 ^ 32 ≤ x21.toNat := by bv_omega
    have htr : ((x21 >>> 32) != 0#64) = true := bne_iff_ne.mpr hhi
    simp only [htr, ↓reduceIte, hge, decide_true]
    decide

theorem tryFromDataNiche_lsr32 (x21 : BitVec 64) (hlt : x21.toNat < 2 ^ 32) :
    tryFromDataNiche x21 >>> 32 = x21 := by
  unfold tryFromDataNiche
  have hhi : (x21 >>> 32) = 0#64 := by bv_omega
  simp only [hhi, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  bv_omega

private theorem bv32_and_63_toNat (v : BitVec 32) : (v &&& 63#32).toNat = v.toNat % 64 := by
  have heq : v &&& 63#32 = v % 64#32 := by bv_bits
  rw [heq, BitVec.toNat_umod]
  rfl

/-- Non-empty `data` block/remainder arithmetic (`+0x470..+0x4b4`): for `1 ≤ L < 2 ^ 32`,
`nblk = 64 * ((L - 1) / 64)` and `remLen = L - nblk` (`1 ≤ remLen ≤ 64`). -/
theorem hmac_nonempty_nblk_arith {L : Nat} (hpos : 0 < L) (hlt32 : L < 2 ^ 32) :
    let w26 : BitVec 32 := BitVec.ofNat 32 L
    let w11 : BitVec 32 := w26 >>> 6
    let w8  : BitVec 32 := w11 - 1#32
    let c_hs : Bool := w11 ≥ 1#32
    let w9  : BitVec 32 := w26 &&& 63#32
    let c_eq : Bool := w9 == 0#32
    let cond : Bool := c_hs && c_eq
    let w11' : BitVec 32 := if cond then w8 else w11
    let w25  : BitVec 32 := w11' <<< 6
    let w8_sub : BitVec 32 := w26 - (w8 <<< 6)
    let w26' : BitVec 32 := if cond then w8_sub else w9
    let nblk : Nat := 64 * ((L - 1) / 64)
    w25.toNat = nblk ∧
    w26'.toNat = L - nblk ∧
    nblk < L ∧
    1 ≤ L - nblk ∧
    L - nblk ≤ 64 := by
  dsimp only
  have hw26 : (BitVec.ofNat 32 L).toNat = L := Nat.mod_eq_of_lt hlt32
  have hlsr : (BitVec.ofNat 32 L >>> 6).toNat = L / 64 := by
    rw [BitVec.toNat_ushiftRight, hw26, Nat.shiftRight_eq_div_pow]
  have hand : (BitVec.ofNat 32 L &&& 63#32).toNat = L % 64 := by
    rw [bv32_and_63_toNat, hw26]
  have hge_iff : ((BitVec.ofNat 32 L >>> 6) ≥ 1#32 : Prop) ↔ L / 64 ≥ 1 := by
    change (1#32 ≤ BitVec.ofNat 32 L >>> 6) ↔ L / 64 ≥ 1
    rw [BitVec.le_def, hlsr]
    rfl
  have hdec : decide ((BitVec.ofNat 32 L >>> 6) ≥ 1#32) = decide (L / 64 ≥ 1) :=
    decide_eq_decide.mpr hge_iff
  have hnblk_lt : 64 * ((L - 1) / 64) < L := by omega
  have hrem_lo : 1 ≤ L - 64 * ((L - 1) / 64) := by omega
  have hrem_hi : L - 64 * ((L - 1) / 64) ≤ 64 := by omega
  by_cases hrem : L % 64 = 0
  · have hge1 : L / 64 ≥ 1 := by omega
    have hmask : (BitVec.ofNat 32 L &&& 63#32 == 0#32) = true := by
      apply beq_iff_eq.mpr
      apply BitVec.eq_of_toNat_eq
      rw [hand, hrem]
      rfl
    have hsub1 : ((BitVec.ofNat 32 L >>> 6) - 1#32).toNat = L / 64 - 1 := by
      rw [BitVec.toNat_sub_of_le]
      · rw [hlsr]; rfl
      · rw [BitVec.le_def, hlsr]; exact hge1
    have hshl : (((BitVec.ofNat 32 L >>> 6) - 1#32) <<< 6).toNat = (L / 64 - 1) * 64 := by
      rw [BitVec.toNat_shiftLeft, hsub1, Nat.shiftLeft_eq]
      exact Nat.mod_eq_of_lt (by omega)
    refine ⟨?_, ?_, hnblk_lt, hrem_lo, hrem_hi⟩
    · rw [hdec]
      simp only [hge1, decide_true, hmask, Bool.and_self, ↓reduceIte, hshl]
      omega
    · rw [hdec]
      simp only [hge1, decide_true, hmask, Bool.and_self, ↓reduceIte]
      rw [BitVec.toNat_sub_of_le]
      · rw [hw26, hshl]; omega
      · rw [BitVec.le_def, hw26, hshl]; omega
  · have hmask : (BitVec.ofNat 32 L &&& 63#32 == 0#32) = false := by
      apply beq_false_of_ne
      intro heq
      have ht := congrArg BitVec.toNat heq
      rw [hand] at ht
      exact hrem ht
    refine ⟨?_, ?_, hnblk_lt, hrem_lo, hrem_hi⟩
    · rw [hdec]
      simp only [hmask, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      rw [BitVec.toNat_shiftLeft, hlsr, Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [hdec]
      simp only [hmask, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hand]
      omega

/-! ## 4. Auxiliary Callee Bundle, 224-Byte Frame Decomposition, and `vecU8` Packing -/

/-- `memcpy` contract accepting `4096` B of stack so both hook-free `allocMemcpyVmSpec` (`0` stack)
and hook `memcpySpec` (`memHookStack ≤ 4096` B) satisfy it. -/
@[expose] def hmacMemcpyVmSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
      s0.readReg64 .x1 = src ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
      (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ stackAt s0.sp 4096)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ LibsignalBinary.Heap.VmPreserved s0 sf ∧ sf.trace = s0.trace ∧
      sf.fs = s0.fs⌝ ∗
      ((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ stackAt s0.sp 4096)

/-- Auxiliary non-allocator, non-HACL callees invoked by Block 6 (`libcrux_hmac::hmac`). -/
structure HmacAuxSubroutines (P : Program) (mpl : Obj.MultiPlacement) : Prop where
  shim_ok         : subroutine_ok P (mpl.ρ rustAllocShimSym) rustAllocShimVmSpec
  memcpy_ok       : subroutine_ok P (mpl.ρ memcpySym) hmacMemcpyVmSpec
  handleError_ok  : subroutine_ok P (mpl.ρ rustHandleErrorSym) rustHandleErrorPanicSpec
  unwrapFailed_ok : subroutine_ok P (mpl.ρ rustUnwrapFailedSym) rustHandleErrorPanicSpec

/-- Build `HmacAuxSubroutines` from `RustStdAllocAuxEntries` + `unwrap_failed` mapped to
`Rust.panicked`. -/
theorem HmacAuxSubroutines.of_rustStdAllocAux {P : Program} {mpl : Obj.MultiPlacement}
    (hAux : RustStdAllocAuxEntries P (mpl.ρ rustAllocShimSym) (mpl.ρ memcpySym)
      (mpl.ρ rustHandleErrorSym))
    (hUnwrap : P.externAt? (mpl.ρ rustUnwrapFailedSym) = some Rust.panicked) :
    HmacAuxSubroutines P mpl where
  shim_ok := hAux.shim_ok
  memcpy_ok := by
    apply subroutine_ok.of_codeLoaded
    rintro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp _
    dsimp only [hmacMemcpyVmSpec] at hpre
    have hpre' : s0.mem ⊨ allocMemcpyVmSpec.pre (dst, src, bs) s0 ∗ (stackAt s0.sp 4096 ∗ R) := by
      dsimp only [allocMemcpyVmSpec]
      simpa only [sepConj_assoc] using hpre
    refine subroutine_ok.mono_outcome hAux.memcpy_ok (dst, src, bs) (stackAt s0.sp 4096 ∗ R)
      s0 hpc hrun hpre' hsp ?_
    rintro sf (⟨hret, hcc, hpost⟩ | ⟨hp, hpan⟩ | ⟨c, hc, hex⟩ | ⟨ho, hoom⟩)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [allocMemcpyVmSpec] at hpost
      dsimp only [hmacMemcpyVmSpec]
      rw [← sepConj_assoc] at hpost
      refine Satisfies.mono (sepConj_mono_left ?_) hpost
      rw [sepConj_assoc]
      refine Entails.pure_left fun ⟨hx0, hacp, hvm⟩ => ?_
      exact Entails.pure_right ⟨hx0, hvm, hacp.2.1, hacp.1⟩ (Entails.of_eq (by sep_ac_rfl))
    · exact Or.inr (Or.inl ⟨hp, by simp [allocMemcpyVmSpec] at hpan⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨c, hc, by simp [allocMemcpyVmSpec] at hex⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ho, by simp [allocMemcpyVmSpec] at hoom⟩))
  handleError_ok := hAux.handleError_ok
  unwrapFailed_ok := rustHandleErrorPanic_of_extern hUnwrap

private theorem memRegion32_eq_exists_pts64 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) := by
  have h16 : ∀ p : BitVec 64, memRegion p 16 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1)) := by
    intro p
    rw [show (16 : Nat) = 8 + 8 from rfl, memRegion_split p 8 8 (by decide),
        memRegion_eight, memRegion_eight, sepExists_sepConj_left]
    refine congrArg SepProp.sepExists (funext fun _ => ?_)
    rw [sepExists_sepConj_right]
  rw [show (32 : Nat) = 16 + 16 from rfl, memRegion_split a 16 16 (by decide),
      h16 a, h16 (a + 16#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [sepExists_sepConj_left]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_left]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  rw [sepExists_sepConj_right]
  refine congrArg SepProp.sepExists (funext fun _ => ?_)
  simp only [sepConj_assoc]

theorem pts64_4_entails_memRegion32 (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3)) ⊢
      memRegion a 32 := by
  rw [memRegion32_eq_exists_pts64 a]
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1
    (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.refl _))))

/-- Pack a freshly allocated 32-byte tag buffer into `vecU8 A ret bs` (`bs.length = 32`). -/
theorem vecU8_pack_32 (A : RustAlloc) (ret pOut : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 32) (hne0 : pOut ≠ 0#64) :
    (((ret ↦₆₄ 32#64) ∗ ((ret + 8#64) ↦₆₄ pOut) ∗ ((ret + 16#64) ↦₆₄ 32#64)) ∗
      A.live pOut 32 1 ∗ (pOut ↦ₛ bs)) ⊢ vecU8 A ret bs := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.sepExists_right 32#64 (Entails.sepExists_right pOut ?_)
  have hcapNe : (32#64 : BitVec 64) ≠ 0 := by decide
  have hpOutNe : pOut ≠ 0 := hne0
  simp only [hlen, hcapNe, ↓reduceIte]
  have hcapNat : (32#64 : BitVec 64).toNat = 32 := rfl
  have hsub0 : (32#64 : BitVec 64).toNat - 32 = 0 := rfl
  rw [hsub0, memRegion_zero, sepConj_emp, hcapNat]
  have hpure : 32 ≤ 32 ∧ 32 < 2 ^ 63 ∧ pOut ≠ 0 := ⟨Nat.le_refl 32, by decide, hpOutNe⟩
  change (((ret ↦₆₄ 32#64) ∗ ((ret + 8#64) ↦₆₄ pOut) ∗ ((ret + 16#64) ↦₆₄ 32#64)) ∗
      A.live pOut 32 1 ∗ (pOut ↦ₛ bs)) ⊢
    (((ret ↦₆₄ 32#64) ∗ ((ret + 8#64) ↦₆₄ pOut) ∗ ((ret + 16#64) ↦₆₄ 32#64)) ∗
      ⌜32 ≤ 32 ∧ 32 < 2 ^ 63 ∧ pOut ≠ 0⌝ ∗ (A.live pOut 32 1 ∗ (pOut ↦ₛ bs)))
  refine Entails.trans (Entails.pure_right hpure (Entails.refl _)) (Entails.of_eq (by sep_ac_rfl))

/-! ## 5. Machine-Code Panic & OOM Stubs (`+0x9e8`, `+0xa84`, `+0xa20`) -/

theorem hmac_seg_oom_key [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 268#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 2544#64) s R
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = 64#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 268#64 := hpc
  clear hpc
  have hx0_gpr : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 3
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

theorem hmac_seg_oom_ipad [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 928#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 2544#64) s R
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = 64#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 928#64 := hpc
  clear hpc
  have hx0_gpr : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 3
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

theorem hmac_seg_oom_opad [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 1004#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 2544#64) s R
      (fun sf P' =>
        (sf.sp = s.sp ∧ sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = 64#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 1004#64 := hpc
  clear hpc
  have hx0_gpr : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 3
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

theorem hmac_seg_unwrap_pre [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 2592#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 2632#64) s (memRegion (s.sp + 64#64) 32 ∗ R)
      (fun sf P' => (sf.sp = s.sp) ∧ (P' ⊢ memRegion (s.sp + 64#64) 32 ∗ R)) := by
  have hpc' : s.pc = haclPl6.base + 2592#64 := hpc
  clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  rw [show (32 : Nat) = 1 + 31 from rfl, memRegion_split (s.sp + 64#64) 1 31 (by decide),
      memRegion_one, sepExists_sepConj_left, sepExists_sepConj_left]
  refine SepWP.exists_elim fun b64 => ?_
  wp_simp_pre only [sepConj_assoc]
  wp_sym_steps 10
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun]) ⟨by simp [wp_norm], ?_⟩
  rw [← sepConj_assoc]
  exact Entails.sepExists_right 2#8 (Entails.refl _)

/-! ## 6. 224-Byte Frame Elimination & Prologue Segment (`+0x000 → +0x0fc` / `+0xa20`) -/

private theorem hmacStack224_eq (sp : BitVec 64) :
    let sp1 := sp - 224#64
    stackAt sp 224 =
      (memRegion sp1 32 ∗
       memRegion (sp1 + 32#64) 32 ∗
       memRegion (sp1 + 64#64) 32 ∗
       memRegion (sp1 + 96#64) 32 ∗
       memRegion (sp1 + 128#64) 32 ∗
       memRegion (sp1 + 160#64) 32 ∗
       memRegion (sp1 + 192#64) 32) := by
  dsimp only
  rw [stackAt_eq_stackFrameAt sp 224 (by decide), stackFrameAt_eq_memRegion sp 224 (by decide)]
  change memRegion (sp - 224#64) (32 + (32 + (32 + (32 + (32 + (32 + 32)))))) = _
  rw [memRegion_split _ 32 _ (by decide),
      memRegion_split _ 32 _ (by decide),
      memRegion_split _ 32 _ (by decide),
      memRegion_split _ 32 _ (by decide),
      memRegion_split _ 32 _ (by decide),
      memRegion_split _ 32 _ (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem memRegion32_elim {prog : Program} {target_pc : BitVec 64}
    {s : State} {a : BitVec 64} {R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ w0 w1 w2 w3 : BitVec 64,
      SepWP prog target_pc s
        ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗ R)
        post oom) :
    SepWP prog target_pc s (memRegion a 32 ∗ R) post oom := by
  rw [memRegion32_eq_exists_pts64 a, sepExists_sepConj_left]
  refine SepWP.exists_elim fun w0 => ?_
  rw [sepExists_sepConj_left]
  refine SepWP.exists_elim fun w1 => ?_
  rw [sepExists_sepConj_left]
  refine SepWP.exists_elim fun w2 => ?_
  rw [sepExists_sepConj_left]
  refine SepWP.exists_elim fun w3 => ?_
  simpa only [sepConj_assoc] using h w0 w1 w2 w3

private theorem hmacStack224_elim {prog : Program} {target_pc : BitVec 64}
    {s0 : State} {R : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ (t0 t1 t2 t3 st0 st1 st2 st3 c0 c1 c2 pad152 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64),
      let sp1 := s0.sp - 224#64
      SepWP prog target_pc s0
        ((sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
         ((sp1 + 64#64) ↦₆₄ st0) ∗ ((sp1 + 72#64) ↦₆₄ st1) ∗
         ((sp1 + 80#64) ↦₆₄ st2) ∗ ((sp1 + 88#64) ↦₆₄ st3) ∗
         ((sp1 + 128#64) ↦₆₄ c0) ∗ ((sp1 + 136#64) ↦₆₄ c1) ∗
         ((sp1 + 144#64) ↦₆₄ c2) ∗ ((sp1 + 152#64) ↦₆₄ pad152) ∗
         ((sp1 + 160#64) ↦₆₄ c4) ∗ ((sp1 + 168#64) ↦₆₄ c5) ∗
         ((sp1 + 176#64) ↦₆₄ c6) ∗ ((sp1 + 184#64) ↦₆₄ c7) ∗
         ((sp1 + 192#64) ↦₆₄ c8) ∗ ((sp1 + 200#64) ↦₆₄ c9) ∗
         ((sp1 + 208#64) ↦₆₄ c10) ∗ ((sp1 + 216#64) ↦₆₄ c11) ∗
         memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗ R) post oom) :
    SepWP prog target_pc s0 (stackAt s0.sp 224 ∗ R) post oom := by
  let sp1 := s0.sp - 224#64
  have heq : stackAt s0.sp 224 ∗ R =
      memRegion sp1 32 ∗ (memRegion (sp1 + 64#64) 32 ∗ (memRegion (sp1 + 128#64) 32 ∗
      (memRegion (sp1 + 160#64) 32 ∗ (memRegion (sp1 + 192#64) 32 ∗
      (memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗ R))))) := by
    rw [hmacStack224_eq s0.sp]
    dsimp only [sp1]
    sep_ac_rfl
  rw [heq]
  apply memRegion32_elim; intro t0 t1 t2 t3
  rw [show ((sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
      (memRegion (sp1 + 64#64) 32 ∗ (memRegion (sp1 + 128#64) 32 ∗
      (memRegion (sp1 + 160#64) 32 ∗ (memRegion (sp1 + 192#64) 32 ∗
      (memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗ R)))))) =
      memRegion (sp1 + 64#64) 32 ∗ ((sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗
      ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗ (memRegion (sp1 + 128#64) 32 ∗
      (memRegion (sp1 + 160#64) 32 ∗ (memRegion (sp1 + 192#64) 32 ∗
      (memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗ R))))) by sep_ac_rfl]
  apply memRegion32_elim; intro st0 st1 st2 st3
  rw [show (((sp1 + 64#64) ↦₆₄ st0) ∗ ((sp1 + 64#64 + 8#64) ↦₆₄ st1) ∗
      ((sp1 + 64#64 + 16#64) ↦₆₄ st2) ∗ ((sp1 + 64#64 + 24#64) ↦₆₄ st3) ∗
      ((sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
      (memRegion (sp1 + 128#64) 32 ∗ (memRegion (sp1 + 160#64) 32 ∗ (memRegion (sp1 + 192#64) 32 ∗
      (memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗ R)))))) =
      memRegion (sp1 + 128#64) 32 ∗ (((sp1 + 64#64) ↦₆₄ st0) ∗ ((sp1 + 64#64 + 8#64) ↦₆₄ st1) ∗
      ((sp1 + 64#64 + 16#64) ↦₆₄ st2) ∗ ((sp1 + 64#64 + 24#64) ↦₆₄ st3) ∗
      (sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
      (memRegion (sp1 + 160#64) 32 ∗ (memRegion (sp1 + 192#64) 32 ∗
      (memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗ R)))) by sep_ac_rfl]
  apply memRegion32_elim; intro c0 c1 c2 pad152
  rw [show (((sp1 + 128#64) ↦₆₄ c0) ∗ ((sp1 + 128#64 + 8#64) ↦₆₄ c1) ∗
      ((sp1 + 128#64 + 16#64) ↦₆₄ c2) ∗ ((sp1 + 128#64 + 24#64) ↦₆₄ pad152) ∗
      (((sp1 + 64#64) ↦₆₄ st0) ∗ ((sp1 + 64#64 + 8#64) ↦₆₄ st1) ∗
      ((sp1 + 64#64 + 16#64) ↦₆₄ st2) ∗ ((sp1 + 64#64 + 24#64) ↦₆₄ st3) ∗
      (sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
      (memRegion (sp1 + 160#64) 32 ∗ (memRegion (sp1 + 192#64) 32 ∗
      (memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗ R))))) =
      memRegion (sp1 + 160#64) 32 ∗ (((sp1 + 128#64) ↦₆₄ c0) ∗ ((sp1 + 128#64 + 8#64) ↦₆₄ c1) ∗
      ((sp1 + 128#64 + 16#64) ↦₆₄ c2) ∗ ((sp1 + 128#64 + 24#64) ↦₆₄ pad152) ∗
      ((sp1 + 64#64) ↦₆₄ st0) ∗ ((sp1 + 64#64 + 8#64) ↦₆₄ st1) ∗
      ((sp1 + 64#64 + 16#64) ↦₆₄ st2) ∗ ((sp1 + 64#64 + 24#64) ↦₆₄ st3) ∗
      (sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
      (memRegion (sp1 + 192#64) 32 ∗
      (memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗ R))) by sep_ac_rfl]
  apply memRegion32_elim; intro c4 c5 c6 c7
  rw [show (((sp1 + 160#64) ↦₆₄ c4) ∗ ((sp1 + 160#64 + 8#64) ↦₆₄ c5) ∗
      ((sp1 + 160#64 + 16#64) ↦₆₄ c6) ∗ ((sp1 + 160#64 + 24#64) ↦₆₄ c7) ∗
      (((sp1 + 128#64) ↦₆₄ c0) ∗ ((sp1 + 128#64 + 8#64) ↦₆₄ c1) ∗
      ((sp1 + 128#64 + 16#64) ↦₆₄ c2) ∗ ((sp1 + 128#64 + 24#64) ↦₆₄ pad152) ∗
      ((sp1 + 64#64) ↦₆₄ st0) ∗ ((sp1 + 64#64 + 8#64) ↦₆₄ st1) ∗
      ((sp1 + 64#64 + 16#64) ↦₆₄ st2) ∗ ((sp1 + 64#64 + 24#64) ↦₆₄ st3) ∗
      (sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
      (memRegion (sp1 + 192#64) 32 ∗
      (memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗ R)))) =
      memRegion (sp1 + 192#64) 32 ∗ (((sp1 + 160#64) ↦₆₄ c4) ∗ ((sp1 + 160#64 + 8#64) ↦₆₄ c5) ∗
      ((sp1 + 160#64 + 16#64) ↦₆₄ c6) ∗ ((sp1 + 160#64 + 24#64) ↦₆₄ c7) ∗
      ((sp1 + 128#64) ↦₆₄ c0) ∗ ((sp1 + 128#64 + 8#64) ↦₆₄ c1) ∗
      ((sp1 + 128#64 + 16#64) ↦₆₄ c2) ∗ ((sp1 + 128#64 + 24#64) ↦₆₄ pad152) ∗
      ((sp1 + 64#64) ↦₆₄ st0) ∗ ((sp1 + 64#64 + 8#64) ↦₆₄ st1) ∗
      ((sp1 + 64#64 + 16#64) ↦₆₄ st2) ∗ ((sp1 + 64#64 + 24#64) ↦₆₄ st3) ∗
      (sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
      (memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗ R)) by sep_ac_rfl]
  apply memRegion32_elim; intro c8 c9 c10 c11
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hgoal := h t0 t1 t2 t3 st0 st1 st2 st3 c0 c1 c2 pad152 c4 c5 c6 c7 c8 c9 c10 c11
  dsimp only at hgoal
  have hperm :
      (((sp1 + 192#64) ↦₆₄ c8) ∗ ((sp1 + 200#64) ↦₆₄ c9) ∗
       ((sp1 + 208#64) ↦₆₄ c10) ∗ ((sp1 + 216#64) ↦₆₄ c11) ∗
       (((sp1 + 160#64) ↦₆₄ c4) ∗ ((sp1 + 168#64) ↦₆₄ c5) ∗
       ((sp1 + 176#64) ↦₆₄ c6) ∗ ((sp1 + 184#64) ↦₆₄ c7) ∗
       ((sp1 + 128#64) ↦₆₄ c0) ∗ ((sp1 + 136#64) ↦₆₄ c1) ∗
       ((sp1 + 144#64) ↦₆₄ c2) ∗ ((sp1 + 152#64) ↦₆₄ pad152) ∗
       ((sp1 + 64#64) ↦₆₄ st0) ∗ ((sp1 + 72#64) ↦₆₄ st1) ∗
       ((sp1 + 80#64) ↦₆₄ st2) ∗ ((sp1 + 88#64) ↦₆₄ st3) ∗
       (sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
       (memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗ R))) =
      ((sp1 ↦₆₄ t0) ∗ ((sp1 + 8#64) ↦₆₄ t1) ∗ ((sp1 + 16#64) ↦₆₄ t2) ∗ ((sp1 + 24#64) ↦₆₄ t3) ∗
       ((sp1 + 64#64) ↦₆₄ st0) ∗ ((sp1 + 72#64) ↦₆₄ st1) ∗
       ((sp1 + 80#64) ↦₆₄ st2) ∗ ((sp1 + 88#64) ↦₆₄ st3) ∗
       ((sp1 + 128#64) ↦₆₄ c0) ∗ ((sp1 + 136#64) ↦₆₄ c1) ∗
       ((sp1 + 144#64) ↦₆₄ c2) ∗ ((sp1 + 152#64) ↦₆₄ pad152) ∗
       ((sp1 + 160#64) ↦₆₄ c4) ∗ ((sp1 + 168#64) ↦₆₄ c5) ∗
       ((sp1 + 176#64) ↦₆₄ c6) ∗ ((sp1 + 184#64) ↦₆₄ c7) ∗
       ((sp1 + 192#64) ↦₆₄ c8) ∗ ((sp1 + 200#64) ↦₆₄ c9) ∗
       ((sp1 + 208#64) ↦₆₄ c10) ∗ ((sp1 + 216#64) ↦₆₄ c11) ∗
       memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32 ∗ R) := by sep_ac_rfl
  rwa [hperm]

private theorem hmacSavedCalleeRegs_entails_memRegions (sp1 : BitVec 64) (s0 : State)
    (pad152 : BitVec 64) :
    hmacSavedCalleeRegs sp1 s0 pad152 ⊢
      memRegion (sp1 + 128#64) 32 ∗ memRegion (sp1 + 160#64) 32 ∗ memRegion (sp1 + 192#64) 32 := by
  unfold hmacSavedCalleeRegs
  have h1 := pts64_4_entails_memRegion32 (sp1 + 128#64)
    (s0.readReg64 .x29) (s0.readReg64 .x30) (s0.readReg64 .x27) pad152
  have h2 := pts64_4_entails_memRegion32 (sp1 + 160#64)
    (s0.readReg64 .x26) (s0.readReg64 .x25) (s0.readReg64 .x24) (s0.readReg64 .x23)
  have h3 := pts64_4_entails_memRegion32 (sp1 + 192#64)
    (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1 h2 h3
  have h123 := sepConj_mono h1 (sepConj_mono h2 h3)
  simpa only [sepConj_assoc] using h123

theorem hmacStack224_recombine (sp : BitVec 64) (s0 : State) (pad152 : BitVec 64)
    (tagBs stBs : List (BitVec 8)) (htag : tagBs.length = 32) (hst : stBs.length = 32) :
    let sp1 := sp - 224#64
    ((sp1 ↦ₛ tagBs) ∗
     memRegion (sp1 + 32#64) 32 ∗
     ((sp1 + 64#64) ↦ₛ stBs) ∗
     memRegion (sp1 + 96#64) 32 ∗
     hmacSavedCalleeRegs sp1 s0 pad152) ⊢ stackAt sp 224 := by
  dsimp only
  rw [hmacStack224_eq sp]
  have htagM : ((sp - 224#64) ↦ₛ tagBs) ⊢ memRegion (sp - 224#64) 32 := by
    rw [← htag]; exact pointsToBytes_entails_memRegion _ _
  have hstM : ((sp - 224#64 + 64#64) ↦ₛ stBs) ⊢ memRegion (sp - 224#64 + 64#64) 32 := by
    rw [← hst]; exact pointsToBytes_entails_memRegion _ _
  have hcal := hmacSavedCalleeRegs_entails_memRegions (sp - 224#64) s0 pad152
  exact sepConj_mono htagM (sepConj_mono (Entails.refl _)
    (sepConj_mono hstM (sepConj_mono (Entails.refl _) hcal)))

/-- Prologue + `Algorithm::Sha256` dispatch + `u32::try_from` checks (`+0x000 → +0x0fc` when
`key.length < 2^32 ∧ data.length < 2^32`, or `→ +0xa20` when `2^32 ≤ key.length ∨ 2^32 ≤ data.length`). -/
@[expose] def hmacPrologueSpatial (s0 : State) : SepProp :=
  let sp1 := s0.sp - 224#64
  (sp1 ↦ₛ List.replicate 32 0#8) ∗
  memRegion (sp1 + 32#64) 32 ∗
  memRegion (sp1 + 64#64) 32 ∗
  memRegion (sp1 + 96#64) 32 ∗
  (∃∗ pad152 : BitVec 64, hmacSavedCalleeRegs sp1 s0 pad152)

@[expose] def hmacProloguePure (s0 sf : State) : Prop :=
  sf.sp = s0.sp - 224#64 ∧
  sf.readReg64 .x19 = s0.readReg64 .x8 ∧
  sf.readReg64 .x20 = s0.readReg64 .x3 ∧
  sf.readReg64 .x21 = s0.readReg64 .x4 ∧
  sf.readReg64 .x23 = s0.readReg64 .x2 ∧
  sf.readReg64 .x24 = s0.readReg64 .x1 ∧
  sf.readReg64 .x25 = tryFromKeyNiche (s0.readReg64 .x2) ∧
  sf.readReg64 .x27 = 32#64 ∧
  sf.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
  ((s0.readReg64 .x2).toNat < 2 ^ 32 → (s0.readReg64 .x4).toNat < 2 ^ 32 →
    sf.readReg64 .x26 = tryFromDataNiche (s0.readReg64 .x4))

private theorem or512_shl32_lsb0 (x : BitVec 64) : (512#64 ||| x <<< 32)[0] = false := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  rfl

private theorem shl32_lsb0 (x : BitVec 64) : (x <<< 32)[0] = false := by
  rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_shiftLeft]
  rfl

private theorem hmacPrologueSpatial_entails (s0 : State) (st0 st1 st2 st3 pad152 : BitVec 64) :
    let sp1 := s0.sp - 224#64
    ((sp1 ↦₆₄ 0#64) ∗ ((sp1 + 8#64) ↦₆₄ 0#64) ∗ ((sp1 + 16#64) ↦₆₄ 0#64) ∗ ((sp1 + 24#64) ↦₆₄ 0#64) ∗
     ((sp1 + 64#64) ↦₆₄ st0) ∗ ((sp1 + 72#64) ↦₆₄ st1) ∗
     ((sp1 + 80#64) ↦₆₄ st2) ∗ ((sp1 + 88#64) ↦₆₄ st3) ∗
     ((sp1 + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp1 + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
     ((sp1 + 144#64) ↦₆₄ s0.readReg64 .x27) ∗ ((sp1 + 152#64) ↦₆₄ pad152) ∗
     ((sp1 + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp1 + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
     ((sp1 + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp1 + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
     ((sp1 + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp1 + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
     ((sp1 + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp1 + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
     memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32) ⊢ hmacPrologueSpatial s0 := by
  dsimp only [hmacPrologueSpatial]
  let sp1 := s0.sp - 224#64
  have hzero := pointsTo64_4_replicate32 sp1 0#8 0#64 (by decide)
  have hst := pts64_4_entails_memRegion32 (sp1 + 64#64) st0 st1 st2 st3
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hst
  have hcal : hmacSavedCalleeRegs sp1 s0 pad152 ⊢ ∃∗ p, hmacSavedCalleeRegs sp1 s0 p :=
    Entails.sepExists_right pad152 (Entails.refl _)
  have hperm :
      ((sp1 ↦₆₄ 0#64) ∗ ((sp1 + 8#64) ↦₆₄ 0#64) ∗ ((sp1 + 16#64) ↦₆₄ 0#64) ∗ ((sp1 + 24#64) ↦₆₄ 0#64) ∗
       ((sp1 + 64#64) ↦₆₄ st0) ∗ ((sp1 + 72#64) ↦₆₄ st1) ∗
       ((sp1 + 80#64) ↦₆₄ st2) ∗ ((sp1 + 88#64) ↦₆₄ st3) ∗
       ((sp1 + 128#64) ↦₆₄ s0.readReg64 .x29) ∗ ((sp1 + 136#64) ↦₆₄ s0.readReg64 .x30) ∗
       ((sp1 + 144#64) ↦₆₄ s0.readReg64 .x27) ∗ ((sp1 + 152#64) ↦₆₄ pad152) ∗
       ((sp1 + 160#64) ↦₆₄ s0.readReg64 .x26) ∗ ((sp1 + 168#64) ↦₆₄ s0.readReg64 .x25) ∗
       ((sp1 + 176#64) ↦₆₄ s0.readReg64 .x24) ∗ ((sp1 + 184#64) ↦₆₄ s0.readReg64 .x23) ∗
       ((sp1 + 192#64) ↦₆₄ s0.readReg64 .x22) ∗ ((sp1 + 200#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((sp1 + 208#64) ↦₆₄ s0.readReg64 .x20) ∗ ((sp1 + 216#64) ↦₆₄ s0.readReg64 .x19) ∗
       memRegion (sp1 + 32#64) 32 ∗ memRegion (sp1 + 96#64) 32) =
      (((sp1 ↦₆₄ 0#64) ∗ ((sp1 + 8#64) ↦₆₄ 0#64) ∗ ((sp1 + 16#64) ↦₆₄ 0#64) ∗ ((sp1 + 24#64) ↦₆₄ 0#64)) ∗
       memRegion (sp1 + 32#64) 32 ∗
       (((sp1 + 64#64) ↦₆₄ st0) ∗ ((sp1 + 72#64) ↦₆₄ st1) ∗
        ((sp1 + 80#64) ↦₆₄ st2) ∗ ((sp1 + 88#64) ↦₆₄ st3)) ∗
       memRegion (sp1 + 96#64) 32 ∗
       hmacSavedCalleeRegs sp1 s0 pad152) := by
    unfold hmacSavedCalleeRegs
    sep_ac_rfl
  rw [hperm, hzero]
  exact sepConj_mono (Entails.refl _) (sepConj_mono (Entails.refl _)
    (sepConj_mono hst (sepConj_mono (Entails.refl _) hcal)))

theorem hmac_seg_prologue [HaclPlacement] {s0 : State}
    (hpc : s0.pc = HaclPlacement.mpl.base 6)
    (hrun : s0.status = .Running)
    (hsp_align : s0.spAligned = true)
    (hw0 : (s0.readReg64 .x0).setWidth 32 = 0#32)
    (hw5 : (s0.readReg64 .x5).setWidth 32 = 1#32)
    (hx6 : s0.readReg64 .x6 = 32#64) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (if (2 ^ 32 ≤ (s0.readReg64 .x2).toNat ∨ 2 ^ 32 ≤ (s0.readReg64 .x4).toNat) then
        HaclPlacement.mpl.base 6 + 2592#64
       else
        HaclPlacement.mpl.base 6 + 252#64)
      s0 (stackAt s0.sp 224)
      (fun sf P' => hmacProloguePure s0 sf ∧ (P' ⊢ hmacPrologueSpatial s0)) := by
  have hpc' : s0.pc = haclPl6.base := hpc
  clear hpc
  have hsp_al224 : ((s0.sp - 224#64) &&& 15#64 == 0#64) = true :=
    State.spAligned_sub s0 224#64 hsp_align
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base, ← sepConj_emp (stackAt s0.sp 224)]
  apply hmacStack224_elim
  intro t0 t1 t2 t3 st0 st1 st2 st3 c0 c1 c2 pad152 c4 c5 c6 c7 c8 c9 c10 c11
  dsimp only
  rw [sepConj_emp]
  have hw0_and : ((s0.readReg64 (Reg.gpr 0#5)).setWidth 32 &&& 255#32 == 0#32) = true := by
    change ((s0.readReg64 .x0).setWidth 32 &&& 255#32 == 0#32) = true
    rw [hw0]; decide
  have hw5_tst : ((s0.readReg64 (Reg.gpr 5#5)).setWidth 32 &&& 1#32 != 0#32) = true := by
    change ((s0.readReg64 .x5).setWidth 32 &&& 1#32 != 0#32) = true
    rw [hw5]; decide
  have hx6_gpr : s0.readReg64 (Reg.gpr 6#5) = 32#64 := hx6
  by_cases hhi_k : s0.readReg64 (Reg.gpr 2#5) >>> 32 = 0#64
  · have hk_lt : (s0.readReg64 .x2).toNat < 2 ^ 32 := by
      have : s0.readReg64 .x2 >>> 32 = 0#64 := hhi_k
      bv_omega
    have hk : ¬ (2 ^ 32 ≤ (s0.readReg64 .x2).toNat) := by omega
    have hbit_k : (512#64 ||| s0.readReg64 (Reg.gpr 2#5) <<< 32)[0] = false :=
      or512_shl32_lsb0 _
    by_cases hhi_d : s0.readReg64 (Reg.gpr 4#5) >>> 32 = 0#64
    · have hd_lt : (s0.readReg64 .x4).toNat < 2 ^ 32 := by
        have : s0.readReg64 .x4 >>> 32 = 0#64 := hhi_d
        bv_omega
      have hd : ¬ (2 ^ 32 ≤ (s0.readReg64 .x4).toNat) := by omega
      have hbit_d : (s0.readReg64 (Reg.gpr 4#5) <<< 32)[0] = false := shl32_lsb0 _
      simp only [hk, hd, or_self, ↓reduceIte]
      wp_sym_steps 33
      refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
        ⟨⟨by simp [wp_norm], by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
          by simp [wp_norm], by simp [wp_norm], ?_, by simp [wp_norm],
          by simp [wp_norm], by simp [wp_norm, isCalleeSavedVReg],
          fun _ _ => ?_⟩,
         hmacPrologueSpatial_entails s0 st0 st1 st2 st3 pad152⟩
      · simp [wp_norm, tryFromKeyNiche, hhi_k]
      · simp [wp_norm, tryFromDataNiche, hhi_d]
    · have hd : 2 ^ 32 ≤ (s0.readReg64 .x4).toNat := by
        have : s0.readReg64 .x4 >>> 32 ≠ 0#64 := hhi_d
        bv_omega
      have hne_d : (s0.readReg64 (Reg.gpr 4#5) >>> 32 == 0#64) = false := beq_false_of_ne hhi_d
      simp only [hk, hd, or_true, ↓reduceIte]
      wp_sym_steps 33
      refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
        ⟨⟨by simp [wp_norm], by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
          by simp [wp_norm], by simp [wp_norm], ?_, by simp [wp_norm],
          by simp [wp_norm], by simp [wp_norm, isCalleeSavedVReg],
          fun _ hdlt => absurd hdlt (by omega)⟩,
         hmacPrologueSpatial_entails s0 st0 st1 st2 st3 pad152⟩
      simp [wp_norm, tryFromKeyNiche, hhi_k]
  · have hk : 2 ^ 32 ≤ (s0.readReg64 .x2).toNat := by
      have : s0.readReg64 .x2 >>> 32 ≠ 0#64 := hhi_k
      bv_omega
    have hne_k : (s0.readReg64 (Reg.gpr 2#5) >>> 32 == 0#64) = false := beq_false_of_ne hhi_k
    simp only [hk, true_or, ↓reduceIte]
    wp_sym_steps 27
    refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
      ⟨⟨by simp [wp_norm], by simp [wp_norm], by simp [wp_norm], by simp [wp_norm],
        by simp [wp_norm], by simp [wp_norm], ?_, by simp [wp_norm],
        by simp [wp_norm], by simp [wp_norm, isCalleeSavedVReg],
        fun hklt _ => absurd hklt (by omega)⟩,
       hmacPrologueSpatial_entails s0 st0 st1 st2 st3 pad152⟩
    simp [wp_norm, tryFromKeyNiche, hhi_k]

/-! ## 7. Allocator Setups, Key Preparation, and 64-Byte `ipad` XOR Loop (`+256 → +1000`) -/

theorem hmac_seg_alloc64_args_key [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 256#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 264#64) s R
      (fun sf P' =>
        (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧
         sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = 1#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 256#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 2
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [CalleeSavedPreserved.iff_regs, wp_norm],
      by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

theorem hmac_seg_alloc64_args_ipad [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 916#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 924#64) s R
      (fun sf P' =>
        (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧
         sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = 1#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 916#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 2
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [CalleeSavedPreserved.iff_regs, wp_norm],
      by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

theorem hmac_seg_alloc64_args_opad [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 992#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 1000#64) s R
      (fun sf P' =>
        (sf.sp = s.sp ∧ CalleeSavedPreserved s sf ∧
         sf.readReg64 .x0 = 64#64 ∧ sf.readReg64 .x1 = 1#64) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 992#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 2
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [CalleeSavedPreserved.iff_regs, wp_norm],
      by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

private theorem ule65_of_le64 {v : BitVec 64} (h : v.toNat ≤ 64) :
    BitVec.ule 65#64 v = false := by simp [BitVec.ule]; omega
private theorem ult65_of_le64 {v : BitVec 64} (h : v.toNat ≤ 64) :
    BitVec.ult v 65#64 = true := by simp [BitVec.ult]; omega
private theorem ult_self_false (v : BitVec 64) :
    BitVec.ult v v = false := by simp [BitVec.ult]
private theorem ule65_of_gt64 {v : BitVec 64} (h : 64 < v.toNat) :
    BitVec.ule 65#64 v = true := by simp [BitVec.ule]; omega
private theorem ult65_of_gt64 {v : BitVec 64} (h : 64 < v.toNat) :
    BitVec.ult v 65#64 = false := by simp [BitVec.ult]; omega

theorem hmac_seg_key_short [HaclPlacement] {s : State} {keyLenBV : BitVec 64} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 268#64)
    (hrun : s.status = .Running)
    (hpKey : s.readReg64 .x0 ≠ 0#64)
    (hx23 : s.readReg64 .x23 = keyLenBV)
    (hx25 : s.readReg64 .x25 = tryFromKeyNiche keyLenBV)
    (hk64 : keyLenBV.toNat ≤ 64) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 308#64) s R
      (fun sf P' =>
        (sf.sp = s.sp ∧
         CalleeSavedPreserved (s.writeReg64 .x22 (s.readReg64 .x0)) sf ∧
         sf.readReg64 .x0 = s.readReg64 .x0 ∧
         sf.readReg64 .x1 = s.readReg64 .x24 ∧
         sf.readReg64 .x2 = keyLenBV) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 268#64 := hpc; clear hpc
  have hne0 : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hpKey
  have hk32 : keyLenBV.toNat < 2 ^ 32 := by omega
  have hlsr : tryFromKeyNiche keyLenBV >>> 32 = keyLenBV := tryFromKeyNiche_lsr32 keyLenBV hk32
  have hx25_gpr : s.readReg64 (Reg.gpr 25#5) = tryFromKeyNiche keyLenBV := hx25
  have hx23_gpr : s.readReg64 (Reg.gpr 23#5) = keyLenBV := hx23
  have hcmp65_ule : BitVec.ule 65#64 keyLenBV = false := ule65_of_le64 hk64
  have hcmp65_ult : BitVec.ult keyLenBV 65#64 = true := ult65_of_le64 hk64
  have hcmp_self : BitVec.ult keyLenBV keyLenBV = false := ult_self_false keyLenBV
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 10
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [CalleeSavedPreserved.iff_regs, wp_norm],
      by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

theorem hmac_seg_after_memcpy [HaclPlacement] {s : State} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 312#64) (hrun : s.status = .Running) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 912#64) s R
      (fun sf P' => (sf.sp = s.sp ∧ CalleeSavedPreserved s sf) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 312#64 := hpc; clear hpc
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 1
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [CalleeSavedPreserved.iff_regs, wp_norm]⟩, Entails.refl _⟩

theorem hmac_seg_key_long [HaclPlacement] {s : State} {keyLenBV : BitVec 64} {R : SepProp}
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 268#64)
    (hrun : s.status = .Running)
    (hpKey : s.readReg64 .x0 ≠ 0#64)
    (hx23 : s.readReg64 .x23 = keyLenBV)
    (hx25 : s.readReg64 .x25 = tryFromKeyNiche keyLenBV)
    (hk64 : 64 < keyLenBV.toNat)
    (hk32 : keyLenBV.toNat < 2 ^ 32) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 908#64) s R
      (fun sf P' =>
        (sf.sp = s.sp ∧
         CalleeSavedPreserved (s.writeReg64 .x22 (s.readReg64 .x0)) sf ∧
         sf.readReg64 .x0 = s.readReg64 .x0 ∧
         sf.readReg64 .x1 = 32#64 ∧
         sf.readReg64 .x2 = s.readReg64 .x24 ∧
         sf.readReg64 .x3 = keyLenBV) ∧ (P' ⊢ R)) := by
  have hpc' : s.pc = haclPl6.base + 268#64 := hpc; clear hpc
  have hne0 : (s.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hpKey
  have hlsr : tryFromKeyNiche keyLenBV >>> 32 = keyLenBV := tryFromKeyNiche_lsr32 keyLenBV hk32
  have hx25_gpr : s.readReg64 (Reg.gpr 25#5) = tryFromKeyNiche keyLenBV := hx25
  have hx23_gpr : s.readReg64 (Reg.gpr 23#5) = keyLenBV := hx23
  have hcmp65_ule : BitVec.ule 65#64 keyLenBV = true := ule65_of_gt64 hk64
  have hcmp65_ult : BitVec.ult keyLenBV 65#64 = false := ult65_of_gt64 hk64
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base]
  wp_sym_steps 9
  refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
    ⟨⟨by simp [wp_norm], by simp [CalleeSavedPreserved.iff_regs, wp_norm],
      by simp [wp_norm], by simp [wp_norm], by simp [wp_norm], by simp [wp_norm]⟩, Entails.refl _⟩

theorem xor_w32_to8_a (b pad : BitVec 8) :
    (((b.setWidth 64).setWidth 32 ^^^ (pad.setWidth 64).setWidth 32).setWidth 64).setWidth 8 =
      b ^^^ pad := by bv_bits
theorem xor_w32_to8_b (b pad : BitVec 8) :
    ((b.setWidth 32 ^^^ pad.setWidth 32).setWidth 64).setWidth 8 = b ^^^ pad := by bv_bits
theorem xor_w32_to8_c (b pad : BitVec 8) :
    (b.setWidth 32 ^^^ pad.setWidth 32).setWidth 8 = b ^^^ pad := by bv_bits

private theorem hmac_seg_ipad_xor_loop [HaclPlacement]
    (suff' : List (BitVec 8)) (b : BitVec 8) {pref : List (BitVec 8)}
    {pKey pDst : BitVec 64} {pad : BitVec 8} {s : State} {R : SepProp}
    (hlen : pref.length + (b :: suff').length = 64)
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 956#64) (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 pref.length)
    (hx22 : s.readReg64 .x22 = pKey) (hx23 : s.readReg64 .x23 = pDst) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 988#64) s
      ((pKey ↦ₛ (pref ++ b :: suff')) ∗
       (pDst ↦ₛ (pref.map (· ^^^ pad) ++ List.replicate (b :: suff').length pad)) ∗ R)
      (fun sf P' =>
        (sf.sp = s.sp ∧ CalleeSavedPreserved s sf) ∧
        (P' ⊢ (pKey ↦ₛ (pref ++ b :: suff')) ∗
              (pDst ↦ₛ (pref ++ b :: suff').map (· ^^^ pad)) ∗ R)) := by
  induction suff' generalizing b pref s with
  | nil =>
    have hplen : pref.length = 63 := by simp at hlen; omega
    have hpc' : s.pc = haclPl6.base + 956#64 := hpc; clear hpc
    have hx8_gpr : s.readReg64 (Reg.gpr 8#5) = 63#64 := by
      change s.readReg64 .x8 = 63#64; rw [hx8, hplen]
    have hx22_gpr : s.readReg64 (Reg.gpr 22#5) = pKey := hx22
    have hx23_gpr : s.readReg64 (Reg.gpr 23#5) = pDst := hx23
    have hpre_eq : ((pKey ↦ₛ (pref ++ [b])) ∗
         (pDst ↦ₛ (pref.map (· ^^^ pad) ++ List.replicate 1 pad)) ∗ R) =
        (((pKey + 63#64) ↦₈ b) ∗ ((pDst + 63#64) ↦₈ pad) ∗
         ((pKey ↦ₛ pref) ∗ (pDst ↦ₛ pref.map (· ^^^ pad)) ∗ R)) := by
      rw [show List.replicate 1 pad = [pad] from rfl, pointsToBytes_snoc pKey,
          pointsToBytes_snoc pDst, List.length_map, hplen]
      change ((pKey ↦ₛ pref) ∗ ((pKey + 63#64) ↦₈ b)) ∗
        (((pDst ↦ₛ pref.map (· ^^^ pad)) ∗ ((pDst + 63#64) ↦₈ pad)) ∗ R) = _; sep_ac_rfl
    dsimp only [List.length]
    rw [← haclPC6_eq_blockProgram, ← haclPl6_base, hpre_eq]
    wp_sym_steps 8
    refine SepWP.done (by simp [wp_norm]) (by simp [wp_norm, hrun])
      ⟨⟨by simp [wp_norm], by simp [CalleeSavedPreserved.iff_regs, wp_norm]⟩, ?_⟩
    try simp only [xor_w32_to8_a, xor_w32_to8_b, xor_w32_to8_c]
    refine Entails.of_eq ?_
    rw [List.map_append, List.map_singleton, pointsToBytes_snoc pKey, pointsToBytes_snoc pDst,
        List.length_map, hplen]
    change (((pKey + 63#64) ↦₈ b) ∗ ((pDst + 63#64) ↦₈ (b ^^^ pad)) ∗
      ((pKey ↦ₛ pref) ∗ (pDst ↦ₛ pref.map (· ^^^ pad)) ∗ R)) =
      ((pKey ↦ₛ pref) ∗ ((pKey + 63#64) ↦₈ b)) ∗
      (((pDst ↦ₛ pref.map (· ^^^ pad)) ∗ ((pDst + 63#64) ↦₈ (b ^^^ pad))) ∗ R); sep_ac_rfl
  | cons b2 suff'' ih =>
    have hlt63 : pref.length < 63 := by simp at hlen; omega
    have hpc' : s.pc = haclPl6.base + 956#64 := hpc; clear hpc
    have hx8_gpr : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 pref.length := hx8
    have hx22_gpr : s.readReg64 (Reg.gpr 22#5) = pKey := hx22
    have hx23_gpr : s.readReg64 (Reg.gpr 23#5) = pDst := hx23
    have hne64_eq : BitVec.ofNat 64 pref.length + 1#64 ≠ 64#64 := by bv_omega
    have hne64 : (BitVec.ofNat 64 pref.length + 1#64 != 64#64) = true := bne_iff_ne.mpr hne64_eq
    have hbeq64 : (BitVec.ofNat 64 pref.length + 1#64 == 64#64) = false := beq_false_of_ne hne64_eq
    have hpre_eq : ((pKey ↦ₛ (pref ++ b :: b2 :: suff'')) ∗
         (pDst ↦ₛ (pref.map (· ^^^ pad) ++ List.replicate (b :: b2 :: suff'').length pad)) ∗ R) =
        (((pKey + BitVec.ofNat 64 pref.length) ↦₈ b) ∗
         ((pDst + BitVec.ofNat 64 pref.length) ↦₈ pad) ∗
         ((pKey ↦ₛ pref) ∗ ((pKey + BitVec.ofNat 64 (pref.length + 1)) ↦ₛ (b2 :: suff'')) ∗
          (pDst ↦ₛ pref.map (· ^^^ pad)) ∗
          ((pDst + BitVec.ofNat 64 (pref.length + 1)) ↦ₛ List.replicate (b2 :: suff'').length pad) ∗ R)) := by
      rw [show List.replicate (b :: b2 :: suff'').length pad =
          pad :: List.replicate (b2 :: suff'').length pad from rfl,
          pointsToBytes_append pKey, pointsToBytes_cons_off pKey,
          pointsToBytes_append pDst, List.length_map, pointsToBytes_cons_off pDst]; sep_ac_rfl
    rw [← haclPC6_eq_blockProgram, ← haclPl6_base, hpre_eq]
    wp_sym_steps 8
    try simp only [xor_w32_to8_a, xor_w32_to8_b, xor_w32_to8_c]
    have hmid_eq :
        (((pKey + BitVec.ofNat 64 pref.length) ↦₈ b) ∗
         ((pDst + BitVec.ofNat 64 pref.length) ↦₈ (b ^^^ pad)) ∗
         ((pKey ↦ₛ pref) ∗ ((pKey + BitVec.ofNat 64 (pref.length + 1)) ↦ₛ (b2 :: suff'')) ∗
          (pDst ↦ₛ pref.map (· ^^^ pad)) ∗
          ((pDst + BitVec.ofNat 64 (pref.length + 1)) ↦ₛ List.replicate (b2 :: suff'').length pad) ∗ R)) =
        ((pKey ↦ₛ ((pref ++ [b]) ++ b2 :: suff'')) ∗
         (pDst ↦ₛ ((pref ++ [b]).map (· ^^^ pad) ++ List.replicate (b2 :: suff'').length pad)) ∗ R) := by
      rw [List.map_append, List.map_singleton,
          pointsToBytes_append pKey (pref ++ [b]), pointsToBytes_snoc pKey,
          pointsToBytes_append pDst (pref.map (· ^^^ pad) ++ [b ^^^ pad]),
          pointsToBytes_snoc pDst, List.length_append, List.length_singleton,
          List.length_append, List.length_map, List.length_singleton]; sep_ac_rfl
    rw [hmid_eq, haclPC6_eq_blockProgram, haclPl6_base]
    have hlen' : (pref ++ [b]).length + (b2 :: suff'').length = 64 := by simp at hlen ⊢; omega
    refine (ih b2 hlen' ?_ ?_ ?_ ?_ ?_).mono fun sf P' _ _ ⟨⟨hsp_sf, hcs_sf⟩, hent⟩ => ⟨⟨?_, ?_⟩, ?_⟩
    · simp [wp_norm]
    · simp [wp_norm, hrun]
    · simp only [wp_norm, List.length_append, List.length_singleton]; bv_omega
    · simp [wp_norm, hx22]
    · simp [wp_norm, hx23]
    · rw [hsp_sf]; simp [wp_norm]
    · refine CalleeSavedPreserved.trans ?_ hcs_sf
      simp [CalleeSavedPreserved.iff_regs, wp_norm]
    · simpa only [List.append_assoc, List.singleton_append] using hent

theorem hmac_seg_ipad_xor [HaclPlacement] {pKey pIpad : BitVec 64} {k0 : List (BitVec 8)}
    {s : State} {R : SepProp} (hk0 : k0.length = 64)
    (hpc : s.pc = HaclPlacement.mpl.base 6 + 928#64) (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = pIpad) (hne0 : pIpad ≠ 0#64) (hx22 : s.readReg64 .x22 = pKey) :
    SepWP (libcruxHmacLib.blockProgram HaclPlacement.mpl 6)
      (HaclPlacement.mpl.base 6 + 988#64) s
      ((pKey ↦ₛ k0) ∗ memRegion pIpad 64 ∗ R)
      (fun sf P' =>
        (sf.sp = s.sp ∧
         CalleeSavedPreserved
           ((s.writeReg64 .x23 pIpad).writeReg64 .x26 (s.readReg64 .x26 >>> 32)) sf) ∧
        (P' ⊢ (pKey ↦ₛ k0) ∗ (pIpad ↦ₛ k0.map (· ^^^ 0x36#8)) ∗ R)) := by
  have hpc' : s.pc = haclPl6.base + 928#64 := hpc; clear hpc
  have hx0_gpr : s.readReg64 (Reg.gpr 0#5) = pIpad := hx0
  have hx22_gpr : s.readReg64 (Reg.gpr 22#5) = pKey := hx22
  have hne0_beq : (pIpad == 0#64) = false := beq_false_of_ne hne0
  have hm64 : (pKey ↦ₛ k0) ∗ memRegion pIpad 64 ∗ R =
      memRegion pIpad 32 ∗ (memRegion (pIpad + 32#64) 32 ∗ ((pKey ↦ₛ k0) ∗ R)) := by
    rw [memRegion_split pIpad 32 32 (by decide)]; sep_ac_rfl
  rw [← haclPC6_eq_blockProgram, ← haclPl6_base, hm64]
  apply memRegion32_elim; intro w0 w1 w2 w3
  rw [show ((pIpad ↦₆₄ w0) ∗ ((pIpad + 8#64) ↦₆₄ w1) ∗ ((pIpad + 16#64) ↦₆₄ w2) ∗
      ((pIpad + 24#64) ↦₆₄ w3) ∗ (memRegion (pIpad + 32#64) 32 ∗ ((pKey ↦ₛ k0) ∗ R))) =
      memRegion (pIpad + 32#64) 32 ∗ ((pIpad ↦₆₄ w0) ∗ ((pIpad + 8#64) ↦₆₄ w1) ∗
      ((pIpad + 16#64) ↦₆₄ w2) ∗ ((pIpad + 24#64) ↦₆₄ w3) ∗ (pKey ↦ₛ k0) ∗ R) by sep_ac_rfl]
  apply memRegion32_elim; intro w4 w5 w6 w7
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_sym_steps 7
  have hfold :
      (((pIpad + 32#64) ↦₆₄ 0x3636363636363636#64) ∗ ((pIpad + 40#64) ↦₆₄ 0x3636363636363636#64) ∗
       ((pIpad + 48#64) ↦₆₄ 0x3636363636363636#64) ∗ ((pIpad + 56#64) ↦₆₄ 0x3636363636363636#64) ∗
       ((pIpad ↦₆₄ 0x3636363636363636#64) ∗ ((pIpad + 8#64) ↦₆₄ 0x3636363636363636#64) ∗
        ((pIpad + 16#64) ↦₆₄ 0x3636363636363636#64) ∗ ((pIpad + 24#64) ↦₆₄ 0x3636363636363636#64) ∗
        (pKey ↦ₛ k0) ∗ R)) =
      ((pKey ↦ₛ k0) ∗ (pIpad ↦ₛ List.replicate 64 0x36#8) ∗ R) := by
    rw [← pointsTo64_8_replicate64 pIpad 0x36#8 0x3636363636363636#64 (by decide)]; sep_ac_rfl
  rw [hfold, haclPC6_eq_blockProgram, haclPl6_base]
  match k0, hk0 with
  | b0 :: suff', hk0' =>
    rw [show List.replicate 64 0x36#8 = List.replicate (b0 :: suff').length 0x36#8 by rw [hk0']]
    refine (hmac_seg_ipad_xor_loop suff' b0 (pref := []) (pKey := pKey) (pDst := pIpad)
      (pad := 0x36#8) (R := R) (by simpa using hk0') ?_ ?_ ?_ ?_ ?_).mono
      fun sf P' _ _ ⟨⟨hsp_sf, hcs_sf⟩, hent⟩ => ⟨⟨?_, ?_⟩, hent⟩
    · simp [wp_norm]
    · simp [wp_norm, hrun]
    · simp [wp_norm]
    · simp [wp_norm, hx22]
    · simp [wp_norm]
    · rw [hsp_sf]; simp [wp_norm]
    · refine CalleeSavedPreserved.trans ?_ hcs_sf
      simp [CalleeSavedPreserved.iff_regs, wp_norm, isCalleeSavedVReg]

end LibsignalBinary.Proofs.HookDischarge.CryptoSha256.LibcruxHmacStep
