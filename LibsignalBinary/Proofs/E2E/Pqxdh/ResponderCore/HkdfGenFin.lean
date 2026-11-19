/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Specifications.LibsignalE2E.State -- shake: keep
import LibsignalBinary.Proofs.CodeLayout

/-!
# Generalized Multi-Block `finalize_fixed` and `PqxdhHkdfExtractOk`

Generalizes `finalize_fixed` (`0x30680`) to multi-block `HmacStGen` (`blocks.length % 64 = 0`,
`blocks.length ≤ 192`, `rem.length < 56`), lifts `Hmac<Sha256>::new_from_slice` (`0x2b3b0`) to
`tripleRatchetProgAt` under `Initiator.FrozenRo`, and proves `PqxdhHkdfExtractOk` (`0x1ad38`) for
both `salt = some` (`32`-B IKM) and `salt = none` (`ikm.length ∈ {160, 192, 224}`).
-/

public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

namespace CryptoVerification.E2E.Pqxdh.ResponderCore

open CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib ProofLib.Variant
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister memcpyHook memsetHook toLEBytes)
open CryptoVerification.LibsignalAesCbc.Run
open CryptoVerification.LibsignalAesCbc.Run.Bytes
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes readShaState)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

private theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

macro "solve_fin_saved" : tactic =>
  `(tactic| (
    try rw [mem_setMem]
    simp (config := { decide := true }) only [arm64_norm]))

macro "fin_reg" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

/-! ## Multi-Block `compress256Hook` Step and `chunks64` Helpers -/

@[simp] private theorem chunks64_length (bs : List (BitVec 8)) :
    (chunks64 bs).length = bs.length / 64 := by
  simp [chunks64]

@[simp] private theorem chunks64_getElem (bs : List (BitVec 8)) (i : ℕ)
    (hi : i < (chunks64 bs).length) :
    (chunks64 bs)[i] = (bs.drop (64 * i)).take 64 := by
  simp [chunks64]

theorem chunks64_of_lt {bs : List (BitVec 8)} (h : bs.length < 64) :
    chunks64 bs = [] := by
  rw [← List.length_eq_zero_iff, chunks64_length]
  omega

theorem chunks64_append_64 {a b : List (BitVec 8)} (ha : a.length = 64) :
    chunks64 (a ++ b) = a :: chunks64 b := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp [ha]
  · cases i with
    | zero =>
      simp [ha]
    | succ j =>
      simp only [chunks64_getElem, List.getElem_cons_succ]
      have hdrop : 64 * (j + 1) = a.length + 64 * j := by omega
      rw [hdrop, ← List.drop_drop, List.drop_left]

theorem chunks64_single {a : List (BitVec 8)} (ha : a.length = 64) :
    chunks64 a = [a] := by
  conv_lhs => rw [← List.append_nil a]
  rw [chunks64_append_64 ha, chunks64_of_lt (by simp)]

theorem chunks64_append_mul {a b : List (BitVec 8)} (k : ℕ) (ha : a.length = 64 * k) :
    chunks64 (a ++ b) = chunks64 a ++ chunks64 b := by
  refine List.ext_getElem ?_ fun i h1 h2 => ?_
  · simp [ha]; omega
  · rw [chunks64_getElem]
    by_cases hi : i < (chunks64 a).length
    · rw [List.getElem_append_left hi, chunks64_getElem]
      have hle : 64 * i + 64 ≤ a.length := by
        simp only [chunks64_length] at hi
        omega
      rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
    · rw [List.getElem_append_right (by omega), chunks64_getElem]
      simp only [chunks64_length] at hi ⊢
      have hdrop : 64 * i = a.length + 64 * (i - a.length / 64) := by omega
      rw [hdrop, ← List.drop_drop, List.drop_left]

theorem chunks64_append {a b : List (BitVec 8)} (ha : a.length % 64 = 0) :
    chunks64 (a ++ b) = chunks64 a ++ chunks64 b :=
  chunks64_append_mul (a.length / 64) (by omega)

theorem compress256Hook_multi_eq (F : ShaState → List (BitVec 8) → ShaState) {s : State}
    {stPtr blkPtr lr : BitVec 64} {nblk : ℕ} {st : ShaState} {blocks : List (BitVec 8)}
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : (s.readReg64 .x2).toNat = nblk)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr (64 * nblk) = blocks) :
    compress256Hook F s =
      (s.setMem (s.mem.writeBytes stPtr
        (shaStateBytes ((chunks64 blocks).foldl F st)))).setPC lr := by
  dsimp only [compress256Hook, returnToLinkRegister]
  have hlr' : (s.setMem (s.mem.writeBytes (s.readReg64 .x0)
      (shaStateBytes
        ((chunks64 (s.mem.readBytes (s.readReg64 .x1) (64 * (s.readReg64 .x2).toNat))).foldl
        F (readShaState s.mem (s.readReg64 .x0)))))).readReg64 .lr = lr := by
    simpa [arm64_norm] using hlr
  rw [hlr', hx0, hx1, hx2, hblk, readShaState_of_shaStateBytes s.mem stPtr st hst]

/-- `Hmac<Sha256>` state at `a` after absorbing `blocks` (`blocks.length % 64 = 0`) into the inner
running state and buffering `rem` (`rem.length < 64`) at `a`. -/
@[expose] def HmacStGen (m : Memory) (a : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) : Prop :=
  blocks.length % 64 = 0 ∧
  blocks.length ≤ 192 ∧
  rem.length < 64 ∧
  m.readBytes a rem.length = rem ∧
  m.read8 (a + 0x3f#64) = BitVec.ofNat 8 rem.length ∧
  m.readBytes (a + 0x40#64) 32 = shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key)) ∧
  m.read64 (a + 0x60#64) = BitVec.ofNat 64 (1 + blocks.length / 64) ∧
  m.readBytes (a + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key) ∧
  m.read64 (a + 0x88#64) = 1#64

theorem HmacStGen.of_agreesOutside {m₁ m₂ : Memory} {hm : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key blocks rem : List (BitVec 8)}
    {base : BitVec 64} {len : ℕ}
    (hst : HmacStGen m₁ hm F key blocks rem)
    (hag : AgreesOutside m₁ m₂ base len)
    (hd : DisjointRegions base len hm 0x90) :
    HmacStGen m₂ hm F key blocks rem := by
  rcases hst with ⟨hmod, hblk_le, hlen, hmsg, hpos, hin, hibl, hout, hobl⟩
  refine ⟨hmod, hblk_le, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hm0 : rem.length = 0
    · simp [hm0] at hmsg ⊢; exact hmsg
    · have hd' : DisjointRegions base len hm rem.length :=
        hd.sub_right hm ⟨by omega, by simp; omega⟩
      exact (hag.readBytes_eq hd' (by omega)).trans hmsg
  · have hout8 : OutsideRegion base len (hm + 0x3f#64) := by
      rcases hd with ⟨hd1, hd2⟩
      unfold OutsideRegion; bv_omega
    exact (hag.1 _ hout8).trans hpos
  · have hd' : DisjointRegions base len (hm + 0x40#64) 32 :=
      hd.sub_right (hm + 0x40#64) ⟨by decide, by bv_omega⟩
    exact (hag.readBytes_eq hd' (by decide)).trans hin
  · have hd' : DisjointRegions base len (hm + 0x60#64) 8 :=
      hd.sub_right (hm + 0x60#64) ⟨by decide, by bv_omega⟩
    exact (hag.read64_eq hd').trans hibl
  · have hd' : DisjointRegions base len (hm + 0x68#64) 32 :=
      hd.sub_right (hm + 0x68#64) ⟨by decide, by bv_omega⟩
    exact (hag.readBytes_eq hd' (by decide)).trans hout
  · have hd' : DisjointRegions base len (hm + 0x88#64) 8 :=
      hd.sub_right (hm + 0x88#64) ⟨by decide, by bv_omega⟩
    exact (hag.read64_eq hd').trans hobl

theorem HmacStGen.of_copy_19 {m₀ m : Memory} {src dst : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key blocks rem : List (BitVec 8)}
    (hsrc : HmacStGen m₀ src F key blocks rem)
    (h0   : m.read64 dst            = m₀.read64 src)
    (h8   : m.read64 (dst + 8#64)   = m₀.read64 (src + 8#64))
    (h16  : m.read64 (dst + 16#64)  = m₀.read64 (src + 16#64))
    (h24  : m.read64 (dst + 24#64)  = m₀.read64 (src + 24#64))
    (h32  : m.read64 (dst + 32#64)  = m₀.read64 (src + 32#64))
    (h40  : m.read64 (dst + 40#64)  = m₀.read64 (src + 40#64))
    (h48  : m.read64 (dst + 48#64)  = m₀.read64 (src + 48#64))
    (h56  : m.read64 (dst + 56#64)  = m₀.read64 (src + 56#64))
    (h64  : m.read64 (dst + 64#64)  = m₀.read64 (src + 64#64))
    (h72  : m.read64 (dst + 72#64)  = m₀.read64 (src + 72#64))
    (h80  : m.read64 (dst + 80#64)  = m₀.read64 (src + 80#64))
    (h88  : m.read64 (dst + 88#64)  = m₀.read64 (src + 88#64))
    (h96  : m.read64 (dst + 96#64)  = m₀.read64 (src + 96#64))
    (h104 : m.read64 (dst + 104#64) = m₀.read64 (src + 104#64))
    (h112 : m.read64 (dst + 112#64) = m₀.read64 (src + 112#64))
    (h120 : m.read64 (dst + 120#64) = m₀.read64 (src + 120#64))
    (h128 : m.read64 (dst + 128#64) = m₀.read64 (src + 128#64))
    (h136 : m.read64 (dst + 136#64) = m₀.read64 (src + 136#64)) :
    HmacStGen m dst F key blocks rem := by
  rcases hsrc with ⟨hmod, hblk_le, hlen, hmsg, hpos, hin, hcnt1, hout, hcnt2⟩
  refine ⟨hmod, hblk_le, hlen, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h64_eq : m.readBytes dst 64 = m₀.readBytes src 64 := by
      rw [show (64 : ℕ) = 32 + 32 from rfl,
          Bytes.readBytes_add m dst 32 32, Bytes.readBytes_add m₀ src 32 32,
          readBytes_32_eq_of_read64_eq h0 h8 h16 h24,
          readBytes_32_eq_of_read64_eq h32
            (by simpa [BitVec.add_assoc] using h40)
            (by simpa [BitVec.add_assoc] using h48)
            (by simpa [BitVec.add_assoc] using h56)]
    have hslice1 := Bytes.readBytes_slice_of_readBytes_eq m dst (m₀.readBytes src 64)
      (by rw [Memory.readBytes_length]; exact h64_eq) 0 rem.length
      (by rw [Memory.readBytes_length]; omega)
    have hslice2 := Bytes.readBytes_slice_of_readBytes_eq m₀ src (m₀.readBytes src 64)
      (by rw [Memory.readBytes_length]) 0 rem.length
      (by rw [Memory.readBytes_length]; omega)
    simpa [hmsg] using hslice1.trans hslice2.symm
  · have hd : dst + 0x3f#64 = (dst + 56#64) + 7#64 := by bv_lin
    have hs : src + 0x3f#64 = (src + 56#64) + 7#64 := by bv_lin
    rw [hd, read8_add_7_of_read64_eq h56, ← hs, hpos]
  · rw [readBytes_32_eq_of_read64_eq h64
          (by simpa [BitVec.add_assoc] using h72)
          (by simpa [BitVec.add_assoc] using h80)
          (by simpa [BitVec.add_assoc] using h88), hin]
  · rw [show (0x60#64 : BitVec 64) = 96#64 from rfl, h96, ← hcnt1]
  · rw [readBytes_32_eq_of_read64_eq h104
          (by simpa [BitVec.add_assoc] using h112)
          (by simpa [BitVec.add_assoc] using h120)
          (by simpa [BitVec.add_assoc] using h128), hout]
  · rw [show (0x88#64 : BitVec 64) = 136#64 from rfl, h136, ← hcnt2]

/-- Final padded inner SHA-256 block when `blocks` (`blocks.length % 64 = 0`) has already been
absorbed and `rem.length < 56`. -/
@[expose] def innerLastBlockGen (blocks rem : List (BitVec 8)) : List (BitVec 8) :=
  rem ++ [0x80] ++ List.replicate (55 - rem.length) 0 ++
    toBEBytes 8 (BitVec.ofNat 64 (8 * (64 + blocks.length + rem.length)))

theorem innerLastBlockGen_length {blocks rem : List (BitVec 8)} (hrem : rem.length < 56) :
    (innerLastBlockGen blocks rem).length = 64 := by
  simp [innerLastBlockGen, toBEBytes]; omega

theorem bit_len_inner_gen_eq {blocksLen n : ℕ} (hmod : blocksLen % 64 = 0)
    (hblk : blocksLen ≤ 192) (hn : n < 56) :
    BitVec.ofNat 64 (1 + blocksLen / 64) <<< 9 ||| BitVec.ofNat 64 n <<< 3 =
      BitVec.ofNat 64 (8 * (64 + blocksLen + n)) := by
  have hor_fin : ∀ (q : Fin 4) (m : Fin 56),
      BitVec.ofNat 64 (1 + q.val) <<< 9 ||| BitVec.ofNat 64 m.val <<< 3 =
        BitVec.ofNat 64 (512 * (1 + q.val)) + 8#64 * BitVec.ofNat 64 m.val := by
    decide
  have h1 : BitVec.ofNat 64 (512 * (1 + blocksLen / 64)) + 8#64 * BitVec.ofNat 64 n =
      BitVec.ofNat 64 (8 * (64 + blocksLen + n)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    change (512 * (1 + blocksLen / 64) % 18446744073709551616 +
      8 * (n % 18446744073709551616) % 18446744073709551616) % 18446744073709551616 =
      (8 * (64 + blocksLen + n)) % 18446744073709551616
    omega
  exact (hor_fin ⟨blocksLen / 64, by omega⟩ ⟨n, hn⟩).trans h1

theorem hmacWith_gen (F : ShaState → List (BitVec 8) → ShaState) (key blocks rem : List (BitVec 8))
    (hk : key.length ≤ 64) (hmod : blocks.length % 64 = 0) (hm : rem.length < 56) :
    hmacWith F key (blocks ++ rem) =
      digestBytes (F (hmacOuterInit F key)
        (outerBlock (digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
          (innerLastBlockGen blocks rem))))) := by
  unfold hmacWith
  have hk_not_gt : ¬ (64 < key.length) := by omega
  simp only [hk_not_gt, ↓reduceIte]
  change sha256With F ((hmacKeyBlock key).map (· ^^^ 0x5c) ++
    sha256With F ((hmacKeyBlock key).map (· ^^^ 0x36) ++ (blocks ++ rem))) = _
  have hkb_len : (hmacKeyBlock key).length = 64 := by
    simp [hmacKeyBlock]; omega
  have hipad_len : ((hmacKeyBlock key).map (· ^^^ 0x36)).length = 64 := by
    simp [hkb_len]
  have hopad_len : ((hmacKeyBlock key).map (· ^^^ 0x5c)).length = 64 := by
    simp [hkb_len]
  have hinner_blk_len : (innerLastBlockGen blocks rem).length = 64 :=
    innerLastBlockGen_length hm
  have hinner_pad : sha256Pad ((hmacKeyBlock key).map (· ^^^ 0x36) ++ (blocks ++ rem)) =
      (hmacKeyBlock key).map (· ^^^ 0x36) ++ blocks ++ innerLastBlockGen blocks rem := by
    unfold sha256Pad innerLastBlockGen
    have hlen : ((hmacKeyBlock key).map (· ^^^ 0x36) ++ (blocks ++ rem)).length =
        64 + blocks.length + rem.length := by
      simp [hkb_len]; omega
    have hmod' : (119 - (64 + blocks.length + rem.length) % 64) % 64 = 55 - rem.length := by omega
    rw [hlen, hmod']
    simp only [List.append_assoc]
  have hinner : sha256With F ((hmacKeyBlock key).map (· ^^^ 0x36) ++ (blocks ++ rem)) =
      digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
        (innerLastBlockGen blocks rem)) := by
    unfold sha256With digestBytes
    rw [hinner_pad, List.append_assoc,
        chunks64_append (by rw [hipad_len]),
        chunks64_single hipad_len,
        chunks64_append hmod,
        chunks64_single hinner_blk_len]
    simp [hmacInnerInit]
  rw [hinner]
  set d := digestBytes (F ((chunks64 blocks).foldl F (hmacInnerInit F key))
    (innerLastBlockGen blocks rem))
  have hd_len : d.length = 32 := digestBytes_length _
  have houter_blk_len : (outerBlock d).length = 64 := by
    simp [outerBlock, hd_len]
  have houter_pad : sha256Pad ((hmacKeyBlock key).map (· ^^^ 0x5c) ++ d) =
      (hmacKeyBlock key).map (· ^^^ 0x5c) ++ outerBlock d := by
    unfold sha256Pad outerBlock
    have hlen : ((hmacKeyBlock key).map (· ^^^ 0x5c) ++ d).length = 96 := by
      simp [hkb_len, hd_len]
    rw [hlen]
    simp only [List.append_assoc]
  unfold sha256With digestBytes
  rw [houter_pad, chunks64_append (by rw [hopad_len]),
      chunks64_single hopad_len, chunks64_single houter_blk_len]
  simp [hmacOuterInit]

/-! ## Generalized `finalize_fixed` (`0x30680`) for `HmacStGen` -/

structure FinGenPre (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (key blocks rem : List (BitVec 8)) (s0 : State) : Prop where
  pc_eq        : s0.pc = b + 0x30764#64
  status       : s0.status = .Running
  key_le       : key.length ≤ 64
  rem_lt       : rem.length < 56
  hmac_st      : HmacStGen s0.mem (s0.readReg64 .x1) F key blocks rem
  rw_out       : RW s0.mem (s0.readReg64 .x0) 32
  rw_hm        : RW s0.mem (s0.readReg64 .x1) 0x90
  rw_fsp       : RW s0.mem (s0.sp - 144#64) 144
  disj_out_hm  : DisjointRegions (s0.readReg64 .x0) 32 (s0.readReg64 .x1) 0x90
  disj_out_fsp : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64) 144
  disj_hm_fsp  : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64) 144
  sp_aligned   : (s0.sp &&& 0b1111#64) = 0#64

@[expose] def ENfs1Long (b : BitVec 64) (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) :
    Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = b + 0x2b494#64 ∧
  s.readReg64 .lr = b + 0x1ad88#64 ∧
  s.readReg64 .x0 = sp0 + 176#64 ∧
  s.readReg64 .x1 = Extract.saltPtrOf sp0 x ∧
  s.readReg64 .x2 = 32#64 ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = BitVec.ofNat 64 x.ikm.length ∧
  s.mem.readBytes (Extract.saltPtrOf sp0 x) 32 = effectiveSalt x.salt

@[expose] def ERet1Long (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = b + 0x1ad88#64 ∧
  s.readReg64 .x20 = x.ikmA ∧
  s.readReg64 .x21 = BitVec.ofNat 64 x.ikm.length ∧
  s.mem.read64 (sp0 + 176#64) = 0#64 ∧
  HmacSt s.mem (sp0 + 184#64) F (effectiveSalt x.salt) []

@[expose] def EC88Long (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = b + 0x1ae80#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacStGen s.mem sp0 F (effectiveSalt x.salt)
    (x.ikm.take (64 * (x.ikm.length / 64))) (x.ikm.drop (64 * (x.ikm.length / 64)))

@[expose] def EFinLong (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (x : ExtractGhost) (s0 : State) (sp0 : BitVec 64) (s : State) : Prop :=
  Extract.ExtCommon s0 sp0 s ∧
  s.pc = b + 0x30764#64 ∧
  s.readReg64 .lr = b + 0x1aeb4#64 ∧
  s.readReg64 .x0 = sp0 + 144#64 ∧
  s.readReg64 .x1 = sp0 + 176#64 ∧
  s.readReg64 .x22 = sp0 + 176#64 ∧
  HmacStGen s.mem (sp0 + 176#64) F (effectiveSalt x.salt)
    (x.ikm.take (64 * (x.ikm.length / 64))) (x.ikm.drop (64 * (x.ikm.length / 64)))

theorem agreesOutside_writeBytes_sub_sp0 {m : Memory} {sp0 a : BitVec 64} {bs : List (BitVec 8)}
    (ha : (a - sp0).toNat + bs.length ≤ 328) :
    AgreesOutside m (m.writeBytes a bs) sp0 328 := by
  have h := ProofLib.AgreesOutside.writeBytes_self m a bs
  have hout : ∀ x, OutsideRegion sp0 328 x → OutsideRegion a bs.length x := by
    intro x hx; simp only [OutsideRegion] at hx ⊢; bv_omega
  exact ⟨fun x hx => h.1 x (hout x hx), h.2.1, fun x hx => h.2.2.1 x (hout x hx), h.2.2.2⟩

theorem HmacStGen.of_comp_write8 {m : Memory} {sp0 : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key blocks : List (BitVec 8)} {nrem : ℕ}
    (hcnt1 : m.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + blocks.length / 64))
    (hout : m.readBytes (sp0 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key))
    (hcnt2 : m.read64 (sp0 + 0x88#64) = 1#64) :
    let ist' := shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key))
    let m₁ := m.writeBytes (sp0 + 0x40#64) ist'
    let m₂ := m₁.write8 (sp0 + 63#64) (BitVec.ofNat 8 nrem)
    m₂.read8 (sp0 + 0x3f#64) = BitVec.ofNat 8 nrem ∧
    m₂.readBytes (sp0 + 0x40#64) 32 = ist' ∧
    m₂.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + blocks.length / 64) ∧
    m₂.readBytes (sp0 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key) ∧
    m₂.read64 (sp0 + 0x88#64) = 1#64 := by
  intro ist' m₁ m₂
  have hist_len : ist'.length = 32 := shaStateBytes_length _
  have hag1 : AgreesOutside m m₁ (sp0 + 0x40#64) 32 := by
    have h := ProofLib.AgreesOutside.writeBytes_self m (sp0 + 0x40#64) ist'
    rwa [hist_len] at h
  have hag2 : AgreesOutside m₁ m₂ (sp0 + 63#64) 1 :=
    (AgreesOutside.rfl' m₁ (sp0 + 63#64) 1).write8 (by simp only [InRegion]; bv_omega)
  have hf64_12 : Frame m₁ m₂ [(sp0, 64)] :=
    (Frame.refl m₁ [(sp0, 64)]).trans_agreesOutside_sub (rbase := sp0) (rlen := 64)
      (by simp) (by bv_omega) hag2
  have hf96_02 : Frame m m₂ [(sp0, 96)] :=
    ((Frame.refl m [(sp0, 96)]).trans_agreesOutside_sub (rbase := sp0) (rlen := 96)
      (by simp) (by bv_omega) hag1).trans
      (hf64_12.mono fun a ha r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        have := ha (sp0, 96) (by simp)
        unfold OutsideRegion at this ⊢; bv_omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Memory.read8_write8_same m₁ (sp0 + 63#64) (BitVec.ofNat 8 nrem)
  · rw [hf64_12.readBytes_eq ?_ (by decide)]
    · have h := Bytes.readBytes_writeBytes_same m (sp0 + 0x40#64) ist' (by rw [hist_len]; decide)
      rwa [hist_len] at h
    · intro r hr; simp only [List.mem_singleton] at hr; subst hr
      exact Extract.disj_sp0_zero_off sp0 64 0x40#64 32 (by decide)
  · rw [hf96_02.read64_eq ?_, hcnt1]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 96 0x60#64 8 (by decide)
  · rw [hf96_02.readBytes_eq ?_ (by decide), hout]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 96 0x68#64 32 (by decide)
  · rw [hf96_02.read64_eq ?_, hcnt2]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 96 0x88#64 8 (by decide)

theorem HmacStGen.of_memcpy_rem {m : Memory} {sp0 : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState} {key blocks rem : List (BitVec 8)}
    (hmod : blocks.length % 64 = 0)
    (hblk_le : blocks.length ≤ 192)
    (hrem_lt : rem.length < 56)
    (hpos : m.read8 (sp0 + 0x3f#64) = BitVec.ofNat 8 rem.length)
    (hist : m.readBytes (sp0 + 0x40#64) 32 =
      shaStateBytes ((chunks64 blocks).foldl F (hmacInnerInit F key)))
    (hcnt1 : m.read64 (sp0 + 0x60#64) = BitVec.ofNat 64 (1 + blocks.length / 64))
    (hout : m.readBytes (sp0 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key))
    (hcnt2 : m.read64 (sp0 + 0x88#64) = 1#64) :
    HmacStGen (m.writeBytes sp0 rem) sp0 F key blocks rem := by
  let m' := m.writeBytes sp0 rem
  have hag : AgreesOutside m m' sp0 rem.length :=
    ProofLib.AgreesOutside.writeBytes_self m sp0 rem
  have hf63 : Frame m m' [(sp0, 63)] :=
    (Frame.refl m [(sp0, 63)]).trans_agreesOutside_sub (rbase := sp0) (rlen := 63)
      (by simp) (by bv_omega) hag
  refine ⟨hmod, hblk_le, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Bytes.readBytes_writeBytes_same m sp0 rem (by omega)
  · have hout_rem : OutsideRegion sp0 rem.length (sp0 + 0x3f#64) := by
      simp only [OutsideRegion]; bv_omega
    rw [hag.1 (sp0 + 0x3f#64) hout_rem, hpos]
  · rw [hf63.readBytes_eq ?_ (by decide), hist]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 63 0x40#64 32 (by decide)
  · rw [hf63.read64_eq ?_, hcnt1]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 63 0x60#64 8 (by decide)
  · rw [hf63.readBytes_eq ?_ (by decide), hout]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 63 0x68#64 32 (by decide)
  · rw [hf63.read64_eq ?_, hcnt2]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    exact Extract.disj_sp0_zero_off sp0 63 0x88#64 8 (by decide)

end CryptoVerification.E2E.Pqxdh.ResponderCore
