/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
import ProofLib.Sep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.CodeLayout

/-!
# `AdvanceChainKey` Sub-Segment of the `consume_message_key` Store Loop

Symbolic execution from `cmkAdvanceChainKeyPC` (`+0x474`) to the loop back-edge (`+0x334` or
`+0x4dc`): computes `hmac_sha256(ckc.key, [0x02])`, increments `ckc.index` (non-overflowing since
`ckc.index < x.counter`), writes the updated chain key to `x.ckA`, and branches on `ck'.index < x.counter`.
-/

public section

namespace CryptoVerification.LibsignalSession.StoreLoop

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel
open CryptoVerification.LibsignalSession
open ProofLib.ProgramReflection

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

/-! ## Bit-Vector Byte Packing and Unpacking Lemmas -/

theorem extractLsb'_shiftLeft8_or_zero (w : Nat) (hw : 8 ≤ w) (acc : BitVec w) (b : BitVec 8) :
    ((acc <<< 8) ||| b.zeroExtend w).extractLsb' 0 8 = b := by
  ext i hi
  simp [hi]
  omega

theorem extractLsb'_shiftLeft8_or_succ (w : Nat) (acc : BitVec w) (b : BitVec 8) (k : Nat)
    (hk : 8 * (k + 1) + 8 ≤ w) :
    ((acc <<< 8) ||| b.zeroExtend w).extractLsb' (8 * (k + 1)) 8 =
      acc.extractLsb' (8 * k) 8 := by
  ext i hi
  have h1 : ¬ (8 * (k + 1) + i < 8) := by omega
  have hltw : 8 * (k + 1) + i < w := by omega
  have hsub : 8 * (k + 1) + i - 8 = 8 * k + i := by omega
  have hb : b.getLsbD (8 * (k + 1) + i) = false := BitVec.getLsbD_of_ge b _ (by omega)
  simp [h1, hltw, hsub, hb]
  rfl

def bytesOfBV_shared_lb {w : Nat} (n : Nat) (v : BitVec w) : List (BitVec 8) :=
  (List.range n).map fun j => v.extractLsb' (8 * j) 8

@[expose] def packBV_shared_lb (w : Nat) (bs : List (BitVec 8)) : BitVec w :=
  bs.foldr (fun b acc => (acc <<< 8) ||| b.zeroExtend w) 0

theorem bytesOfBV_packBV (w : Nat) :
    ∀ (bs : List (BitVec 8)), 8 * bs.length ≤ w → bytesOfBV_shared_lb bs.length (packBV_shared_lb w bs) = bs
  | [], _ => rfl
  | b :: bs, hlen => by
    have hlen_cons : 8 * (bs.length + 1) ≤ w := hlen
    unfold bytesOfBV_shared_lb
    rw [packBV_shared_lb, List.foldr_cons, ← packBV_shared_lb]
    simp only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
      Nat.mul_zero, extractLsb'_shiftLeft8_or_zero w (by omega), List.cons.injEq]
    refine ⟨trivial, ?_⟩
    have hmap :
        List.map ((fun j => ((packBV_shared_lb w bs <<< 8) ||| b.zeroExtend w).extractLsb' (8 * j) 8) ∘ Nat.succ)
          (List.range bs.length) =
        bytesOfBV_shared_lb bs.length (packBV_shared_lb w bs) := by
      unfold bytesOfBV_shared_lb
      apply List.map_congr_left
      intro k hk
      rw [List.mem_range] at hk
      exact extractLsb'_shiftLeft8_or_succ w (packBV_shared_lb w bs) b k (by omega)
    rw [hmap]
    exact bytesOfBV_packBV w bs (by omega)

theorem keyToBytes32_bytesToKey32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    keyToBytes32 (bytesToKey32 bs) = bs := by
  have h1 : keyToBytes32 (bytesToKey32 bs) = bytesOfBV_shared_lb bs.length (packBV_shared_lb 256 bs) := by
    rw [h]
    unfold keyToBytes32 bytesOfBV_shared_lb bytesToKey32 packBV_shared_lb
    rw [List.ofFn_eq_map]
    rfl
  rw [h1]
  exact bytesOfBV_packBV 256 bs (by omega)

@[expose] def pack64 (bs : List (BitVec 8)) : BitVec 64 := packBV_shared_lb 64 bs

theorem unpack64_pack64 (bs : List (BitVec 8)) (h : bs.length = 8) :
    unpack64 (pack64 bs) = bs := by
  have h1 : unpack64 (pack64 bs) = bytesOfBV_shared_lb bs.length (packBV_shared_lb 64 bs) := by
    rw [h]
    unfold unpack64 bytesOfBV_shared_lb pack64
    rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
    rfl
  rw [h1]
  exact bytesOfBV_packBV 64 bs (by omega)

theorem pointsToBytes_8_eq_pointsTo64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 8) :
    (a ↦ₛ bs) = (a ↦₆₄ pack64 bs) := by
  rw [pointsTo64_eq_pointsToBytes, unpack64_pack64 bs h]

theorem pointsToBytes_32_eq_pointsTo64 (a : BitVec 64) (bs : List (BitVec 8)) (h : bs.length = 32) :
    (a ↦ₛ bs) =
      ((a ↦₆₄ pack64 (bs.take 8)) ∗
       ((a + 8#64) ↦₆₄ pack64 ((bs.drop 8).take 8)) ∗
       ((a + 16#64) ↦₆₄ pack64 ((bs.drop 16).take 8)) ∗
       ((a + 24#64) ↦₆₄ pack64 (bs.drop 24))) := by
  have hsplit :
      bs = bs.take 8 ++ ((bs.drop 8).take 8 ++ ((bs.drop 16).take 8 ++ bs.drop 24)) := by
    have h24 : bs.drop 24 = (bs.drop 16).drop 8 := by simp [List.drop_drop]
    have h16 : bs.drop 16 = (bs.drop 8).drop 8 := by simp [List.drop_drop]
    rw [h24, List.take_append_drop, h16, List.take_append_drop, List.take_append_drop]
  have h0 : (bs.take 8).length = 8 := by simp [h]
  have h1 : ((bs.drop 8).take 8).length = 8 := by simp [h]
  have h2 : ((bs.drop 16).take 8).length = 8 := by simp [h]
  have h3 : (bs.drop 24).length = 8 := by simp [h]
  conv => lhs; rw [hsplit]
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
      h0, h1, h2,
      pointsToBytes_8_eq_pointsTo64 a (bs.take 8) h0,
      pointsToBytes_8_eq_pointsTo64 _ ((bs.drop 8).take 8) h1,
      pointsToBytes_8_eq_pointsTo64 _ ((bs.drop 16).take 8) h2,
      pointsToBytes_8_eq_pointsTo64 _ (bs.drop 24) h3]
  have ha8 : a + BitVec.ofNat 64 8 = a + 8#64 := rfl
  have ha16 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 16#64 := by bv_omega
  have ha24 : a + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 + BitVec.ofNat 64 8 = a + 24#64 := by bv_omega
  rw [ha24, ha16, ha8]

theorem leBytes_four_eq_unpack32 (w : BitVec 32) :
    leBytes 4 w.toNat = unpack32 w := by
  unfold leBytes unpack32 BitVec.extractLsb'
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map, Nat.shiftRight_eq_div_pow]
  rfl

theorem chainKeyBytes_pointsTo (a : BitVec 64) (ck : ChainKey) :
    (a ↦ₛ chainKeyBytes ck) =
      (a ↦ₛ keyToBytes32 ck.key) ∗ ((a + 32#64) ↦₃₂ ck.index) := by
  unfold chainKeyBytes
  have hlen : (keyToBytes32 ck.key).length = 32 := by simp [keyToBytes32]
  rw [pointsToBytes_append, hlen, leBytes_four_eq_unpack32, ← pointsTo32_eq_pointsToBytes]

private theorem pointsTo8_eq_pointsToBytes_singleton (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

theorem memRegion_one_eq_exists_pointsTo8 (a : BitVec 64) :
    memRegion a 1 = ∃∗ b : BitVec 8, (a ↦₈ b) :=
  IsBlock.eq_of_iff (IsBlock.memRegion a 1) (IsBlock.sepExists fun b => IsBlock.pointsTo8 a b) fun m =>
    { mp := fun _ => ⟨m.read8 a, rfl⟩, mpr := fun _ => trivial }

theorem pointsTo8_entails_memRegion_one (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) ⊢ memRegion a 1 := by
  sep_interval

/-! ## Stack and Frame Splitting Lemmas -/

private theorem stackAt_7712_split_2048 (sp0 : BitVec 64) :
    stackAt (sp0 - 480#64) 7712 =
      memRegion (sp0 - 8192#64) 5664 ∗ stackAt (sp0 - 480#64) 2048 := by
  dsimp only [stackAt]; sep_interval_eq

private theorem memRegion_256_advanceChainKey_split (sp0 : BitVec 64) :
    memRegion (sp0 - 352#64) 256 =
      ∃∗ b320 : BitVec 8,
        ((sp0 - 320#64) ↦₈ b320) ∗
        memRegion (sp0 - 319#64) 31 ∗
        memRegion (sp0 - 224#64) 32 ∗
        (memRegion (sp0 - 352#64) 32 ∗
         memRegion (sp0 - 288#64) 64 ∗
         memRegion (sp0 - 192#64) 96) := by
  simp only [← sepExists_sepConj_left]
  sep_interval_eq

private theorem memRegion_32_eq_exists_pointsTo64_4 (a : BitVec 64) :
    memRegion a 32 =
      ∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64,
        (a ↦₆₄ t0) ∗ ((a + 8#64) ↦₆₄ t1) ∗ ((a + 16#64) ↦₆₄ t2) ∗ ((a + 24#64) ↦₆₄ t3) := by
  simp only [← sepExists_sepConj_left, ← sepExists_sepConj_right]
  sep_interval_eq

theorem pointsTo64_4_entails_memRegion_32 (a : BitVec 64)
    (t0 t1 t2 t3 : BitVec 64) :
    ((a ↦₆₄ t0) ∗ ((a + 8#64) ↦₆₄ t1) ∗ ((a + 16#64) ↦₆₄ t2) ∗ ((a + 24#64) ↦₆₄ t3)) ⊢
      memRegion a 32 := by
  sep_interval

private def advanceChainKeyFrameAt (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (s0 : State) : SepProp :=
  ratchetAt A x.self G' st' ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  memRegion x.ret 88 ∗
  (logAddr ↦₆₄ 0#64) ∗
  memRegion (s0.sp - 8192#64) 5664 ∗
  memRegion (s0.sp - 480#64) 112 ∗
  ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
  memRegion (s0.sp - 360#64) 4 ∗
  memRegion (s0.sp - 352#64) 32 ∗
  memRegion (s0.sp - 288#64) 64 ∗
  memRegion (s0.sp - 192#64) 96 ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

private theorem cmkLoopHeapAt_advanceChainKey_split (A : RustAlloc) (logAddr : BitVec 64)
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (st' : RatchetState) (ckc : ChainKey) (s0 : State) :
    cmkLoopHeapAt A logAddr x G' st' ckc s0 =
      ∃∗ b320 : BitVec 8,
        ((s0.sp - 320#64) ↦₈ b320) ∗
        (memRegion (s0.sp - 224#64) 32 ∗
         (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
         stackAt (s0.sp - 480#64) 2048 ∗
         memRegion (s0.sp - 319#64) 31 ∗
         ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
         ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
         advanceChainKeyFrameAt A logAddr x G' st' s0) := by
  unfold cmkLoopHeapAt cmkLoopFrame advanceChainKeyFrameAt
  rw [chainKeyBytes_pointsTo x.ckA ckc,
      stackAt_7712_split_2048 s0.sp,
      memRegion_256_advanceChainKey_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext b320
  sep_interval_eq

private theorem advanceChainKeyPost_entails_cmkLoopHeapAt (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (logAddr : BitVec 64) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (ckc : ChainKey)
    (q0_lo q0_hi q1_lo q1_hi : BitVec 64)
    (hq0_lo : q0_lo = pack64 ((hmacWith F (keyToBytes32 ckc.key) [2#8]).take 8))
    (hq0_hi : q0_hi = pack64 (((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 8).take 8))
    (hq1_lo : q1_lo = pack64 (((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 16).take 8))
    (hq1_hi : q1_hi = pack64 ((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 24))
    (s0 : State) :
    (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
     ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
     ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
     ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
     ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
     ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
     ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
     ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
     ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
     (x.ckA ↦₆₄ q0_lo) ∗
     ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
     ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
     ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
     ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
     stackAt (s0.sp - 480#64) 2048 ∗
     advanceChainKeyFrameAt A logAddr x G' st' s0) ⊢
      cmkLoopHeapAt A logAddr x G' st' (chainStepN F 1 ckc) s0 := by
  let bs := hmacWith F (keyToBytes32 ckc.key) [2#8]
  have hbs : bs.length = 32 := hmacWith_length F (keyToBytes32 ckc.key) [2#8]
  have hck'_key : keyToBytes32 (chainStepN F 1 ckc).key = bs :=
    keyToBytes32_bytesToKey32 bs hbs
  have hck'_idx : (chainStepN F 1 ckc).index = ckc.index + 1#32 := rfl
  unfold cmkLoopHeapAt cmkLoopFrame advanceChainKeyFrameAt
  rw [chainKeyBytes_pointsTo x.ckA (chainStepN F 1 ckc), hck'_key, hck'_idx,
      pointsToBytes_32_eq_pointsTo64 x.ckA bs hbs, ← hq0_lo, ← hq0_hi, ← hq1_lo, ← hq1_hi]
  dsimp only [stackAt]
  sep_interval

/-! ## Symbolic Execution of `AdvanceChainKey` -/

theorem add_one_ne_zero_of_lt {idx ctr : BitVec 32} (h : idx < ctr) :
    idx + 1#32 ≠ 0#32 := by
  intro heq
  have hlt_nat : idx.toNat < ctr.toNat := BitVec.lt_def.mp h
  have hctr : ctr.toNat < 2 ^ 32 := ctr.isLt
  have hadd : (idx + 1#32).toNat = idx.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0 : (idx + 1#32).toNat = 0 := by rw [heq]; rfl
  omega

private theorem advanceChainKey_preHmac_placed_wp [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (b320 : BitVec 8) (s0 s : State)
    (hstat : s.status = .Running)
    (hpc : s.pc = (blkPl_24).base + 1140#64)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) s
      ((s0.sp - 320#64) ↦₈ b320)
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ((s0.sp - 320#64) ↦₈ 2#8) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x0 = s0.sp - 224#64 ∧
        sf.readReg64 .x1 = x.ckA ∧
        sf.readReg64 .x2 = 32#64 ∧
        sf.readReg64 .x3 = s0.sp - 320#64 ∧
        sf.readReg64 .x4 = 1#64 ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x22 = x.theirA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.readReg64 .x30 = (blkPl_24).base + 1172#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  wp_steps
  wp_done

private theorem advanceChainKey_hmac_placed_wp [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState)
    (H : String → Option (State → State))
    (xg : ConsumeMessageKeyGhost) (ckc : ChainKey) (s0 s : State)
    (hhmac : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s))
    (hstat : s.status = .Running)
    (hpc : s.pc = lsmpl.base 73)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = s0.sp - 224#64)
    (hx1 : s.readReg64 .x1 = xg.ckA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hx3 : s.readReg64 .x3 = s0.sp - 320#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = xg.ckA)
    (hx22 : s.readReg64 .x22 = xg.theirA)
    (hx23 : s.readReg64 .x23 = xg.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx30 : s.readReg64 .x30 = (blkPl_24).base + 1172#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H) ((blkPl_24).base + 1172#64) s
      (memRegion (s0.sp - 224#64) 32 ∗
       (xg.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
       stackAt (s0.sp - 480#64) 2048)
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (((s0.sp - 224#64) ↦ₛ hmacWith F (keyToBytes32 ckc.key) [2#8]) ∗
             (xg.ckA ↦ₛ keyToBytes32 ckc.key) ∗
             ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
             stackAt (s0.sp - 480#64) 2048) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = xg.ckA ∧
        sf.readReg64 .x22 = xg.theirA ∧
        sf.readReg64 .x23 = xg.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  wp_call hhmac (s0.sp - 224#64, xg.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [2#8])
  wp_done

private theorem advanceChainKey_postHmac_placed_wp [LibsignalPlacement]
    (H : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (ckc : ChainKey)
    (q0_lo q0_hi q1_lo q1_hi k0 k1 k2 k3 t0 t1 t2 t3 : BitVec 64)
    (s0 s : State)
    (hstat : s.status = .Running)
    (hpc : s.pc = (blkPl_24).base + 1172#64)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlt : ckc.index < x.counter) :
    SepWP ((blkPC_24).rebase (blkPl_24).base H)
      (if (ckc.index + 1#32) < x.counter
       then (blkPl_24).base + 820#64
       else (blkPl_24).base + 1244#64)
      s
      (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦₆₄ t0) ∗
       ((s0.sp - 312#64) ↦₆₄ t1) ∗
       ((s0.sp - 304#64) ↦₆₄ t2) ∗
       ((s0.sp - 296#64) ↦₆₄ t3) ∗
       (x.ckA ↦₆₄ k0) ∗
       ((x.ckA + 8#64) ↦₆₄ k1) ∗
       ((x.ckA + 16#64) ↦₆₄ k2) ∗
       ((x.ckA + 24#64) ↦₆₄ k3) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index))
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
             ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
             ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
             ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
             ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
             ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
             ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
             ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
             ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
             (x.ckA ↦₆₄ q0_lo) ∗
             ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
             ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
             ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
             ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x26 = x.theirA ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x28 = (ckc.index + 1#32).zeroExtend 64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have hne0 : ckc.index + 1#32 ≠ 0#32 := add_one_ne_zero_of_lt hlt
  wp_steps
  wp_if hloop
  · have hlt' : ckc.index + 1#32 < x.counter := BitVec.ult_iff_lt.mp hloop
    simp only [hlt', ↓reduceIte]
    wp_done
  · have hnlt' : ¬ (ckc.index + 1#32 < x.counter) := mt BitVec.ult_iff_lt.mpr hloop
    simp only [hnlt', ↓reduceIte]
    wp_steps
    wp_done

private theorem advanceChainKey_placed_ok_of_hmac [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State))
    {Inv : Memory → Prop}
    (hinv_kf : ∀ m m', Inv m → m.KeepsFrozen m' → Inv m')
    (hhmac_at : ∀ {s1 : State}, Inv s1.mem →
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s1))
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (st' : RatchetState)
    (ckc : CryptoGames.LibsignalSession.ChainKey) (R : SepProp) (s0 sD : State)
    (hlt : ckc.index < x.counter)
    (hD : AdvanceChainKeyState_placed A x G' st' ckc R s0 sD)
    (hL : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded sD.mem)
    (hinv : Inv sD.mem) :
    let ck' := chainStepN F 1 ckc
    let nextPC := if ck'.index < x.counter then cmkLoopPC_placed else cmkEpiloguePC_placed
    ∃ s', Steps ((blkPC_24).rebase (blkPl_24).base H) sD s' ∧
      CmkLoopState_placed A x G' st' ck' R nextPC s0 s' := by
  dsimp only
  rcases hD with
    ⟨hpc,
     ⟨hstat, hsp, hsp0_align, _hsp_align, hx29, htr, hcl, hvregs⟩,
     ⟨hx19, hx21, hx22, hx23, hx27⟩,
     hmem⟩
  have hpc' : sD.pc = (blkPl_24).base + 1140#64 := hpc
  rw [cmkLoopHeap_placed_eq_at, cmkLoopHeapAt_advanceChainKey_split A lsLogFilterAddr x G' st' ckc s0] at hmem
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmem
  rcases hmem with ⟨b320, hmem⟩
  rw [sepConj_assoc] at hmem
  let R1 : SepProp :=
    (memRegion (s0.sp - 224#64) 32 ∗
     (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
     stackAt (s0.sp - 480#64) 2048 ∗
     memRegion (s0.sp - 319#64) 31 ∗
     ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
     ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
     advanceChainKeyFrameAt A lsLogFilterAddr x G' st' s0) ∗ R
  rcases (advanceChainKey_preHmac_placed_wp H x b320 s0 sD hstat hpc' hsp hsp0_align
      hx19 hx21 hx22 hx23 hx27 hx29 ⟨htr, hvregs⟩).elim hmem hL with
    ⟨s1, hsteps1, ⟨_hpc1, hstat1, P_f1, hm1, hpost1,
      hsp1, _hsp1_align, htr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1,
      hx19_1, hx21_1, hx22_1, hx23_1, hx27_1, hx29_1, hx30_1⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem1 := hpost1 R1 hm1
  rw [pointsTo8_eq_pointsToBytes_singleton (s0.sp - 320#64) 2#8] at hmem1
  let R2 : SepProp :=
    memRegion (s0.sp - 319#64) 31 ∗
    ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
    ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
    advanceChainKeyFrameAt A lsLogFilterAddr x G' st' s0 ∗ R
  have hmem1' : s1.mem ⊨
      (memRegion (s0.sp - 224#64) 32 ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
       stackAt (s0.sp - 480#64) 2048) ∗ R2 :=
    Satisfies.mono (by dsimp only [R1, R2]; bi_entail) hmem1
  have hinv1 : Inv s1.mem := hinv_kf _ _ hinv hsteps1.keepsFrozen
  have hL1 : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s1.mem := hsteps1.codeLoaded hL
  rcases (advanceChainKey_hmac_placed_wp F H (xg := x) ckc s0 s1 (hhmac_at hinv1) hstat1 _hpc1 hsp1 hsp0_align
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx19_1 hx21_1 hx22_1 hx23_1 hx27_1 hx29_1 hx30_1
      htr1).elim hmem1' hL1 with
    ⟨s2, hsteps2, ⟨_hpc2, hstat2, P_f2, hm2, hpost2,
      hsp2, _hsp2_align, htr2, hx19_2, hx21_2, hx22_2, hx23_2, hx27_2, hx29_2⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem2 := hpost2 R2 hm2
  let bs := hmacWith F (keyToBytes32 ckc.key) [2#8]
  have hbs : bs.length = 32 := hmacWith_length F (keyToBytes32 ckc.key) [2#8]
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  have hmem2' : s2.mem ⊨
      memRegion (s0.sp - 320#64) 32 ∗
      (((s0.sp - 224#64) ↦ₛ bs) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       stackAt (s0.sp - 480#64) 2048 ∗
       advanceChainKeyFrameAt A lsLogFilterAddr x G' st' s0 ∗ R) := by
    have h320 : ((s0.sp - 320#64) ↦ₛ [2#8]) ∗ memRegion (s0.sp - 319#64) 31 ⊢
        memRegion (s0.sp - 320#64) 32 := by sep_interval
    exact Satisfies.mono (Entails.trans (by dsimp only [R2]; bi_entail) (sepConj_mono_left h320)) hmem2
  rw [memRegion_32_eq_exists_pointsTo64_4 (s0.sp - 320#64),
      pointsToBytes_32_eq_pointsTo64 (s0.sp - 224#64) bs hbs,
      pointsToBytes_32_eq_pointsTo64 x.ckA (keyToBytes32 ckc.key) hkey_len] at hmem2'
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmem2'
  rcases hmem2' with ⟨t0, t1, t2, t3, hmem2'⟩
  let q0_lo := pack64 (bs.take 8)
  let q0_hi := pack64 ((bs.drop 8).take 8)
  let q1_lo := pack64 ((bs.drop 16).take 8)
  let q1_hi := pack64 (bs.drop 24)
  let k0 := pack64 ((keyToBytes32 ckc.key).take 8)
  let k1 := pack64 (((keyToBytes32 ckc.key).drop 8).take 8)
  let k2 := pack64 (((keyToBytes32 ckc.key).drop 16).take 8)
  let k3 := pack64 ((keyToBytes32 ckc.key).drop 24)
  let R3 : SepProp := stackAt (s0.sp - 480#64) 2048 ∗ advanceChainKeyFrameAt A lsLogFilterAddr x G' st' s0 ∗ R
  have hmem2_ready : s2.mem ⊨
      (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦₆₄ t0) ∗
       ((s0.sp - 312#64) ↦₆₄ t1) ∗
       ((s0.sp - 304#64) ↦₆₄ t2) ∗
       ((s0.sp - 296#64) ↦₆₄ t3) ∗
       (x.ckA ↦₆₄ k0) ∗
       ((x.ckA + 8#64) ↦₆₄ k1) ∗
       ((x.ckA + 16#64) ↦₆₄ k2) ∗
       ((x.ckA + 24#64) ↦₆₄ k3) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index)) ∗ R3 :=
    Satisfies.mono (by dsimp only [R3, q0_lo, q0_hi, q1_lo, q1_hi, k0, k1, k2, k3]; bi_entail) hmem2'
  have hL2 : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s2.mem := hsteps2.codeLoaded hL1
  rcases (advanceChainKey_postHmac_placed_wp H x ckc q0_lo q0_hi q1_lo q1_hi k0 k1 k2 k3 t0 t1 t2 t3
      s0 s2 hstat2 _hpc2 hsp2 hsp0_align hx19_2 hx21_2 hx22_2 hx23_2 hx27_2 hx29_2
      htr2 hlt).elim hmem2_ready hL2 with
    ⟨s', hsteps3, ⟨hpc', hstat', P_f3, hm3, hpost3,
      hsp', hsp'_align, htr', hx19', hx21', hx23', hx26', hx27', hx28', hx29'⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem3 := hpost3 R3 hm3
  have hmem_final : s'.mem ⊨ cmkLoopHeapAt A lsLogFilterAddr x G' st' (chainStepN F 1 ckc) s0 ∗ R := by
    refine Satisfies.mono (Entails.trans ?_
      (sepConj_mono_left
        (advanceChainKeyPost_entails_cmkLoopHeapAt F A lsLogFilterAddr x G' st' ckc q0_lo q0_hi q1_lo q1_hi rfl rfl rfl rfl s0)))
      hmem3
    dsimp only [R3]
    bi_entail
  rw [← cmkLoopHeap_placed_eq_at] at hmem_final
  have hsteps_all : Steps ((blkPC_24).rebase (blkPl_24).base H) sD s' :=
    (hsteps1.trans hsteps2).trans hsteps3
  refine ⟨s', hsteps_all, ?_⟩
  refine ⟨hpc',
    ⟨hstat', hsp', hsp0_align, hsp'_align, hx29', htr'.1,
     hcl.of_keepsFrozen hsteps_all.keepsFrozen, htr'.2⟩,
    ⟨hx21', hx23', hx26', hx27', hx28'⟩,
    fun _ => hx19',
    hmem_final⟩

theorem advanceChainKey_placed_ok [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    AdvanceChainKeyPlacedSpec F A H := by
  intro hHmac x G' st' ckc R s0 sD hlt hD hL
  let ⟨_, ⟨_, _, _, _, _, _, hcl, _⟩, _⟩ := hD
  exact advanceChainKey_placed_ok_of_hmac F A H
    (Inv := LibsignalCodeLoaded lsmpl)
    (fun _ _ h hkf => h.of_keepsFrozen hkf)
    (fun h => hmac_placed_ok_at_state hHmac h)
    x G' st' ckc R s0 sD hlt hD hL hcl

theorem advanceChainKey_placed_ro_ok [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    AdvanceChainKeyPlacedRoSpec F A H := by
  intro hHmac x G' st' ckc R s0 sD hlt hD hL hro
  let ⟨_, ⟨_, _, _, _, _, _, hcl, _⟩, _⟩ := hD
  exact advanceChainKey_placed_ok_of_hmac F A H
    (Inv := fun m => LibsignalCodeLoaded lsmpl m ∧ LibsignalRoLoaded lsmpl m)
    (fun _ _ ⟨hc, hr⟩ hkf => ⟨hc.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen hr hkf⟩)
    (fun ⟨hc, hr⟩ => hmac_placed_ro_ok_at_state hHmac hc hr)
    x G' st' ckc R s0 sD hlt hD hL ⟨hcl, hro⟩

end CryptoVerification.LibsignalSession.StoreLoop
