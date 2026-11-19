/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSteps -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import ProofLib.RegChain
import ProofLib.Sep
meta import Lean
import ProofLib.SepLogic.WP.Apply

/-!
# Segment S0 (`IdentityKeys`) & Identity/Pre-Key Callee Proofs

Verifies Segment S0 (`+0x000 → +0x1d8`) of `try_decrypt_with_state` along with relocatable
`[LibsignalPlacement]` contracts for `SessionState::remote_identity_key` (block `29`) and
`SessionState::clear_unacknowledged_pre_key_message` (block `35`).
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

run_meta do
  let env ← Lean.getEnv
  for (h, ks) in #[(``vecGhostAt, #[2]), (``sessionStateRestAt, #[1])] do
    let n := Lean.mkPrivateName env (((ks.foldl Lean.Name.mkNum ProofLib.Sep.sepKeyMarker).str "_TARGET_") ++ h)
    unless env.contains n do
      Lean.withExporting (isExporting := false) do
        Lean.addDecl <| .defnDecl { name := n, levelParams := [], type := .const ``Unit [], value := .const ``Unit.unit [], hints := .abbrev, safety := .safe }

private theorem tapeAfter_zero (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest ⊢ tapeAfter ctl cur rest 0 := by
  unfold tapeAt tapeAfter
  have hcur : cur + BitVec.ofNat 64 0 = cur := by bv_omega
  have hlen : rest.length - 0 = rest.length := Nat.sub_zero _
  rw [hcur, hlen]
  exact Entails.pure_left (fun _ => Entails.refl _)

open Arm64.Obj CryptoVerification CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.FindReceiverChainIndex

private theorem pointsToBytes_drop_split_placed (a : BitVec 64) (bs : List (BitVec 8)) (i k : Nat)
    (h : i + k ≤ bs.length) :
    ((a + BitVec.ofNat 64 i) ↦ₛ bs.drop i) =
      ((a + BitVec.ofNat 64 i) ↦ₛ (bs.drop i).take k) ∗ ((a + BitVec.ofNat 64 (i + k)) ↦ₛ bs.drop (i + k)) := by
  have h1 := pointsToBytes_take_drop (a + BitVec.ofNat 64 i) k (bs.drop i) (by simp; omega)
  have hadd : a + BitVec.ofNat 64 i + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (i + k) := by bv_omega
  rw [List.drop_drop, hadd] at h1; exact h1

private theorem vecGhostAt_eq_of_nil_placed (A : RustAlloc) (g : VecGhost) (a : BitVec 64) (hnil : g.bytes = []) :
    vecGhostAt A g a =
      (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗ vecU8Buf A g.cap g.ptr g.bytes := by
  unfold vecGhostAt; rw [vecU8At_eq_header_sep_buf, hnil]
  change ((a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64)) ∗ vecU8Buf A g.cap g.ptr [] =
    (a ↦₆₄ g.cap) ∗ ((a + 8#64) ↦₆₄ g.ptr) ∗ ((a + 16#64) ↦₆₄ 0#64) ∗ vecU8Buf A g.cap g.ptr []
  simp only [sepConj_assoc]

private theorem pointsTo16_zero_placed (a : BitVec 64) : (a ↦₁₆ 0#16) = (a ↦₈ 0#8) ∗ ((a + 1#64) ↦₈ 0#8) := by
  simp only [pointsTo16, BitVec.add_zero]; rfl

private theorem pointsTo16_256_placed (a : BitVec 64) : (a ↦₁₆ 256#16) = (a ↦₈ 0#8) ∗ ((a + 1#64) ↦₈ 1#8) := by
  simp only [pointsTo16, BitVec.add_zero]; rfl

private theorem memRegion_34_none_split_placed (ret : BitVec 64) :
    memRegion ret 34 = (∃∗ h0 : BitVec 16, ret ↦₁₆ h0) ∗ memRegion (ret + 2#64) 32 := by
  sep_interval_eq

private theorem stackAt_remoteIdentityKey_none_split_placed (sp : BitVec 64) :
    stackAt sp remoteIdentityKeyStack =
      memRegion (sp - 144#64) 112 ∗ cells (sp - 32#64) 3 ∗ memRegion (sp - 8#64) 8 := by
  simp only [stackAt, remoteIdentityKeyStack]; sep_interval_eq

private theorem sevenLo_eq_sevenHi_placed (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6)) =
      ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))) := by
  rw [← pointsToBytes4_eq_pointsTo32, ← pointsToBytes4_eq_pointsTo32]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sevenLo_eq_sevenHi'_placed (a a1 a2 a3 a4 a5 a6 : BitVec 64)
    (h1 : a + 1#64 = a1) (h2 : a + 2#64 = a2) (h3 : a + 3#64 = a3)
    (h4 : a + 4#64 = a4) (h5 : a + 5#64 = a5) (h6 : a + 6#64 = a6)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ (a4 ↦₈ b4) ∗ (a5 ↦₈ b5) ∗ (a6 ↦₈ b6) ∗ rest) =
      ((a ↦₈ b0) ∗ (a1 ↦₈ b1) ∗ (a2 ↦₈ b2) ∗ (a3 ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) := by
  subst h1 h2 h3 h4 h5 h6
  simpa only [sepConj_assoc] using congrArg (· ∗ rest) (sevenLo_eq_sevenHi_placed a b0 b1 b2 b3 b4 b5 b6)

private theorem pointsTo16_32_16_eq_pointsTo64_placed (a : BitVec 64)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16) :
    ((a ↦₁₆ v7) ∗ ((a + 2#64) ↦₃₂ v9) ∗ ((a + 6#64) ↦₁₆ v13)) = (a ↦₆₄ (v13 ++ v9 ++ v7)) := by
  simp only [pointsTo16, pointsTo32, pointsTo64, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  rw [(IdentityBitVecFacts.extractLsb'_append_lo (v13 ++ v9) v7 0 8 (by decide)).symm,
      (IdentityBitVecFacts.extractLsb'_append_lo (v13 ++ v9) v7 8 8 (by decide)).symm,
      ((IdentityBitVecFacts.extractLsb'_append_hi (v13 ++ v9) v7 16 8 (by decide)).trans (IdentityBitVecFacts.extractLsb'_append_lo v13 v9 0 8 (by decide))).symm,
      ((IdentityBitVecFacts.extractLsb'_append_hi (v13 ++ v9) v7 24 8 (by decide)).trans (IdentityBitVecFacts.extractLsb'_append_lo v13 v9 8 8 (by decide))).symm,
      ((IdentityBitVecFacts.extractLsb'_append_hi (v13 ++ v9) v7 32 8 (by decide)).trans (IdentityBitVecFacts.extractLsb'_append_lo v13 v9 16 8 (by decide))).symm,
      ((IdentityBitVecFacts.extractLsb'_append_hi (v13 ++ v9) v7 40 8 (by decide)).trans (IdentityBitVecFacts.extractLsb'_append_lo v13 v9 24 8 (by decide))).symm,
      ((IdentityBitVecFacts.extractLsb'_append_hi (v13 ++ v9) v7 48 8 (by decide)).trans (IdentityBitVecFacts.extractLsb'_append_hi v13 v9 32 8 (by decide))).symm,
      ((IdentityBitVecFacts.extractLsb'_append_hi (v13 ++ v9) v7 56 8 (by decide)).trans (IdentityBitVecFacts.extractLsb'_append_hi v13 v9 40 8 (by decide))).symm]

private theorem pointsTo16_32_16_eq_pointsTo64'_placed (a a2 a6 : BitVec 64)
    (h2 : a + 2#64 = a2) (h6 : a + 6#64 = a6)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16) (rest : SepProp) :
    ((a ↦₁₆ v7) ∗ (a2 ↦₃₂ v9) ∗ (a6 ↦₁₆ v13) ∗ rest) = ((a ↦₆₄ (v13 ++ v9 ++ v7)) ∗ rest) := by
  subst h2 h6
  simpa only [sepConj_assoc] using congrArg (· ∗ rest) (pointsTo16_32_16_eq_pointsTo64_placed a v7 v9 v13)

private theorem truncate16_zeroExtend32_placed (v : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 32 v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

private theorem vecGhostAt_ss_24_of_nil_placed (A : RustAlloc) (g : VecGhost) (ss : BitVec 64) (hnil : g.bytes = []) :
    vecGhostAt A g (ss + 24#64) =
      ((ss + 24#64) ↦₆₄ g.cap) ∗ ((ss + 32#64) ↦₆₄ g.ptr) ∗ ((ss + 40#64) ↦₆₄ 0#64) ∗ vecU8Buf A g.cap g.ptr g.bytes := by
  rw [vecGhostAt_eq_of_nil_placed A g (ss + 24#64) hnil,
      show ss + 24#64 + 8#64 = ss + 32#64 by bv_omega, show ss + 24#64 + 16#64 = ss + 40#64 by bv_omega]

private theorem vecGhostAt_ss_24_of_pos_placed (A : RustAlloc) (g : VecGhost) (ss : BitVec 64) (hpos : 0 < g.bytes.length) :
    vecGhostAt A g (ss + 24#64) =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      ((ss + 24#64) ↦₆₄ g.cap) ∗ ((ss + 32#64) ↦₆₄ g.ptr) ∗ ((ss + 40#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
      A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
      memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length) := by
  rw [vecGhostAt_eq_of_pos A g (ss + 24#64) hpos,
      show ss + 24#64 + 8#64 = ss + 32#64 by bv_omega, show ss + 24#64 + 16#64 = ss + 40#64 by bv_omega]
  ac_rfl

private theorem remoteKeyChunks_ret_2_placed (ret : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16) (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    remoteKeyChunks (ret + 2#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((ret + 2#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((ret + 6#64) ↦₈ b4) ∗ ((ret + 7#64) ↦₈ b5) ∗
      ((ret + 8#64) ↦₈ b6) ∗ ((ret + 9#64) ↦₁₆ v7) ∗ ((ret + 11#64) ↦₃₂ v9) ∗ ((ret + 15#64) ↦₁₆ v13) ∗
      ((ret + 17#64) ↦₆₄ v15) ∗ ((ret + 25#64) ↦₆₄ v23) ∗ ((ret + 33#64) ↦₈ v31) := by
  dsimp only [remoteKeyChunks]
  rw [IdentityBitVecFacts.add_add_eq_add ret 2#64 6#64 4#64 rfl, IdentityBitVecFacts.add_add_eq_add ret 2#64 7#64 5#64 rfl,
      IdentityBitVecFacts.add_add_eq_add ret 2#64 8#64 6#64 rfl, IdentityBitVecFacts.add_add_eq_add ret 2#64 9#64 7#64 rfl,
      IdentityBitVecFacts.add_add_eq_add ret 2#64 11#64 9#64 rfl, IdentityBitVecFacts.add_add_eq_add ret 2#64 15#64 13#64 rfl,
      IdentityBitVecFacts.add_add_eq_add ret 2#64 17#64 15#64 rfl, IdentityBitVecFacts.add_add_eq_add ret 2#64 25#64 23#64 rfl,
      IdentityBitVecFacts.add_add_eq_add ret 2#64 33#64 31#64 rfl]

private theorem remoteKeyChunks_sp_79_placed (sp : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16) (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    remoteKeyChunks (sp - 79#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((sp - 79#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((sp - 75#64) ↦₈ b4) ∗ ((sp - 74#64) ↦₈ b5) ∗
      ((sp - 73#64) ↦₈ b6) ∗ ((sp - 72#64) ↦₁₆ v7) ∗ ((sp - 70#64) ↦₃₂ v9) ∗ ((sp - 66#64) ↦₁₆ v13) ∗
      ((sp - 64#64) ↦₆₄ v15) ∗ ((sp - 56#64) ↦₆₄ v23) ∗ ((sp - 48#64) ↦₈ v31) := by
  dsimp only [remoteKeyChunks]
  rw [IdentityBitVecFacts.sub_add_eq_sub sp 79#64 75#64 4#64 rfl, IdentityBitVecFacts.sub_add_eq_sub sp 79#64 74#64 5#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub sp 79#64 73#64 6#64 rfl, IdentityBitVecFacts.sub_add_eq_sub sp 79#64 72#64 7#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub sp 79#64 70#64 9#64 rfl, IdentityBitVecFacts.sub_add_eq_sub sp 79#64 66#64 13#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub sp 79#64 64#64 15#64 rfl, IdentityBitVecFacts.sub_add_eq_sub sp 79#64 56#64 23#64 rfl,
      IdentityBitVecFacts.sub_add_eq_sub sp 79#64 48#64 31#64 rfl]

private theorem sevenLo_sp_79_placed (sp : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 79#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((sp - 75#64) ↦₈ b4) ∗ ((sp - 74#64) ↦₈ b5) ∗ ((sp - 73#64) ↦₈ b6) ∗ rest) =
      (((sp - 79#64) ↦₈ b0) ∗ ((sp - 78#64) ↦₈ b1) ∗ ((sp - 77#64) ↦₈ b2) ∗ ((sp - 76#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi'_placed (sp - 79#64) (sp - 78#64) (sp - 77#64) (sp - 76#64) (sp - 75#64) (sp - 74#64) (sp - 73#64)
    (IdentityBitVecFacts.sub_add_eq_sub sp 79#64 78#64 1#64 rfl) (IdentityBitVecFacts.sub_add_eq_sub sp 79#64 77#64 2#64 rfl)
    (IdentityBitVecFacts.sub_add_eq_sub sp 79#64 76#64 3#64 rfl) (IdentityBitVecFacts.sub_add_eq_sub sp 79#64 75#64 4#64 rfl)
    (IdentityBitVecFacts.sub_add_eq_sub sp 79#64 74#64 5#64 rfl) (IdentityBitVecFacts.sub_add_eq_sub sp 79#64 73#64 6#64 rfl) b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_sp_96_placed (sp : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 96#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((sp - 92#64) ↦₈ b4) ∗ ((sp - 91#64) ↦₈ b5) ∗ ((sp - 90#64) ↦₈ b6) ∗ rest) =
      (((sp - 96#64) ↦₈ b0) ∗ ((sp - 95#64) ↦₈ b1) ∗ ((sp - 94#64) ↦₈ b2) ∗ ((sp - 93#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi'_placed (sp - 96#64) (sp - 95#64) (sp - 94#64) (sp - 93#64) (sp - 92#64) (sp - 91#64) (sp - 90#64)
    (IdentityBitVecFacts.sub_add_eq_sub sp 96#64 95#64 1#64 rfl) (IdentityBitVecFacts.sub_add_eq_sub sp 96#64 94#64 2#64 rfl)
    (IdentityBitVecFacts.sub_add_eq_sub sp 96#64 93#64 3#64 rfl) (IdentityBitVecFacts.sub_add_eq_sub sp 96#64 92#64 4#64 rfl)
    (IdentityBitVecFacts.sub_add_eq_sub sp 96#64 91#64 5#64 rfl) (IdentityBitVecFacts.sub_add_eq_sub sp 96#64 90#64 6#64 rfl) b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_sp_136_placed (sp : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 136#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((sp - 132#64) ↦₈ b4) ∗ ((sp - 131#64) ↦₈ b5) ∗ ((sp - 130#64) ↦₈ b6) ∗ rest) =
      (((sp - 136#64) ↦₈ b0) ∗ ((sp - 135#64) ↦₈ b1) ∗ ((sp - 134#64) ↦₈ b2) ∗ ((sp - 133#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi'_placed (sp - 136#64) (sp - 135#64) (sp - 134#64) (sp - 133#64) (sp - 132#64) (sp - 131#64) (sp - 130#64)
    (IdentityBitVecFacts.sub_add_eq_sub sp 136#64 135#64 1#64 rfl) (IdentityBitVecFacts.sub_add_eq_sub sp 136#64 134#64 2#64 rfl)
    (IdentityBitVecFacts.sub_add_eq_sub sp 136#64 133#64 3#64 rfl) (IdentityBitVecFacts.sub_add_eq_sub sp 136#64 132#64 4#64 rfl)
    (IdentityBitVecFacts.sub_add_eq_sub sp 136#64 131#64 5#64 rfl) (IdentityBitVecFacts.sub_add_eq_sub sp 136#64 130#64 6#64 rfl) b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_ret_2_placed (ret : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((ret + 2#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((ret + 6#64) ↦₈ b4) ∗ ((ret + 7#64) ↦₈ b5) ∗ ((ret + 8#64) ↦₈ b6) ∗ rest) =
      (((ret + 2#64) ↦₈ b0) ∗ ((ret + 3#64) ↦₈ b1) ∗ ((ret + 4#64) ↦₈ b2) ∗ ((ret + 5#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi'_placed (ret + 2#64) (ret + 3#64) (ret + 4#64) (ret + 5#64) (ret + 6#64) (ret + 7#64) (ret + 8#64)
    (IdentityBitVecFacts.add_add_eq_add ret 2#64 3#64 1#64 rfl) (IdentityBitVecFacts.add_add_eq_add ret 2#64 4#64 2#64 rfl)
    (IdentityBitVecFacts.add_add_eq_add ret 2#64 5#64 3#64 rfl) (IdentityBitVecFacts.add_add_eq_add ret 2#64 6#64 4#64 rfl)
    (IdentityBitVecFacts.add_add_eq_add ret 2#64 7#64 5#64 rfl) (IdentityBitVecFacts.add_add_eq_add ret 2#64 8#64 6#64 rfl) b0 b1 b2 b3 b4 b5 b6 rest

private theorem pointsTo16_32_16_sp_89_placed (sp : BitVec 64) (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16) (rest : SepProp) :
    (((sp - 89#64) ↦₁₆ v7) ∗ ((sp - 87#64) ↦₃₂ v9) ∗ ((sp - 83#64) ↦₁₆ v13) ∗ rest) = (((sp - 89#64) ↦₆₄ (v13 ++ v9 ++ v7)) ∗ rest) :=
  pointsTo16_32_16_eq_pointsTo64'_placed (sp - 89#64) (sp - 87#64) (sp - 83#64)
    (IdentityBitVecFacts.sub_add_eq_sub sp 89#64 87#64 2#64 rfl) (IdentityBitVecFacts.sub_add_eq_sub sp 89#64 83#64 6#64 rfl) v7 v9 v13 rest

private theorem pointsTo16_32_16_ret_9_placed (ret : BitVec 64) (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16) (rest : SepProp) :
    (((ret + 9#64) ↦₁₆ v7) ∗ ((ret + 11#64) ↦₃₂ v9) ∗ ((ret + 15#64) ↦₁₆ v13) ∗ rest) = (((ret + 9#64) ↦₆₄ (v13 ++ v9 ++ v7)) ∗ rest) :=
  pointsTo16_32_16_eq_pointsTo64'_placed (ret + 9#64) (ret + 11#64) (ret + 15#64)
    (IdentityBitVecFacts.add_add_eq_add ret 9#64 11#64 2#64 rfl) (IdentityBitVecFacts.add_add_eq_add ret 9#64 15#64 6#64 rfl) v7 v9 v13 rest

private theorem exists_remoteKeyChunks_of_length_32_placed {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
      (v15 v23 : BitVec 64) (v31 : BitVec 8),
      ∀ a : BitVec 64, (a ↦ₛ bs) = remoteKeyChunks a b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 := by
  refine ⟨bs.getD 0 0#8, bs.getD 1 0#8, bs.getD 2 0#8, bs.getD 3 0#8, bs.getD 4 0#8, bs.getD 5 0#8, bs.getD 6 0#8,
    pack16 (bs.getD 7 0#8) (bs.getD 8 0#8), pack32 (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8) (bs.getD 12 0#8),
    pack16 (bs.getD 13 0#8) (bs.getD 14 0#8),
    pack64 (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8) (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8),
    pack64 (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8) (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8),
    bs.getD 31 0#8, fun a => ?_⟩
  nth_rw 1 [← BitVec.add_zero a]; change ((a + BitVec.ofNat 64 0) ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split_placed a bs 0 4 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split_placed _ bs 4 1 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split_placed _ bs 5 1 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split_placed _ bs 6 1 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split_placed _ bs 7 2 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split_placed _ bs 9 4 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split_placed _ bs 13 2 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split_placed _ bs 15 8 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split_placed _ bs 23 8 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_drop_split_placed _ bs 31 1 (IdentityBitVecFacts.le_of_eq32 h (by decide))]
  have hdrop32 : bs.drop 32 = [] := by simp [h]
  rw [hdrop32, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take4_eq_pointsTo32 _ bs 0 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 4 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 5 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 6 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 7 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take4_eq_pointsTo32 _ bs 9 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 13 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 15 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 23 (IdentityBitVecFacts.le_of_eq32 h (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 31 (IdentityBitVecFacts.le_of_eq32 h (by decide))]
  simp only [remoteKeyChunks, pack32, BitVec.add_zero]

private theorem memRegion_34_remoteKeyChunks_placed (ret : BitVec 64) :
    memRegion ret 34 =
      (∃∗ h0 : BitVec 16, ret ↦₁₆ h0) ∗ (∃∗ r2 : BitVec 32, (ret + 2#64) ↦₃₂ r2) ∗
      (∃∗ r6 : BitVec 8, (ret + 6#64) ↦₈ r6) ∗ (∃∗ r7 : BitVec 8, (ret + 7#64) ↦₈ r7) ∗
      (∃∗ r8 : BitVec 8, (ret + 8#64) ↦₈ r8) ∗ (∃∗ r9 : BitVec 64, (ret + 9#64) ↦₆₄ r9) ∗
      (∃∗ r17 : BitVec 64, (ret + 17#64) ↦₆₄ r17) ∗ (∃∗ r25 : BitVec 64, (ret + 25#64) ↦₆₄ r25) ∗
      (∃∗ r33 : BitVec 8, (ret + 33#64) ↦₈ r33) := by
  sep_interval_eq

private theorem stackAt_remoteIdentityKey_some_split_placed (sp : BitVec 64) :
    stackAt sp remoteIdentityKeyStack =
      memRegion (sp - 144#64) 8 ∗ (∃∗ s8 : BitVec 8, (sp - 136#64) ↦₈ s8) ∗
      (∃∗ s9 : BitVec 8, (sp - 135#64) ↦₈ s9) ∗ (∃∗ s10 : BitVec 8, (sp - 134#64) ↦₈ s10) ∗
      (∃∗ s11 : BitVec 32, (sp - 133#64) ↦₃₂ s11) ∗ memRegion (sp - 129#64) 1 ∗
      (∃∗ s16 : BitVec 64, (sp - 128#64) ↦₆₄ s16) ∗ (∃∗ s24 : BitVec 8, (sp - 120#64) ↦₈ s24) ∗
      memRegion (sp - 119#64) 7 ∗ (∃∗ s32 : BitVec 64, (sp - 112#64) ↦₆₄ s32) ∗
      (∃∗ s40 : BitVec 8, (sp - 104#64) ↦₈ s40) ∗ memRegion (sp - 103#64) 7 ∗
      (∃∗ s48 : BitVec 32, (sp - 96#64) ↦₃₂ s48) ∗ (∃∗ s52 : BitVec 8, (sp - 92#64) ↦₈ s52) ∗
      (∃∗ s53 : BitVec 8, (sp - 91#64) ↦₈ s53) ∗ (∃∗ s54 : BitVec 8, (sp - 90#64) ↦₈ s54) ∗
      (∃∗ s55 : BitVec 16, (sp - 89#64) ↦₁₆ s55) ∗ (∃∗ s57 : BitVec 32, (sp - 87#64) ↦₃₂ s57) ∗
      (∃∗ s61 : BitVec 16, (sp - 83#64) ↦₁₆ s61) ∗ memRegion (sp - 81#64) 1 ∗
      memRegion (sp - 80#64) 33 ∗ memRegion (sp - 47#64) 15 ∗ cells (sp - 32#64) 3 ∗
      (∃∗ w : BitVec 32, (sp - 8#64) ↦₃₂ w) ∗ (∃∗ h : BitVec 16, (sp - 4#64) ↦₁₆ h) ∗
      memRegion (sp - 2#64) 2 := by
  simp only [stackAt, remoteIdentityKeyStack]; sep_interval_eq

private theorem memRegion_sp_80_33_remoteKeyChunks_placed (sp : BitVec 64) :
    memRegion (sp - 80#64) 33 =
      (∃∗ k_tag : BitVec 8, (sp - 80#64) ↦₈ k_tag) ∗ (∃∗ k0 : BitVec 8, (sp - 79#64) ↦₈ k0) ∗
      (∃∗ k1 : BitVec 8, (sp - 78#64) ↦₈ k1) ∗ (∃∗ k2 : BitVec 8, (sp - 77#64) ↦₈ k2) ∗
      (∃∗ k3 : BitVec 32, (sp - 76#64) ↦₃₂ k3) ∗ (∃∗ k7 : BitVec 16, (sp - 72#64) ↦₁₆ k7) ∗
      (∃∗ k9 : BitVec 32, (sp - 70#64) ↦₃₂ k9) ∗ (∃∗ k13 : BitVec 16, (sp - 66#64) ↦₁₆ k13) ∗
      (∃∗ k15 : BitVec 64, (sp - 64#64) ↦₆₄ k15) ∗ (∃∗ k23 : BitVec 64, (sp - 56#64) ↦₆₄ k23) ∗
      (∃∗ k31 : BitVec 8, (sp - 48#64) ↦₈ k31) := by
  sep_interval_eq

set_option maxHeartbeats 1600000 in
/-- Block `29` (`<libsignal_protocol::state::session::SessionState>::remote_identity_key`)
meets `remoteIdentityKeyPlacedSpec A` under `[LibsignalPlacement]`. -/
theorem remote_identity_key_placed_ok [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_29).rebase (blkPl_29).base H) (blkPl_29).base
      (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)) := by
  simp only [withLsCodeLoaded, remoteIdentityKeyPlacedSpec]
  have htry0 : subroutine_ok ((blkPC_211).rebase (blkPl_211).base H) (lsmpl.base 211)
      deserializeMemPlacedSpec := pkTryFromMem_placed_ok H
  have htry := ls_subroutine_ok_of_block (callerProg := (blkPC_29).rebase (blkPl_29).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain htry0)
  simp only [withLsCodeLoaded, deserializeMemPlacedSpec] at htry
  wp_init x s0; obtain ⟨ss, g, rem, ret⟩ := x; dsimp only at *; subst h_2 h_3
  cases rem with
  | none =>
    dsimp only at h_1
    rw [vecGhostAt_ss_24_of_nil_placed A g (s0.readReg64 (Reg.gpr 0#5)) h_1,
        memRegion_34_none_split_placed (s0.readReg64 (Reg.gpr 8#5)),
        remoteIdentityOkAt, stackAt_remoteIdentityKey_none_split_placed s0.sp]
    cells_unfold; wp_pull_exists; wp_steps
    rw [pointsTo16_zero_placed (s0.readReg64 (Reg.gpr 8#5))]; wp_done
  | some ik =>
    dsimp only at h_1
    have hge33 := deserialize_length_ge_33 h_1
    have hpos : 0 < g.bytes.length := by omega
    have hbs32 : ik.publicKey.bytes.toList.length = 32 := by simp
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, v7, v9, v13, v15, v23, v31, hchunks⟩ :=
      exists_remoteKeyChunks_of_length_32_placed hbs32
    rw [vecGhostAt_ss_24_of_pos_placed A g (s0.readReg64 (Reg.gpr 0#5)) hpos,
        memRegion_34_remoteKeyChunks_placed (s0.readReg64 (Reg.gpr 8#5)),
        remoteIdentityOkAt, hchunks (s0.readReg64 (Reg.gpr 8#5) + 2#64),
        remoteKeyChunks_ret_2_placed (s0.readReg64 (Reg.gpr 8#5)),
        stackAt_remoteIdentityKey_some_split_placed s0.sp]
    cells_unfold; wp_pull_exists; refine SepWP.pure_elim ?_
    rintro ⟨hlen_cap, hcap_lt, hptr_ne⟩
    have hlen_lt : g.bytes.length < 2 ^ 63 := by omega
    have hlen_toNat : (BitVec.ofNat 64 g.bytes.length).toNat = g.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hlen_ne : (BitVec.ofNat 64 g.bytes.length == 0#64) = false := by
      rw [beq_eq_false_iff_ne]; intro h0
      have h0' := congrArg BitVec.toNat h0; rw [hlen_toNat] at h0'
      change g.bytes.length = 0 at h0'; omega
    apply sepWP_seq_lscl h (mid := lsmpl.base 211); wp_steps
    apply SepWP.done (by wp_norm_lhs) (by wp_norm_lhs); intro hcl_call
    wp_apply
    rw [hchunks (s0.sp - 79#64), remoteKeyChunks_sp_79_placed s0.sp]; wp_steps
    rw [sevenLo_sp_79_placed s0.sp]; wp_steps
    rw [sevenLo_sp_96_placed s0.sp]; wp_steps
    rw [← sevenLo_sp_96_placed s0.sp]; wp_steps
    rw [sevenLo_sp_96_placed s0.sp]; wp_steps
    rw [← sevenLo_sp_136_placed s0.sp]; wp_steps
    rw [sevenLo_sp_136_placed s0.sp]; wp_steps
    try rw [truncate16_zeroExtend32_placed]
    try rw [truncate16_zeroExtend32_placed]
    rw [pointsTo16_32_16_sp_89_placed s0.sp, sevenLo_ret_2_placed (s0.readReg64 (Reg.gpr 8#5))]; wp_steps
    try rw [pointsTo16_256_placed (s0.readReg64 (Reg.gpr 8#5))]
    try rw [← sevenLo_ret_2_placed (s0.readReg64 (Reg.gpr 8#5))]
    try rw [← pointsTo16_32_16_ret_9_placed (s0.readReg64 (Reg.gpr 8#5))]
    try rw [← sevenLo_sp_96_placed s0.sp]
    try rw [← pointsTo16_32_16_sp_89_placed s0.sp]
    try rw [memRegion_sp_80_33_remoteKeyChunks_placed s0.sp]
    wp_done

/-! ### Block `35`: `SessionState::clear_unacknowledged_pre_key_message` -/

abbrev lsRustDeallocSym : String := "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc"

private theorem ls_hook_ok_of_mem_placed [LibsignalPlacement] {α : Type} {prog : Program} {i : Nat}
    {H : LibsignalHooks} [hprog : IsLsBlockProg prog i H] {sym : String} {spec : Spec α}
    (hsat : HookSat H sym spec) (hmem : sym ∈ libsignalHookedExterns := by decide)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ sym) spec := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem (mem_libsignalSessionExterns_of_hooked hmem)
  exact ls_hook_ok (k := k) (by simp [hk, hget]) hsat hi hunmut (hhooked := hmem)

private theorem slt_one_iff_eq_zero_placed {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap.slt 1#64 = true) ↔ cap = 0 := by
  have h1 : (cap = 0) ↔ cap.toNat = 0 := ⟨by rintro rfl; rfl, fun h0 => BitVec.eq_of_toNat_eq h0⟩
  have h2 : (1#64 : BitVec 64).toNat = 1 := rfl
  have h3 : 2 * cap.toNat < 2 ^ 64 := by omega
  rw [h1]; unfold BitVec.slt BitVec.toInt; simp only [decide_eq_true_iff, h2, h3, ↓reduceIte]; omega

private theorem optTailVecAt_entails_deallocX_placed (A : RustAlloc) (size : Nat)
    (hsz24 : 24 ≤ size) (hsz64 : size ≤ 64) (a : BitVec 64) (opt : Option TailVecGhost) :
    optTailVecAt A size a opt ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) (size - 16) ∗
        (if cap.slt 1#64 = true then emp
         else ⌜0 < cap.toNat ∧ cap.toNat < 2 ^ 63⌝ ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  cases opt with
  | none =>
    unfold optTailVecAt
    have hsplit : size - 8 = 8 + (size - 16) := by omega
    rw [hsplit, ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := size - 16)
          (b' := a + 16#64) rfl (by bv_omega) (by omega),
        memRegion_eight (a + 8#64), sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro ptr
    refine Entails.sepExists_right noneCap (Entails.sepExists_right ptr ?_)
    have hslt : noneCap.slt 1#64 = true := by decide
    simp only [hslt, ↓reduceIte, sepConj_emp]; exact Entails.refl _
  | some g =>
    unfold optTailVecAt; apply Entails.pure_left; intro htail
    have hvec : vecGhostAt A g.vec a ⊢
        (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else ⌜0 < g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63⌝ ∗ A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat) := by
      unfold vecGhostAt
      refine Entails.trans (vecU8At_entails_dealloc A a g.vec.cap g.vec.ptr g.vec.bytes) ?_
      rw [sepConj_pure_left_comm]; apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader; simp only [slt_one_iff_eq_zero_placed hcap_lt, sepConj_assoc]
      refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
      by_cases h0 : g.vec.cap = 0
      · simp only [h0, ↓reduceIte]; exact Entails.refl _
      · simp only [h0, ↓reduceIte]
        exact Entails.pure_right ⟨Nat.pos_of_ne_zero (fun h => h0 (BitVec.eq_of_toNat_eq h)), hcap_lt⟩ (Entails.refl _)
    refine Entails.trans (sepConj_mono_left hvec) ?_
    refine Entails.sepExists_right g.vec.cap (Entails.sepExists_right g.vec.ptr ?_)
    have h16 : (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ⊢
        memRegion (a + 16#64) (size - 16) := by
      have hsplit : size - 16 = 8 + (size - 24) := by omega
      rw [hsplit, ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := size - 24)
            (b' := a + 24#64) rfl (by bv_omega) (by omega)]
      apply sepConj_mono (pointsTo64_entails_memRegion _ _)
      have hb := pointsToBytes_entails_memRegion (a + 24#64) g.tail; rwa [htail] at hb
    have hpull1 :
        (((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else ⌜0 < g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63⌝ ∗ A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat)) ∗
          ((a + 24#64) ↦ₛ g.tail)) =
        ((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ∗
          (if g.vec.cap.slt 1#64 = true then emp
           else ⌜0 < g.vec.cap.toNat ∧ g.vec.cap.toNat < 2 ^ 63⌝ ∗ A.live g.vec.ptr g.vec.cap.toNat 1 ∗ memRegion g.vec.ptr g.vec.cap.toNat)) := by ac_rfl
    rw [hpull1]; exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16))

private theorem stackAt_clearUpk_opt_placed {hookStack : Nat} (hstack : hookStack + 32 ≤ 2 ^ 64) (sp : BitVec 64) :
    stackAt sp (32 + hookStack) = stackAt (sp - 32#64) hookStack ∗ cells (sp - 32#64) 4 := by
  rw [Nat.add_comm 32 hookStack]; exact stackAt_split_cells sp hookStack 4 hstack

@[local wp_norm] private theorem exists_two_pow_one_placed : (∃ k : Nat, 1 = 2 ^ k) ↔ True :=
  iff_true_intro ⟨0, rfl⟩

set_option maxHeartbeats 1600000 in
set_option linter.unusedSimpArgs false in
/-- Stack-parameterized relocatable verification of
`SessionState::clear_unacknowledged_pre_key_message` (Block `35`). -/
theorem clear_unacknowledged_pre_key_message_placed_ok_of_dealloc [LibsignalPlacement]
    (A : RustAlloc) (H : String → Option (State → State)) (hookStack : Nat)
    (hstack : hookStack + 32 ≤ 2 ^ 64 := by decide)
    (hdealloc : subroutine_ok ((blkPC_35).rebase (blkPl_35).base H)
      (lsρ lsRustDeallocSym) (rustDeallocExternSpecWithStack A hookStack)) :
    subroutine_ok ((blkPC_35).rebase (blkPl_35).base H) (blkPl_35).base
      (clearUpkSpecWithStack A hookStack) := by
  unfold clearUpkSpecWithStack; wp_init x s0; obtain ⟨ss, G, st⟩ := x; dsimp only at *; subst h
  rw [sessionStateAt_split_upk, stackAt_clearUpk_opt_placed (by omega) s0.sp]
  cells_unfold; wp_pull_exists; refine SepWP.pure_elim ?_
  rintro ⟨hloc, hrem, hchains, hpending, hreg, hlik_len, hrik_len⟩
  refine SepWP.weaken_pre (sepConj_mono
    (optTailVecAt_entails_deallocX_placed A 48 (by decide) (by decide) (s0.readReg64 (Reg.gpr 0#5) + 0xf8#64) G.pending)
    (sepConj_mono_left (optTailVecAt_entails_deallocX_placed A 32 (by decide) (by decide) (s0.readReg64 (Reg.gpr 0#5) + 0x128#64) G.kyber))) ?_
  wp_pull_exists; rename_i cap2 ptr2 cap1 ptr1
  refine clearUpk_strengthen_post (sessionStateAt_cleared_upk_intro A (s0.readReg64 (Reg.gpr 0#5)) ptr1 ptr2 G st
    hloc hrem hchains hreg hlik_len hrik_len) ?_
  wp_steps
  by_cases h1 : cap1.slt 1#64 = true <;> simp only [h1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps
    by_cases h2 : cap2.slt 1#64 = true <;> simp only [h2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hpos2, hlt2⟩
      have hlay2 : LayoutOk cap2.toNat 1 := ⟨hpos2, ⟨0, rfl⟩, by omega⟩
      wp_steps; wp_call hdealloc (ptr2, cap2.toNat, 1); wp_steps; wp_done
  · refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hpos1, hlt1⟩
    have hlay1 : LayoutOk cap1.toNat 1 := ⟨hpos1, ⟨0, rfl⟩, by omega⟩
    wp_steps; wp_call hdealloc (ptr1, cap1.toNat, 1); wp_steps
    by_cases h2 : cap2.slt 1#64 = true <;> simp only [h2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
    · wp_steps; wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_; rintro ⟨hpos2, hlt2⟩
      have hlay2 : LayoutOk cap2.toNat 1 := ⟨hpos2, ⟨0, rfl⟩, by omega⟩
      wp_steps; wp_call hdealloc (ptr2, cap2.toNat, 1); rw [hsp_sf]; wp_steps; wp_done

/-- Block `35` (`<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message`)
meets `clearUpkSpec A` under `[LibsignalPlacement]`. -/
theorem clear_unacknowledged_pre_key_message_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_35).rebase (blkPl_35).base H) (blkPl_35).base
      (clearUpkSpec A) :=
  clear_unacknowledged_pre_key_message_placed_ok_of_dealloc A H allocHookStack (by decide)
    (rustDeallocExternWithStack_of_rustDealloc (ls_hook_ok_of_mem_placed hdealloc) (by decide) (by decide))

/-- Block `35` (`<libsignal_protocol::state::session::SessionState>::clear_unacknowledged_pre_key_message`)
meets `clearUpkSpecX A` under `[LibsignalPlacement]`. -/
theorem clear_unacknowledged_pre_key_message_placed_ok_x [LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_35).rebase (blkPl_35).base H) (blkPl_35).base
      (clearUpkSpecX A) :=
  clear_unacknowledged_pre_key_message_placed_ok_of_dealloc A H extHookStack (by decide)
    (rustDeallocExternWithStack_of_rustDealloc (ls_hook_ok_of_mem_placed hdealloc) (by decide) (by decide))

/-! ### Block `130` Segment S0 (`+0x000..+0x1d8`): `identityKeys_placed_ok` -/

theorem identityKeys_step5_some_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (x : TryDecryptGhost) (remIk : IdentityKey) (F : SepProp) (s0 s4 : State)
    (hcl : LibsignalCodeLoaded lsmpl s4.mem)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s4.pc = (blkPl_131).base + 384#64) (h_run : s4.status = .Running)
    (h_sp : s4.sp = s0.sp - 1504#64) (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx8 : s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s4.readReg64 .x10 = BitVec.zeroExtend 64 b22) (hx11 : s4.readReg64 .x11 = 1#64)
    (hx19 : s4.readReg64 .x19 = x.ret) (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s4.readReg64 .x21 = x.ss) (hx22 : s4.readReg64 .x22 = x.msgA)
    (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA) (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hrem_eq : ∀ a : BitVec 64, (a ↦ₛ remIk.publicKey.bytes.toList) =
      remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk)
    (hm : s4.mem ⊨ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗ memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      ((s0.sp - 1504#64 + 352#64) ↦₆₄ w3) ∗ ((s0.sp - 1504#64 + 360#64) ↦₈ b31) ∗
      ((s0.sp - 1504#64 + 976#64) ↦₃₂ w0) ∗ ((s0.sp - 1504#64 + 980#64) ↦₈ b4) ∗
      ((s0.sp - 1504#64 + 981#64) ↦₈ b5) ∗ memRegion ((s0.sp - 1504#64) + 56#64) 296 ∗
      memRegion ((s0.sp - 1504#64) + 361#64) 39 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 542 ∗
      memRegion ((s0.sp - 1504#64) + 982#64) 298 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s4
      (fun s5 => s5.sp = sp ∧ s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 1352 ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rw [stackAt_tryDecryptSubStack_sub s0.sp isSameAccountStack (by decide)] at hm
  obtain ⟨u400, u408, dw0, db4, db5, db6, db7, db8, db9, db10, db11, db12, db13, db14, db15, db16, db17, db18, db19, db20, db21, db22, dw3, db31, hm_ext⟩ :=
    identityKeys_step5_some_extract (sp := s0.sp - 1504#64) (Satisfies.mono (by bi_frame) hm)
  rw [← h_sp] at hm_ext
  have hx20' : s4.readReg64 .x20 = s4.sp + 320#64 := by rw [h_sp]; exact hx20
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by rw [hx29, h_sp]; bv_omega
  have hsame := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H)
    (is_same_account_placed_ok h_bb)
  have hwp := identityKeys_remote_some_wp_placed hsame x remIk s4 hcl w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
    w3 b31 u400 u408 dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19 db20 db21 db22 dw3 db31
    h_pc h_run h_sp_align hx8 hx9 hx10 hx11 hx20' hx25 hx29' hrem_eq hdiff
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp (Satisfies.mono (by bi_frame) hm_ext)) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨by reg_chain, halign5, by reg_chain, hx1_5, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, hx25_5, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s5; rw [h_sp] at hm2
  have hm3 := Satisfies.mono
    (sepConj_mono_left (identityKeys_step5_some_recombine (s0.sp - 1504#64) x.st.localIdentity remIk w0 b4 b5 b6
      (pack64 b7 b8 b9 b10 b11 b12 b13 b14) w3 b31))
    (Satisfies.mono (by bi_frame) hm2)
  rw [stackAt_tryDecryptSubStack_sub s0.sp isSameAccountStack (by decide)]
  exact Satisfies.mono (by bi_entail) hm3

theorem identityKeys_step45_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State) (hcl : LibsignalCodeLoaded lsmpl s3.mem)
    (h_pc : s3.pc = (blkPl_131).base + 160#64) (h_run : s3.status = .Running)
    (h_sp : s3.sp = s0.sp - 1504#64) (h_sp_align : s3.spAligned = true)
    (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hx19 : s3.readReg64 .x19 = x.ret) (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s3.readReg64 .x21 = x.ss) (hx22 : s3.readReg64 .x22 = x.msgA)
    (hx23 : s3.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s3.readReg64 .x25 = x.locA) (hx29 : s3.readReg64 .x29 = s0.sp - 96#64)
    (hnot_self : x.st.remoteIdentity ≠ some x.st.localIdentity)
    (hm : s3.mem ⊨ remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff tryDecryptDummyImg ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 472#64) s3
      (fun s5 => s5.sp = sp ∧ s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 1352 ∗
          logOff tryDecryptDummyImg ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rcases hrem_opt : x.st.remoteIdentity with _ | remIk
  · rw [hrem_opt] at hm; dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega, show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, w3, b31, hent_402, hm_402⟩ :=
      exists_remoteGroupC_of_memRegion_32 (a := (s0.sp - 1504#64) + 402#64)
        (Satisfies.mono (by dsimp only [sp] at hm; bi_frame) hm)
    refine reaches_pc_seq
      (identityKeys_step4_reaches_placed (H := H) x _ s0 s3 0#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 (hent_402 (sp + 402#64))
        (by rw [← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]
            exact Satisfies.mono (by bi_frame) hm_402)) ?_
    intro s4 hpc4 hrun4 ⟨hsp4, halign4, htr4, _, _, _, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩
    have hm4_1352 := Satisfies.mono
      (sepConj_mono_left (identityKeys_step4_to_memRegion_1352 (s0.sp - 1504#64) x.st.localIdentity w0 b4 b5 w3 b31))
      (Satisfies.mono (by bi_frame) hm4)
    refine reaches_pc_mono
      (identityKeys_step5_none_reaches_placed (H := H) x (((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗ F)
        s0 s4 hpc4 hrun4 hsp4 halign4 htr4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx29_4
        (Satisfies.mono (by dsimp only [sp]; bi_entail) hm4_1352)) ?_
    intro s5 _ _ ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩
    refine ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, ?_⟩
    exact Satisfies.mono (by dsimp only [sp]; bi_entail) hm5
  · rw [hrem_opt] at hm; dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega, show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, w3, b31, hrem_c⟩ :=
      exists_remoteGroupC_of_length_32 (List.Vector.toList_length remIk.publicKey.bytes)
    have hent_402 : remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ⊢
        memRegion (sp + 402#64) 32 := by
      rw [← hrem_c (sp + 402#64)]
      have hlen : remIk.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
      sep_interval
    rw [hrem_c (sp + 402#64)] at hm
    refine reaches_pc_seq_lscl hcl
      (identityKeys_step4_reaches_placed (H := H) x _ s0 s3 1#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 hent_402
        (by rw [← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]
            exact Satisfies.mono (by dsimp only [sp] at hm; bi_frame) hm)) ?_
    intro s4 hpc4 hrun4 ⟨hsp4, halign4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩ hcl4
    have hrem_d : ∀ a : BitVec 64, (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 :=
      fun a => (hrem_c a).trans (remoteGroupC_eq_remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    have hdiff : x.st.localIdentity ≠ remIk := by intro heq; apply hnot_self; rw [hrem_opt, heq]
    refine reaches_pc_mono
      (identityKeys_step5_some_reaches_placed h_bb x remIk (logOff tryDecryptDummyImg ∗ F) s0 s4 hcl4
        w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31
        hpc4 hrun4 hsp4 halign4 htr4 hx8_4 hx9_4 hx10_4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx29_4
        hrem_d hdiff (Satisfies.mono (by bi_entail) hm4)) ?_
    intro s5 _ _ ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩
    refine ⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, ?_⟩
    exact Satisfies.mono (by bi_entail) hm5

/-- Block `130` Segment S0 (`+0x000..+0x1d8`) under `[LibsignalPlacement]`: reaches
`segLoadRatchetPC_placed` with `LoadRatchetState_placed`. -/
theorem identityKeys_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)} (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (x : TryDecryptGhost) (R : SepProp) (s0 : State)
    (h_pc : s0.pc = tryDecryptEntry_placed) (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hpre : s0.mem ⊨ (tryDecryptPlacedSpec C A ctl uuidTryParse S).pre x s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segLoadRatchetPC_placed s0
      (LoadRatchetState_placed A ctl x R s0) := by
  dsimp only [tryDecryptPlacedSpec, withLsCodeLoaded, tryDecryptRawSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hnot_self, _, _, _⟩, hm0⟩
  rw [sepConj_assoc] at hm0
  have ⟨hdeser_loc, hdeser_rem⟩ := sessionStateAt_ik_facts hm0
  rw [sessionStateAt_eq_ik_rest A x.ss x.G x.st, sepConj_assoc, sepConj_assoc] at hm0
  generalize hrik : vecGhostAt A x.G.remoteIk (x.ss + 24#64) = rikH,
    hss : sessionStateRestAt A x.ss x.G x.st = ssRestH,
    htape : tapeAt ctl x.cur x.rest = tapeH,
    hrem_a : protocolAddressAt A x.rem x.remA = remH,
    hloc_a : protocolAddressAt A x.loc x.locA = locH,
    hmsg_a : signalMessageAt A x.msgG x.msgA x.msg = msgH at hm0
  refine reaches_pc_seq_lscl hcl0
    (identityKeys_step1_reaches_placed (A := A) (H := H) x _ s0 hcl0 h_pc h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc
      (by rw [← sepConj_assoc, ← sepConj_assoc]; refine Satisfies.mono ?_ hm0; bi_frame)) ?_
  intro s1 hpc1 hrun1 ⟨hsp1, halign1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx29_1, hm1⟩ hcl1
  generalize hlik : vecGhostAt A x.G.localIk x.ss = likH at hm1
  refine reaches_pc_seq_lscl hcl1
    (identityKeys_step2_reaches_placed (H := H) x _ s0 s1 hpc1 hrun1 hsp1 halign1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1
      (by rw [← sepConj_assoc, ← sepConj_assoc]; refine Satisfies.mono ?_ hm1; bi_frame)) ?_
  intro s2 hpc2 hrun2 ⟨hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx29_2, hm2⟩ hcl2
  rw [← hrik] at hm2
  have hrem := ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H)
    (remote_identity_key_placed_ok A H)
  refine reaches_pc_seq_lscl hcl2
    (identityKeys_step3_reaches_placed hrem x _ s0 s2 hcl2 hpc2 hrun2 hsp2 halign2 htr2 hx0_2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx29_2 hdeser_rem
      (by rw [← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]; refine Satisfies.mono ?_ hm2; bi_frame)) ?_
  intro s3 hpc3 hrun3 ⟨hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx29_3, hm3⟩ hcl3
  rw [hrik] at hm3
  refine reaches_pc_mono
    (reaches_pc_lscl hcl3
      (identityKeys_step45_reaches_placed h_bb x _ s0 s3 hcl3 hpc3 hrun3 hsp3 halign3 htr3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx29_3 hnot_self
        (by rw [← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc, ← sepConj_assoc]
            refine Satisfies.mono ?_ hm3; bi_frame))) ?_
  intro s5 hpc5 hrun5 ⟨⟨hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩, hcl5⟩
  refine ⟨hpc5, ⟨hrun5, hsp5, h_sp_align, halign5, hx29_5, htr5.1, hcl5, htr5.2⟩,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx1_5, ?_⟩
  rw [← htape] at hm5
  unfold tryDecryptCommonHeap
  rw [sessionStateAt_eq_ik_rest A x.ss x.G x.st, hlik, hrik, hss, hrem_a, hloc_a, hmsg_a]
  refine Satisfies.mono ?_ hm5
  refine Entails.trans (by bi_frame)
    (Entails.trans (sepConj_mono_left (tapeAfter_zero ctl x.cur x.rest)) ?_)
  generalize tapeAfter ctl x.cur x.rest 0 = tapeH0
  bi_entail

/-- Block `130` Segment S0 (`+0x000..+0x1d8`) under `[LibsignalPlacement]` (`tryDecryptFnPlacedSpec` variant). -/
theorem identityKeys_placed_ok_x [LibsignalPlacement] {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (x : TryDecryptGhost) (R : SepProp) (s0 : State)
    (h_pc : s0.pc = tryDecryptEntry_placed) (h_run : s0.status = .Running)
    (h_sp_align : s0.spAligned = true)
    (hpre : s0.mem ⊨ (tryDecryptFnPlacedSpec C decFn A ctl uuidTryParse S).pre x s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segLoadRatchetPC_placed s0
      (LoadRatchetState_placed A ctl x R s0) :=
  @identityKeys_placed_ok _ C A ctl S H h_bb x R s0 h_pc h_run h_sp_align hpre

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
