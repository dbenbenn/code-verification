/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import Lean
public import Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.DefsI0
public import Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.I0Laws
public import Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
public import Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire
public import Symbolic.BugInjection.Proofs.Common443.CompRGamma
public import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.PtCoins
import Symbolic.Proofs.Swarm.CREF.BobRecBaseKeyMono
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.TR.RecvHistStepTR2
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTie
import Symbolic.Proofs.Swarm.UA.BI.Step
import Symbolic.Proofs.Swarm.UA.XlateSteps
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState

/-!
# Send-Path Prefix Refutation for `PqxdhKemSsOmittedCli` (`NoPrefixExplains.lean`)

Proves `not_explains_prefix2`: for every `S : OpaqueSymbolSemantics`, `g : Ghost`, `ss`, `vis`,
and suffix `tail`, `[.run ev0, .run ev1] ++ tail` has no `Explains` witness under `pqxdhI0`:
1. At Call 0 (`ev0`, `alice init`), `s₀` must be `Step.aliceStart "alice" ...`. Its `aliceVis`
   exposes `.kyberCoin 0` for `entropy = randTerm (tr₀.length + 1) 32`, so `GhostWF` forces
   `(γ entropy).length = 32`, hence `(γ ss).length = 32` (`concretizeKemSS` on `pqxdhI0`) and
   `(γ ikm).length ∈ {160, 192}`.
2. In `pqxdhSha256Rows`, no recorded 64-byte block ends in big-endian bit length `1792`
   (`8 * (64 + 160)`) or `2048` (`8 * (64 + 192)`), so `prk = hmac zeroSalt ikm` is tagged with
   `compTag4`, propagating to `o.keys.rk` and `stA.cks`.
3. Invisible `.network` steps before Call 1 (`ev1`, `alice send`) preserve `AliceInv`, so the
   `messageEncrypt "alice"` step at `ev1` produces an inner MAC whose first 4 bytes equal
   `compTag4` (for **all** `S` and **all** `pqSalt`), contradicting Call 1's recorded stdout.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.NoPrefixExplains

open scoped DY.Libsignal.Composed
open ByteSpecs (ShaState sha256IV sha256Pad chunks64 sha256With hmacWith toBEBytes)
open DY (Participant Traceful ExecTrace ExecTraceTypes)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent CliEvent)
open DY.Libsignal.Refinement (sha256CompressFunction shaStateBytes shaStateOfBytes)
open DY.Libsignal.PQXDH
  (BundleHandles AliceHandshakeOut discontinuity agree pqxdhIkm pqxdhKdf pqxdhLabel
   aliceAgreement aliceHandshake)
open DY.Libsignal.TripleRatchet
  (TRState TREvent zeroSalt hmac hkdfBlock1 hkdfBlock2 kdfRk createChain kdfCk trMsgKeys computeMac
   trHonestWireMsg messageEncrypt logMessageKeyAndStore u32Max)
open DY.Libsignal.Composed (ComposedEvent reachability)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost Step VisEntry BundlePreKeyIds
   gamma gamma' leBytes randTerm newRandoms kyberCoinEntries aliceVis encDraws encSendEntry
   pqExposureAt trExposureAt exposures lastSent pendingPreKey stepView
   setupTrace runSteps StepsWF RunMatches RunRejected OutputsMatch BytesMatchEntry SendMatches
   GhostWF nextBundleIds MatchesEventsAt Explains runWrapped parsePreKeyWire PreKeyFields)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (bytesToNat compTag4 compTag4Opad compDefaultSha256)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
  (compLookupDh_length compKyberEncaps_length)
open Symbolic.BugInjection.Proofs.Common443.CompRTag
  (toBEBytes_length sha256With_length sha256Pad_append64 chunks64_append64
   chunks64_padTail64_32 padTail64 padTail64_take4
   sha256With_take4_of_offTable hmacWith_take4_of_inner)
open Symbolic.BugInjection.Proofs.Common443.CompRNbscTable
  (compDefaultSha256_take4 leBytes_bytesToNat tagW toBEBytes_tagW shaStateOfBytes_compTag4_head
   shaStateBytes_take4_of_head kblk kblk_length)
open Symbolic.BugInjection.Proofs.Common443.CompRPreKeyWire (parsePreKeyWire_preKeyWire_inv)
open Symbolic.BugInjection.Proofs.Common443.CompRGamma (gamma_agree)
open Symbolic.Swarm.COMPOSED.CompTrace
  (TRStEntry RndE NetE TREvE TRStE PQEvE CEvE run_bind_fst run_bind_snd receiveMessage_snd)
open Symbolic.Swarm.CREF
  (bks_stored_of_getLocalState bks_lt_length_of_at?
   rpkT_receiveMessage_fst rpkT_getMessageSentAt_of_at?)
open Symbolic.Swarm.CREF.TR (Runs)
open Symbolic.Swarm.CREF.TR.RecvHistStep2 (traceStatesP_setupTrace traceStatesP_at?_st)
open Symbolic.Swarm.CREF.TR.RecvDec
  (getLocalState_snd at?_append_non_entry at?_eq_none_of_le)
open Symbolic.Proofs.Swarm.UA.BI.Step (stepIn_ok next_network)
open Symbolic.Proofs.Swarm.UA.XlateSteps (stepIn_next)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
  (storeLocalState_tr_snd_eq logEvent_snd_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionBase (Preserves)
open Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.DefsShaRows
  (pqxdhSha256Bucket pqxdhSha256Rows pqxdhSha256)
open Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.DefsI0 (pqxdhI0)
open Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.I0Laws
  (pqxdhI0_agreement pqxdhI0_kyberEncaps pqxdhI0_sha256Compress pqxdhI0_cryptoEquationsHold)
open Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.PtCoins (aliceStart_ok_newRandoms)

/-! ## 1. SHA-256 Off-Table `compTag4` Propagation on `pqxdhSha256Rows` -/

private theorem shaStateOfBytes_head_eq_take4 (bytes : HwBytes) :
    (shaStateOfBytes bytes).head = (shaStateOfBytes (bytes.take 4)).head := by
  rcases bytes with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _⟩⟩⟩⟩ <;> rfl

abbrev FP : ShaState → HwBytes → ShaState := sha256CompressFunction pqxdhI0
def OnTabP (s : ShaState) (b : HwBytes) : Prop := (pqxdhSha256 (shaStateBytes s) b).take 4 ≠ compTag4

theorem FP_eq (s : ShaState) (b : HwBytes) :
    FP s b = shaStateOfBytes (pqxdhSha256 (shaStateBytes s) b) := by
  show sha256CompressFunction pqxdhI0 s b = _
  unfold sha256CompressFunction; rw [pqxdhI0_sha256Compress, Option.getD_some]

theorem pqxdhSha256_row_of_untagged {st blk : HwBytes}
    (h : (pqxdhSha256 st blk).take 4 ≠ compTag4) :
    st.take 4 ≠ compTag4 ∧ st.length = 32 ∧ blk.length = 64 ∧
      ∃ row ∈ pqxdhSha256Rows, row.1 = bytesToNat st ∧ row.2.1 = bytesToNat blk ∧
        pqxdhSha256 st blk = leBytes 32 row.2.2 := by
  unfold pqxdhSha256 at h ⊢
  by_cases htag : (st.take 4 == compTag4 || blk.take 4 == compTag4 ||
      blk.take 4 == Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0.compTag4Ipad ||
      blk.take 4 == compTag4Opad) = true
  · simp only [htag, ↓reduceIte] at h; exact absurd (compDefaultSha256_take4 st blk) h
  · have hst : st.take 4 ≠ compTag4 := fun he => by apply htag; simp [he]
    simp only [htag, ↓reduceIte, Bool.false_eq_true] at h ⊢
    by_cases hlen : (st.length == 32 && blk.length == 64) = true
    · simp only [hlen, ↓reduceIte] at h ⊢; simp only [Bool.and_eq_true, beq_iff_eq] at hlen
      cases hf : List.find? (fun r => r.1 == bytesToNat st && r.2.1 == bytesToNat blk)
          (pqxdhSha256Bucket (bytesToNat blk % 64)) with
      | none => simp only [hf] at h; exact absurd (compDefaultSha256_take4 st blk) h
      | some row =>
        rcases row with ⟨r1, r2, r3⟩
        have hmem_b := List.mem_of_find?_eq_some hf
        have hmem : (r1, r2, r3) ∈ pqxdhSha256Rows :=
          List.mem_flatMap.mpr ⟨bytesToNat blk % 64,
            List.mem_range.mpr (Nat.mod_lt _ (by decide)), hmem_b⟩
        have hp := List.find?_some hf; simp only [Bool.and_eq_true, beq_iff_eq] at hp
        exact ⟨hst, hlen.1, hlen.2, ⟨r1, r2, r3⟩, hmem, hp.1, hp.2, rfl⟩
    · simp only [hlen, ↓reduceIte, Bool.false_eq_true] at h
      exact absurd (compDefaultSha256_take4 st blk) h

theorem hstepP : ∀ s b, ¬ OnTabP s b → (FP s b).head = tagW := by
  intro s b h
  rw [FP_eq, shaStateOfBytes_head_eq_take4, Classical.not_not.mp h, shaStateOfBytes_compTag4_head]

theorem hT1_P : ∀ s b, s.head = tagW → ¬ OnTabP s b := by
  intro s b hs h; apply h; have hst := shaStateBytes_take4_of_head s hs
  unfold pqxdhSha256; simp only [hst, beq_self_eq_true, Bool.true_or, ↓reduceIte]
  exact compDefaultSha256_take4 _ _

theorem hT2_P : ∀ s b, b.take 4 = toBEBytes 4 tagW → ¬ OnTabP s b := by
  intro s b hb h; rw [toBEBytes_tagW] at hb; apply h
  unfold pqxdhSha256; simp only [hb, beq_self_eq_true, Bool.true_or, Bool.or_true, ↓reduceIte]
  exact compDefaultSha256_take4 _ _

theorem onTabP_of_sha256With_untagged (m : HwBytes) (h : (sha256With FP m).take 4 ≠ compTag4)
    (l₁ : List HwBytes) (b : HwBytes) (l₂ : List HwBytes)
    (hsplit : chunks64 (sha256Pad m) = l₁ ++ b :: l₂) : OnTabP (l₁.foldl FP sha256IV) b := by
  intro hoff; apply h
  rw [sha256With_take4_of_offTable OnTabP tagW FP hstepP hT1_P m l₁ b l₂ hsplit
    (fun h' => h' hoff), toBEBytes_tagW]

theorem hmacWith_eqP (k m : HwBytes) (hk : k.length ≤ 64) :
    hmacWith FP k m = sha256With FP (kblk k 0x5c ++ sha256With FP (kblk k 0x36 ++ m)) := by
  have hk' : ¬ 64 < k.length := by omega
  simp only [hmacWith, hk', ↓reduceIte, kblk]

theorem hmac_inner_untaggedP (k m : HwBytes) (hk : k.length ≤ 64)
    (h : (hmacWith FP k m).take 4 ≠ compTag4) :
    (sha256With FP (kblk k 0x36 ++ m)).take 4 ≠ compTag4 := by
  intro hin; apply h
  rw [hmacWith_take4_of_inner OnTabP tagW FP hstepP hT1_P hT2_P k m hk
    (by rw [toBEBytes_tagW]; exact hin), toBEBytes_tagW]

theorem hmac_outer_first_onTabP (k m : HwBytes) (hk : k.length ≤ 64)
    (h : (hmacWith FP k m).take 4 ≠ compTag4) : OnTabP sha256IV (kblk k 0x5c) := by
  rw [hmacWith_eqP k m hk] at h; have hx := kblk_length k 0x5c hk
  exact onTabP_of_sha256With_untagged _ h [] _
    (chunks64 (padTail64 (sha256With FP (kblk k 0x36 ++ m))))
    (by rw [sha256Pad_append64 _ _ hx, chunks64_append64 _ _ hx]; rfl)

def normKeyP (k : HwBytes) : HwBytes := if 64 < k.length then sha256With FP k else k

theorem normKeyP_length_le (k : HwBytes) : (normKeyP k).length ≤ 64 := by
  unfold normKeyP; split
  · rw [sha256With_length]; omega
  · omega

theorem hmacWith_eq_normKeyP (k m : HwBytes) : hmacWith FP k m = hmacWith FP (normKeyP k) m := by
  unfold normKeyP; split
  · rename_i h; have hle : ¬ 64 < (sha256With FP k).length := by rw [sha256With_length]; omega
    simp only [hmacWith, h, hle, ↓reduceIte]
  · rfl

def TaggedP (x : HwBytes) : Prop := x.length = 32 ∧ x.take 4 = compTag4

private theorem hmacWith_FP_length (k m : HwBytes) : (hmacWith FP k m).length = 32 := by
  unfold hmacWith; split <;> exact sha256With_length FP _

theorem hmacWith_FP_of_tagged_key {k : HwBytes} (m : HwBytes) (hk : TaggedP k) :
    TaggedP (hmacWith FP k m) := by
  have hklen : k.length = 32 := hk.1
  refine ⟨hmacWith_FP_length k m, Classical.byContradiction fun h => ?_⟩
  have htab : OnTabP sha256IV (kblk k 0x5c) := hmac_outer_first_onTabP k m (by omega) h
  have hk4 : (kblk k 0x5c).take 4 = compTag4Opad := by
    unfold kblk
    rw [← List.map_take, List.take_append_of_le_length (by omega), hk.2]
    decide
  apply htab
  unfold pqxdhSha256
  simp only [hk4, beq_self_eq_true, Bool.or_true, ↓reduceIte]
  exact compDefaultSha256_take4 _ _

theorem hmacWith_FP_of_tagged_msg (k : HwBytes) {m : HwBytes} (hm : TaggedP m) :
    TaggedP (hmacWith FP k m) := by
  refine ⟨hmacWith_FP_length k m, Classical.byContradiction fun h => ?_⟩
  rw [hmacWith_eq_normKeyP k m] at h
  set k' := normKeyP k
  have hk' : k'.length ≤ 64 := normKeyP_length_le k
  have hin : (sha256With FP (kblk k' 0x36 ++ m)).take 4 ≠ compTag4 :=
    hmac_inner_untaggedP k' m hk' h
  set x := kblk k' 0x36
  have hx : x.length = 64 := kblk_length k' 0x36 hk'
  have hsplit : chunks64 (sha256Pad (x ++ m)) = [x] ++ padTail64 m :: [] := by
    rw [sha256Pad_append64 x m hx, chunks64_append64 x _ hx, chunks64_padTail64_32 m hm.1]
    rfl
  have hon : OnTabP (FP sha256IV x) (padTail64 m) :=
    onTabP_of_sha256With_untagged _ hin [x] (padTail64 m) [] hsplit
  have hp4 : (padTail64 m).take 4 = toBEBytes 4 tagW := by
    rw [padTail64_take4 m hm.1, hm.2, toBEBytes_tagW]
  exact hT2_P (FP sha256IV x) (padTail64 m) hp4 hon

private theorem chunks64_64 {b : HwBytes} (hb : b.length = 64) : chunks64 b = [b] := by
  apply List.ext_getElem
  · simp [chunks64, hb]
  · intro i _ hi
    have h0 : i = 0 := by simp at hi; omega
    subst h0; simp [chunks64, List.take_of_length_le, hb]

private theorem chunks64_append_last :
    ∀ (k : Nat) {a b : HwBytes}, a.length = 64 * k → b.length = 64 →
      chunks64 (a ++ b) = chunks64 a ++ b :: []
  | 0, a, b, ha, hb => by
    have : a = [] := List.eq_nil_of_length_eq_zero ha
    subst this
    have hc0 : chunks64 [] = [] := by simp [chunks64]
    rw [List.nil_append, hc0, List.nil_append, chunks64_64 hb]
  | k + 1, a, b, ha, hb => by
    have ht : (a.take 64).length = 64 := by rw [List.length_take]; omega
    have hd : (a.drop 64).length = 64 * k := by rw [List.length_drop]; omega
    conv_lhs => rw [← List.take_append_drop 64 a, List.append_assoc]
    conv_rhs => rw [← List.take_append_drop 64 a]
    rw [chunks64_append64 _ _ ht, chunks64_append64 _ _ ht, List.cons_append,
        chunks64_append_last k hd hb]

private theorem pqxdhSha256Rows_no_1792_2048 :
    (pqxdhSha256Rows.all fun r =>
      (leBytes 64 r.2.1).drop 56 != toBEBytes 8 (1792 : BitVec 64) &&
      (leBytes 64 r.2.1).drop 56 != toBEBytes 8 (2048 : BitVec 64)) = true := by
  decide +kernel

theorem hmacWith_FP_of_ikm160_192 {k m : HwBytes} (hk : k.length ≤ 64)
    (hm : m.length = 160 ∨ m.length = 192) :
    TaggedP (hmacWith FP k m) := by
  refine ⟨hmacWith_FP_length k m, Classical.byContradiction fun h => ?_⟩
  have hin : (sha256With FP (kblk k 0x36#8 ++ m)).take 4 ≠ compTag4 :=
    hmac_inner_untaggedP k m hk h
  set M := kblk k 0x36#8 ++ m
  have hx : (kblk k 0x36#8).length = 64 := kblk_length k 0x36#8 hk
  rcases hm with hm160 | hm192
  · have hM : M.length = 224 := by dsimp [M]; rw [List.length_append, hx, hm160]
    let a := M.take 192
    let b := M.drop 192 ++ [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 (1792 : BitVec 64)
    have ha : a.length = 64 * 3 := by dsimp [a]; rw [List.length_take]; omega
    have hdM : (M.drop 192).length = 32 := by rw [List.length_drop]; omega
    have hb : b.length = 64 := by
      dsimp [b]; simp only [List.length_append, List.length_cons, List.length_nil,
        toBEBytes_length, hdM]
    have hpad : sha256Pad M = a ++ b := by
      unfold sha256Pad
      rw [hM]
      change M ++ [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 (1792 : BitVec 64) = a ++ b
      have htake : M.take 192 ++ M.drop 192 = M := List.take_append_drop 192 M
      dsimp [a, b]
      rw [← List.append_assoc, ← List.append_assoc, ← List.append_assoc, htake]
    have hsplit : chunks64 (sha256Pad M) = chunks64 a ++ b :: [] := by
      rw [hpad]; exact chunks64_append_last 3 ha hb
    have hon := onTabP_of_sha256With_untagged M hin (chunks64 a) b [] hsplit
    obtain ⟨_, _, _, row, hmem, _, hr2, _⟩ := pqxdhSha256_row_of_untagged hon
    have hrt := leBytes_bytesToNat b; rw [hb] at hrt
    have hblk : leBytes 64 row.2.1 = b := by rw [hr2, hrt]
    have hb56 : b.drop 56 = toBEBytes 8 (1792 : BitVec 64) := by
      have hpfx : (M.drop 192 ++ [0x80#8] ++ List.replicate 23 0#8).length = 56 := by
        simp [hdM]
      dsimp [b]; exact List.drop_left' hpfx
    have hall := List.all_eq_true.mp pqxdhSha256Rows_no_1792_2048 row hmem
    simp [hblk, hb56] at hall
  · have hM : M.length = 256 := by dsimp [M]; rw [List.length_append, hx, hm192]
    let b := [0x80#8] ++ List.replicate 55 0#8 ++ toBEBytes 8 (2048 : BitVec 64)
    have hb : b.length = 64 := by
      dsimp [b]; simp [toBEBytes_length]
    have hpad : sha256Pad M = M ++ b := by
      unfold sha256Pad; rw [hM]
      dsimp [b]; simp [List.append_assoc]
    have hsplit : chunks64 (sha256Pad M) = chunks64 M ++ b :: [] := by
      rw [hpad]; exact chunks64_append_last 4 (by omega) hb
    have hon := onTabP_of_sha256With_untagged M hin (chunks64 M) b [] hsplit
    obtain ⟨_, _, _, row, hmem, _, hr2, _⟩ := pqxdhSha256_row_of_untagged hon
    have hrt := leBytes_bytesToNat b; rw [hb] at hrt
    have hblk : leBytes 64 row.2.1 = b := by rw [hr2, hrt]
    have hb56 : b.drop 56 = toBEBytes 8 (2048 : BitVec 64) := by
      have hpfx : ([0x80#8] ++ List.replicate 55 0#8).length = 56 := by simp
      dsimp [b]; exact List.drop_left' hpfx
    have hall := List.all_eq_true.mp pqxdhSha256Rows_no_1792_2048 row hmem
    simp [hblk, hb56] at hall

/-! ## 2. Term-Level `TT` Tagging through `aliceAgreement`, `createChain`, and `computeMac` -/

theorem gamma_hmacP (S : OpaqueSymbolSemantics) (g : Ghost) (k m : DY.Bytes) :
    gamma pqxdhI0 S g (hmac k m) = hmacWith FP (gamma pqxdhI0 S g k) (gamma pqxdhI0 S g m) :=
  Symbolic.Swarm.CREF.TR.gamma_hmac pqxdhI0 S g k m

theorem gamma_concatP (S : OpaqueSymbolSemantics) (g : Ghost) (a b : DY.Bytes) :
    gamma pqxdhI0 S g (DY.Concat.concat a b) = gamma pqxdhI0 S g a ++ gamma pqxdhI0 S g b :=
  Symbolic.Swarm.CREF.TR.gamma_concat pqxdhI0 S g a b

theorem gamma_trunc8P (S : OpaqueSymbolSemantics) (g : Ghost) (x : DY.Bytes) :
    gamma pqxdhI0 S g (DY.Trunc.trunc8 x) = (gamma pqxdhI0 S g x).take 8 :=
  Symbolic.Swarm.CREF.TR.gamma_trunc8 pqxdhI0 S g x

theorem gamma_computeMacP (S : OpaqueSymbolSemantics) (g : Ghost) (mk sIk rIk w : DY.Bytes) :
    gamma pqxdhI0 S g (computeMac mk sIk rIk w) =
      (hmacWith FP (gamma pqxdhI0 S g mk)
        (gamma pqxdhI0 S g sIk ++ (gamma pqxdhI0 S g rIk ++ gamma pqxdhI0 S g w))).take 8 := by
  unfold computeMac; rw [gamma_trunc8P, gamma_hmacP, gamma_concatP, gamma_concatP]

def TT (S : OpaqueSymbolSemantics) (g : Ghost) (t : DY.Bytes) : Prop :=
  TaggedP (gamma pqxdhI0 S g t)

theorem tt_hmac_of_key {S : OpaqueSymbolSemantics} {g : Ghost} {k : DY.Bytes} (m : DY.Bytes)
    (hk : TT S g k) : TT S g (hmac k m) := by
  unfold TT; rw [gamma_hmacP]; exact hmacWith_FP_of_tagged_key _ hk

theorem tt_hmac_of_msg {S : OpaqueSymbolSemantics} {g : Ghost} (k : DY.Bytes) {m : DY.Bytes}
    (hm : TT S g m) : TT S g (hmac k m) := by
  unfold TT; rw [gamma_hmacP]; exact hmacWith_FP_of_tagged_msg _ hm

theorem tt_kdfCk_fst {S : OpaqueSymbolSemantics} {g : Ghost} {ck : DY.Bytes}
    (hck : TT S g ck) : TT S g (kdfCk ck).1 := by
  unfold kdfCk; exact tt_hmac_of_key _ hck

theorem tt_kdfCk_snd {S : OpaqueSymbolSemantics} {g : Ghost} {ck : DY.Bytes}
    (hck : TT S g ck) : TT S g (kdfCk ck).2 := by
  unfold kdfCk; exact tt_hmac_of_key _ hck

theorem tt_trMsgKeys_macKey {S : OpaqueSymbolSemantics} {g : Ghost}
    (pqSalt : DY.Bytes) {seed : DY.Bytes} (hseed : TT S g seed) :
    TT S g (trMsgKeys pqSalt seed).macKey := by
  unfold trMsgKeys hkdfBlock2
  exact tt_hmac_of_key _ (tt_hmac_of_msg pqSalt hseed)

theorem computeMac_tagged_of_tt {S : OpaqueSymbolSemantics} {g : Ghost}
    {mk : DY.Bytes} (sIk rIk w : DY.Bytes) (hmk : TT S g mk) :
    (gamma pqxdhI0 S g (computeMac mk sIk rIk w)).length = 8 ∧
    (gamma pqxdhI0 S g (computeMac mk sIk rIk w)).take 4 = compTag4 := by
  rw [gamma_computeMacP]
  have hf := hmacWith_FP_of_tagged_key
    (gamma pqxdhI0 S g sIk ++ (gamma pqxdhI0 S g rIk ++ gamma pqxdhI0 S g w)) hmk
  refine ⟨?_, ?_⟩
  · rw [List.length_take, hf.1]; decide
  · rw [List.take_take, show min 4 8 = 4 by decide]; exact hf.2

private theorem gamma_zeroSalt_len (S : OpaqueSymbolSemantics) (g : Ghost) :
    (gamma pqxdhI0 S g zeroSalt).length = 32 := by
  unfold zeroSalt
  rw [Symbolic.Swarm.CREF.TR.gamma_lit pqxdhI0 S g]
  decide

private theorem gamma_discontinuity_len (S : OpaqueSymbolSemantics) (g : Ghost) :
    (gamma pqxdhI0 S g discontinuity).length = 32 := by
  unfold discontinuity
  rw [Symbolic.Swarm.CREF.TR.gamma_lit pqxdhI0 S g]
  decide

private theorem gamma_agree_len (S : OpaqueSymbolSemantics) (g : Ghost) (pk sk : DY.Bytes) :
    (gamma pqxdhI0 S g (agree pk sk)).length = 32 := by
  rw [gamma_agree pqxdhI0 pqxdhI0_cryptoEquationsHold S g pk sk,
      pqxdhI0_agreement, Option.getD_some]
  exact compLookupDh_length _ _

private theorem gamma_kemEncap_snd_len (S : OpaqueSymbolSemantics) (g : Ghost)
    (pqPk entropy : DY.Bytes) (he : (gamma pqxdhI0 S g entropy).length = 32) :
    (gamma pqxdhI0 S g (DY.PQKem.kemEncap pqPk entropy).2).length = 32 := by
  rw [Symbolic.Swarm.CREF.TR.gamma_kemEncap_snd pqxdhI0 S g pqPk entropy]
  simp only [he, ↓reduceIte, pqxdhI0_kyberEncaps, Option.getD_some,
    List.length_drop, compKyberEncaps_length]

theorem tt_aliceAgreement_cks (S : OpaqueSymbolSemantics) (g : Ghost)
    (ikA ek ikB spk pqPk : DY.Bytes) (opk : Option DY.Bytes) (entropy dhsA : DY.Bytes)
    (he : (gamma pqxdhI0 S g entropy).length = 32) :
    TT S g (createChain (aliceAgreement ikA ek ikB spk pqPk opk entropy).2.rk spk dhsA).2 := by
  have hss0 := gamma_kemEncap_snd_len S g pqPk entropy he
  unfold aliceAgreement
  generalize hke : DY.PQKem.kemEncap pqPk entropy = ke at hss0 ⊢
  rcases ke with ⟨ct, ss⟩
  dsimp only at hss0 ⊢
  unfold createChain kdfRk hkdfBlock2
  apply tt_hmac_of_key
  apply tt_hmac_of_key
  unfold pqxdhKdf hkdfBlock1
  apply tt_hmac_of_key
  unfold TT
  rw [gamma_hmacP]
  have hk : (gamma pqxdhI0 S g zeroSalt).length ≤ 64 := by
    rw [gamma_zeroSalt_len]; omega
  refine hmacWith_FP_of_ikm160_192 hk ?_
  cases opk with
  | none =>
    left
    unfold pqxdhIkm; dsimp only [Option.map]
    simp only [gamma_concatP, List.length_append, gamma_discontinuity_len, gamma_agree_len, hss0]
  | some o =>
    right
    unfold pqxdhIkm; dsimp only [Option.map]
    simp only [gamma_concatP, List.length_append, gamma_discontinuity_len, gamma_agree_len, hss0]

/-! ## 3. Trace Stepping (`AliceInv`) Across Call 0 (`init`) and Call 1 (`send`) -/

def AliceInv (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) : Prop :=
  ∀ i st, (tr.at? i : Option TRStEntry) = some ⟨⟨"alice", st⟩⟩ → TT S g st.cks

theorem aliceInv_setupTrace (S : OpaqueSymbolSemantics) (g : Ghost) (r : ProtocolSetup) :
    AliceInv S g (setupTrace r) := by
  intro i st hat
  exact False.elim (traceStatesP_at?_st (traceStatesP_setupTrace (P := fun _ => False) r) hat)

private theorem at?_of_le_lt {E : Type} [ExecTraceTypes.Has E] {tr tr' : ExecTrace}
    (hle : tr ≤ tr') {i : Nat} (hi : i < tr.length) :
    (tr'.at? i : Option E) = (tr.at? i : Option E) := by
  have hi' : i < tr'.length := Nat.lt_of_lt_of_le hi (DY.Trace.length_le tr tr' hle)
  simp only [DY.Trace.at?, hi, hi', ↓reduceDIte]
  rw [← DY.Trace.at_le tr tr' i hi hle]

theorem aliceInv_append_other {E : Type} [ExecTraceTypes.Has E]
    {S : OpaqueSymbolSemantics} {g : Ghost} {tr : ExecTrace}
    (h : AliceInv S g tr) (e : E)
    (hnone : (DY.TraceEntryHas.proj (DY.TraceEntryHas.inj e : ExecTrace.Entry) :
      Option TRStEntry) = none) :
    AliceInv S g (tr.append e) := by
  intro i st hat
  rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases hat with ⟨hlt, hat0⟩ | ⟨_, hproj⟩
  · exact h i st hat0
  · rw [hnone] at hproj; cases hproj

theorem aliceInv_runSteps_network {S : OpaqueSymbolSemantics} {g : Ghost} :
    ∀ (pre : List Step) (tr : ExecTrace),
      (∀ x ∈ pre, ∃ msg, x = .network msg) →
      AliceInv S g tr → AliceInv S g (runSteps pre tr)
  | [], _, _, h => h
  | s :: pre, tr, hnet, h => by
    obtain ⟨m, rfl⟩ := hnet s List.mem_cons_self
    have h1 : AliceInv S g ((Step.network m).next tr) := by
      rw [next_network]; exact aliceInv_append_other h (NetE m) rfl
    exact aliceInv_runSteps_network pre _ (fun x hx => hnet x (List.mem_cons_of_mem _ hx)) h1

private theorem step_invisible_eq_network {s : Step} (h : s.cls = .invisible) :
    ∃ msg, s = .network msg := by
  cases s <;> simp [Step.cls] at h
  exact ⟨_, rfl⟩

private theorem stepsWF_append_right :
    ∀ (pre : List Step) {ss : List Step} {tr : ExecTrace},
      StepsWF (pre ++ ss) tr → StepsWF ss (runSteps pre tr)
  | [], _, _, hwf => hwf
  | _ :: pre, _, _, ⟨_, _, hwf⟩ => stepsWF_append_right pre hwf

private theorem matchesEventsAt_run_peel {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {initIds : Option BundlePreKeyIds} {tr : ExecTrace} {ss : List Step}
    {ev : RunEvent} {evs : List CliEvent} {vis visAll : List VisEntry}
    (hnotRej : ¬ RunRejected ev)
    (hwf : StepsWF ss tr)
    (hm : MatchesEventsAt pqxdhI0 r S g initIds tr ss (.run ev :: evs) vis)
    (hsub : ∀ w ∈ vis, w ∈ visAll) :
    ∃ pre s ss' v vs,
      (∀ x ∈ pre, ∃ msg, x = .network msg) ∧
      StepsWF ss' (s.next (runSteps pre tr)) ∧
      RunMatches pqxdhI0 r S g (runSteps pre tr) s ev v initIds ∧
      (∀ w ∈ v, w ∈ visAll) ∧
      (∀ w ∈ vs, w ∈ visAll) ∧
      MatchesEventsAt pqxdhI0 r S g (nextBundleIds initIds ev)
        (s.next (runSteps pre tr)) ss' evs vs := by
  cases hm with
  | run0 _ hrej _ => exact False.elim (hnotRej hrej)
  | run1 hinv hrm hrest =>
    have hwf' := stepsWF_append_right _ hwf
    obtain ⟨_, _, hwf_tail⟩ := hwf'
    refine ⟨_, _, _, _, _, fun x hx => step_invisible_eq_network (hinv x hx),
      hwf_tail, hrm,
      fun w hw => hsub w (List.mem_append_left _ hw),
      fun w hw => hsub w (List.mem_append_right _ hw), hrest⟩

private structure HSKeys (tr₀ : ExecTrace) (o : AliceHandshakeOut) : Prop where
  keys_eq : ∃ ikA ek ikB pqPk,
    o.keys = (aliceAgreement ikA ek ikB o.spk pqPk o.opk (randTerm (tr₀.length + 1) 32)).2

private structure HSWpOut (tr₀ : ExecTrace) {α : Type} (P : α → Prop) (x : Traceful α) : Prop where
  ok : ∀ a, (x.run tr₀).1 = some a →
    P a ∧ (x.run tr₀).2.val = (tr₀.append (RndE 32)).append (RndE 32)

private theorem HSWpOut.bind_ro {tr₀ : ExecTrace} {α β : Type} {P : β → Prop}
    {x : Traceful α} {f : α → Traceful β}
    (hx : Preserves (fun t => t = tr₀) x)
    (hf : ∀ a, HSWpOut tr₀ P (f a)) : HSWpOut tr₀ P (x >>= f) :=
  ⟨fun b hb => by
    rw [run_bind_fst] at hb
    rw [run_bind_snd]
    have htr : (x.run tr₀).2.val = tr₀ := hx.run tr₀ rfl
    rcases hx1 : (x.run tr₀).1 with _ | a
    · simp [hx1] at hb
    · simp only [hx1] at hb ⊢; rw [htr] at hb ⊢; exact (hf a).ok b hb⟩

private theorem aliceHandshake_out_keys (a b : Participant) (idStateIdx regIdxB : Nat)
    (h : BundleHandles) (tr₀ : ExecTrace) :
    HSWpOut tr₀ (HSKeys tr₀) (aliceHandshake a b idStateIdx regIdxB h) := by
  unfold aliceHandshake
  apply HSWpOut.bind_ro (Preserves.getKey a idStateIdx .identity); intro ikA
  apply HSWpOut.bind_ro (Preserves.lookupIdentity b regIdxB); intro p
  rcases p with ⟨ikB, vkB⟩; dsimp only
  apply HSWpOut.bind_ro (Preserves.receiveMessage h.spk); intro spk
  apply HSWpOut.bind_ro (Preserves.receiveMessage h.spkSig); intro spkSig
  apply HSWpOut.bind_ro (Preserves.receiveMessage h.pqpk); intro pqpk
  apply HSWpOut.bind_ro (Preserves.receiveMessage h.pqpkSig); intro pqpkSig
  apply HSWpOut.bind_ro (Preserves.guardP _); intro _
  apply HSWpOut.bind_ro (Preserves.guardP _); intro _
  have htail : ∀ opk : Option DY.Bytes, HSWpOut tr₀ (HSKeys tr₀) (do
      let ek ← DY.Random.genRand 32
      _root_.guard (!DY.Libsignal.PQXDH.x25519LowOrder spk)
      _root_.guard (opk.all fun o => !DY.Libsignal.PQXDH.x25519LowOrder o)
      let entropy ← DY.Random.genRand 32
      let (ct, keys) := aliceAgreement ikA ek ikB spk pqpk opk entropy
      Pure.pure { ikA := DY.DiffieHellman.dhPk ikA, ikB, spk, pqpk, opk,
                  ek := DY.DiffieHellman.dhPk ek, ct, keys }) := by
    intro opk
    refine ⟨fun out hout => ?_⟩
    unfold _root_.guard at hout ⊢
    by_cases hp1 : (!DY.Libsignal.PQXDH.x25519LowOrder spk) = true
    · by_cases hp2 : (opk.all fun o => !DY.Libsignal.PQXDH.x25519LowOrder o) = true
      · simp only [hp1, hp2, ↓reduceIte, run_bind_fst, run_bind_snd,
          (Runs.genRand _ 32).1, (Runs.genRand _ 32).2,
          DY.Traceful.run_pure, Option.some.injEq] at hout ⊢
        have hlen1 : (tr₀.append (RndE 32)).length = tr₀.length + 1 := by
          simp [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
        subst hout
        exact ⟨⟨⟨ikA, randTerm tr₀.length 32, ikB, pqpk, by rw [hlen1]⟩⟩, trivial⟩
      · simp [hp1, hp2, run_bind_fst, (Runs.genRand _ 32).1, DY.Traceful.run_pure,
          DY.Traceful.run_failure] at hout
    · simp [hp1, run_bind_fst, (Runs.genRand _ 32).1, DY.Traceful.run_failure] at hout
  cases h.opk <;> dsimp only
  · apply HSWpOut.bind_ro Preserves.pure; intro opk; exact htail opk
  · apply HSWpOut.bind_ro (Preserves.receiveMessage _); intro _
    apply HSWpOut.bind_ro Preserves.pure; intro opk; exact htail opk

theorem alice_init_step_inv {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {pre : List Step} {s : Step} {ev : RunEvent}
    {v visAll : List VisEntry}
    (hgwf : GhostWF g visAll)
    (hinv : AliceInv S g tr)
    (hnet : ∀ x ∈ pre, ∃ msg, x = .network msg)
    (hinit : ev.party = "alice" ∧ ∃ peer regId, ev.cmd = .init peer regId)
    (hrm : RunMatches pqxdhI0 r S g (runSteps pre tr) s ev v none)
    (hv_sub : ∀ w ∈ v, w ∈ visAll) :
    AliceInv S g (s.next (runSteps pre tr)) := by
  set tr₀ := runSteps pre tr
  have hinv₀ : AliceInv S g tr₀ := aliceInv_runSteps_network pre tr hnet hinv
  obtain ⟨_, hparty, hfits, _, hok, _, hv_eq, _⟩ := hrm
  obtain ⟨hp_alice, peer, regId, hcmd⟩ := hinit
  rw [hp_alice] at hparty; rw [hcmd] at hfits
  cases s with
  | aliceStart a b idStateIdx regIdxB h =>
    simp only [Step.party?, Option.some.injEq] at hparty; subst hparty
    have hnr := aliceStart_ok_newRandoms "alice" b idStateIdx regIdxB h tr₀ hok
    have hkyb_mem : (⟨.rng, [randTerm (tr₀.length + 1) 32], .kyberCoin 0, none⟩ : VisEntry) ∈ visAll := by
      apply hv_sub; rw [hv_eq]; unfold stepView; simp only [hok, ↓reduceIte]
      apply List.mem_append_left; unfold aliceVis; rw [hnr]
      apply List.mem_cons_of_mem; apply List.mem_cons_of_mem
      apply List.mem_append_left; unfold kyberCoinEntries
      exact List.mem_map.mpr ⟨0, by simp, rfl⟩
    have he32 : (gamma pqxdhI0 S g (randTerm (tr₀.length + 1) 32)).length = 32 := by
      rw [Symbolic.Proofs.Swarm.UA.XlateSteps.gamma_randTerm_eq _ _ _ _ _ (by decide)]
      exact hgwf.1 _ hkyb_mem rfl (tr₀.length + 1) 32 (by decide) (by simp)
    have hok_eq :
        ((DY.Libsignal.Composed.aliceStart "alice" b idStateIdx regIdxB h).run tr₀).1.isSome = true := by
      rwa [show (Step.aliceStart "alice" b idStateIdx regIdxB h).ok tr₀ =
          ((DY.Libsignal.Composed.aliceStart "alice" b idStateIdx regIdxB h).run tr₀).1.isSome from
        stepIn_ok DY.Libsignal.Composed.aliceStart.reachability
          ("alice", b, idStateIdx, regIdxB, h) tr₀] at hok
    have hnext_eq :
        (Step.aliceStart "alice" b idStateIdx regIdxB h).next tr₀ =
          ((DY.Libsignal.Composed.aliceStart "alice" b idStateIdx regIdxB h).run tr₀).2.val :=
      stepIn_next DY.Libsignal.Composed.aliceStart.reachability
        ("alice", b, idStateIdx, regIdxB, h) tr₀
    unfold DY.Libsignal.Composed.aliceStart at hok_eq hnext_eq
    rw [run_bind_fst] at hok_eq
    rcases hhs : (aliceHandshake "alice" b idStateIdx regIdxB h).run tr₀ with ⟨_ | o, ⟨tr_hs, hle_hs⟩⟩
    · simp [hhs] at hok_eq
    · obtain ⟨⟨ikA, ek, ikB, pqPk, hkeys_eq⟩, htr_hs⟩ :=
        (aliceHandshake_out_keys "alice" b idStateIdx regIdxB h tr₀).ok o
          (by rw [hhs])
      rw [hhs] at htr_hs; dsimp only at htr_hs; subst htr_hs
      rw [run_bind_snd, hhs] at hnext_eq; dsimp only at hnext_eq
      let tr_d := ((tr₀.append (RndE 32)).append (RndE 32)).append (RndE 32)
      let dhsA := randTerm ((tr₀.append (RndE 32)).append (RndE 32)).length 32
      let stA : TRState := {
        peer := b, myIk := DY.Libsignal.PQXDH.serializedIk o.ikA,
        peerIk := DY.Libsignal.PQXDH.serializedIk o.ikB,
        rk := (createChain o.keys.rk o.spk dhsA).1, dhs := dhsA,
        cks := (createChain o.keys.rk o.spk dhsA).2, ns := 0, pn := 0,
        sid := DY.Concat.concat (DY.DiffieHellman.dhPk dhsA) o.keys.rk,
        initiator := true, rIdx := 1,
        recv := [{ ratchetKey := o.spk, chainKey := o.keys.ck, index := 0, rIdx := 1 }],
        spqr := DY.Spqr.spqrInit o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B }
      have hcks_tt : TT S g stA.cks := by
        show TT S g (createChain o.keys.rk o.spk dhsA).2
        rw [hkeys_eq]
        exact tt_aliceAgreement_cks S g ikA ek ikB o.spk pqPk o.opk _ dhsA he32
      have htr_shape :
          ∃ (e1 e2 : DY.Network.ExecEntryT)
            (e3 : DY.ProtocolEvent.ExecEntryT DY.Libsignal.PQXDH.PQXDHEvent)
            (e4 : DY.ProtocolEvent.ExecEntryT TREvent)
            (e5 : DY.ProtocolEvent.ExecEntryT ComposedEvent),
            (Step.aliceStart "alice" b idStateIdx regIdxB h).next tr₀ =
              ((((((((tr₀.append (RndE 32)).append (RndE 32)).append (RndE 32)).append
                e1).append e2).append e3).append e4).append e5).append (TRStE "alice" stA) := by
        rw [hnext_eq]
        simp only [DY.Libsignal.TripleRatchet.traceLength,
          Symbolic.DYBridge.DY.Random.genRand_eq_1,
          Symbolic.DYBridge.DY.Network.sendMessage_eq_1,
          Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1,
          DY.Traceful.run_bind, DY.Traceful.run_mk, DY.Traceful.run_pure]
        exact ⟨_, _, _, _, _, rfl⟩
      obtain ⟨e1, e2, e3, e4, e5, htr_shape⟩ := htr_shape
      rw [htr_shape]
      have hmid : AliceInv S g
          ((((((((tr₀.append (RndE 32)).append (RndE 32)).append (RndE 32)).append
            e1).append e2).append e3).append e4).append e5) :=
        aliceInv_append_other
          (aliceInv_append_other
            (aliceInv_append_other
              (aliceInv_append_other
                (aliceInv_append_other
                  (aliceInv_append_other
                    (aliceInv_append_other
                      (aliceInv_append_other hinv₀ (RndE 32) rfl)
                      (RndE 32) rfl)
                    (RndE 32) rfl)
                  e1 rfl)
                e2 rfl)
              e3 rfl)
            e4 rfl)
          e5 rfl
      intro i st hat
      rcases Symbolic.Swarm.COMPOSED.CompTrace.at?_append_cases hat with ⟨_, hat0⟩ | ⟨_, hproj⟩
      · exact hmid i st hat0
      · simp only [TRStE, Symbolic.Swarm.COMPOSED.CompTrace.proj_inj_eq,
          Option.some.injEq] at hproj
        injection hproj with hst_eq
        injection hst_eq with _ hst_eq'
        subst hst_eq'
        exact hcks_tt
  | _ => cases hfits

/-! ## 4. Call 1 (`alice send`) PreKey Output Contradiction -/

private theorem not_send_mem_encDraws {nr : List (DY.Bytes × Nat)} {v : VisEntry}
    (hv : v ∈ encDraws nr) (hk : v.kind = .send) : False := by
  unfold encDraws at hv
  split at hv
  · cases hv
  · rcases List.mem_cons.mp hv with rfl | hrest
    · cases hk
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hrest
      cases hk

private theorem not_send_mem_exposures {tr tr' : ExecTrace} {v : VisEntry}
    (hv : v ∈ exposures tr tr') (hk : v.kind = .send) : False := by
  unfold exposures at hv
  rcases List.mem_append.mp hv with hpq | htr
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hpq
    unfold pqExposureAt at hj
    split at hj <;> simp at hj <;> (subst hj; cases hk)
  · obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp htr
    unfold trExposureAt at hj
    split at hj <;> simp at hj <;> (subst hj; cases hk)

private theorem step_ok_encryptAbort_false (me : Participant) (stateIdx : Nat) (tr : ExecTrace) :
    (Step.messageEncryptAbort me stateIdx).ok tr = false := by
  unfold Step.ok Step.toInput
  rw [stepIn_ok DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability (me, stateIdx) tr]
  dsimp only [DY.Libsignal.TripleRatchet.messageEncryptAbort.reachability,
    DY.Libsignal.TripleRatchet.messageEncryptAbort]
  rw [run_bind_fst]
  rcases ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr).1 with
    _ | _
  · rfl
  · dsimp only
    rw [run_bind_fst, (Runs.genRand _ 32).1]
    dsimp only; rw [DY.Traceful.run_failure]; rfl

private theorem messageEncrypt_lastSent {me : Participant} {stateIdx cl pq : Nat} {tr₁ : ExecTrace}
    (hok : (Step.messageEncrypt me stateIdx cl pq).ok tr₁ = true) :
    ∃ st pqSalt wire,
      (tr₁.at? stateIdx : Option TRStEntry) = some ⟨⟨me, st⟩⟩ ∧
      lastSent tr₁ ((Step.messageEncrypt me stateIdx cl pq).next tr₁) =
        some (DY.Concat.concat wire
          (computeMac (trMsgKeys pqSalt (kdfCk st.cks).2).macKey st.myIk st.peerIk wire)) := by
  unfold Step.ok Step.toInput at hok
  rw [stepIn_ok DY.Libsignal.TripleRatchet.messageEncrypt.reachability
    (me, stateIdx, cl, pq) tr₁] at hok
  have hnext : (Step.messageEncrypt me stateIdx cl pq).next tr₁ = _ :=
    stepIn_next DY.Libsignal.TripleRatchet.messageEncrypt.reachability
      (me, stateIdx, cl, pq) tr₁
  dsimp only [DY.Libsignal.TripleRatchet.messageEncrypt.reachability] at hok hnext
  unfold messageEncrypt at hok hnext
  rw [run_bind_fst] at hok; rw [run_bind_snd] at hnext
  rcases hst : ((DY.PersistentLocalState.getLocalState me stateIdx : Traceful TRState).run tr₁).1
    with _ | st
  · rw [hst] at hok; cases hok
  · have hat_st := bks_stored_of_getLocalState hst
    rw [hst, getLocalState_snd] at hok hnext; dsimp only at hok hnext
    have hguard : (_root_.guard (st.ns ≠ u32Max) : Traceful Unit) = pure () := by
      unfold _root_.guard; split
      · rfl
      · next hneg =>
        exfalso; unfold _root_.guard at hok; split at hok
        · next hpos => exact hneg hpos
        · rw [run_bind_fst, DY.Traceful.run_failure] at hok; cases hok
    rw [hguard] at hok hnext
    rw [run_bind_fst, DY.Traceful.run_pure] at hok; dsimp only at hok
    rw [run_bind_snd, DY.Traceful.run_pure] at hnext; dsimp only at hnext
    rw [run_bind_fst, (Runs.genRand tr₁ 32).1, (Runs.genRand tr₁ 32).2] at hok
    rw [run_bind_snd, (Runs.genRand tr₁ 32).1, (Runs.genRand tr₁ 32).2] at hnext
    dsimp only at hok hnext
    let tr_r1 := tr₁.append (RndE 32)
    rw [run_bind_fst, (Runs.genRand tr_r1 cl).1, (Runs.genRand tr_r1 cl).2] at hok
    rw [run_bind_snd, (Runs.genRand tr_r1 cl).1, (Runs.genRand tr_r1 cl).2] at hnext
    dsimp only at hok hnext
    let tr_r2 := tr_r1.append (RndE cl)
    let spqrOut := DY.Spqr.spqrSend st.spqr (randTerm tr_r1.length cl)
    rw [run_bind_fst, (Runs.sendMessage tr_r2 spqrOut.2.1).1,
        (Runs.sendMessage tr_r2 spqrOut.2.1).2] at hok
    rw [run_bind_snd, (Runs.sendMessage tr_r2 spqrOut.2.1).1,
        (Runs.sendMessage tr_r2 spqrOut.2.1).2] at hnext
    dsimp only at hok hnext
    let tr_k := tr_r2.append (NetE spqrOut.2.1)
    rw [run_bind_fst, rpkT_receiveMessage_fst, receiveMessage_snd] at hok
    rw [run_bind_snd, rpkT_receiveMessage_fst, receiveMessage_snd] at hnext
    rcases hpq : tr_k.getMessageSentAt pq with _ | pqSalt
    · rw [hpq] at hok; cases hok
    · rw [hpq] at hnext; dsimp only at hnext
      let m := randTerm tr₁.length 32
      let seed := (kdfCk st.cks).2
      let keys := trMsgKeys pqSalt seed
      let wire := trHonestWireMsg (DY.DiffieHellman.dhPk st.dhs) st.ns st.pn
        (DY.SymEnc.symEnc keys.cipherKey keys.iv m) spqrOut.2.2
      let mac := computeMac keys.macKey st.myIk st.peerIk wire
      let evSent := TREvent.Sent me st.peer (DY.DiffieHellman.dhPk st.dhs) st.ns m
      have hl1 : ((DY.ProtocolEvent.logEvent evSent).run tr_k).1 = some () := by
        simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
          DY.Traceful.run_mk, DY.Traceful.run_pure]
      rw [run_bind_snd, hl1, logEvent_snd_eq evSent tr_k] at hnext; dsimp only at hnext
      let tr_s := tr_k.append (TREvE evSent)
      rw [run_bind_snd] at hnext; unfold logMessageKeyAndStore at hnext
      let evMk := TREvent.MessageKey (st.sessionInfo me) .sender seed pqSalt st.ns st.rIdx stateIdx
      have hmk1 : ((DY.ProtocolEvent.logEvent evMk).run tr_s).1 = some () := by
        simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_bind,
          DY.Traceful.run_mk, DY.Traceful.run_pure]
      rw [run_bind_snd, run_bind_fst, hmk1, logEvent_snd_eq evMk tr_s] at hnext
      dsimp only at hnext
      let tr_mk := tr_s.append (TREvE evMk)
      let st' : TRState := { st with cks := (kdfCk st.cks).1, ns := st.ns + 1, spqr := spqrOut.1 }
      have hst1 : ((DY.PersistentLocalState.storeLocalState me st').run tr_mk).1 =
          some tr_mk.length := by
        simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1,
          Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1,
          Symbolic.DYBridge.DY.appendEntry_eq_1, DY.Traceful.run_mk]
      rw [hst1, storeLocalState_tr_snd_eq me st' tr_mk] at hnext; dsimp only at hnext
      let tr_bef := tr_mk.append (TRStE me st')
      let msgTerm := DY.Concat.concat wire mac
      rw [(Runs.sendMessage tr_bef msgTerm).2] at hnext
      refine ⟨st, pqSalt, wire, hat_st, ?_⟩
      rw [hnext]; unfold lastSent
      have hlen_app : ∀ {E : Type} [ExecTraceTypes.Has E] (t : ExecTrace) (x : E),
          (t.append x).length = t.length + 1 := fun _ _ => by
        simp only [Symbolic.DYBridge.DY.Trace.append_eq_1, Symbolic.DYBridge.DY.Trace.length_eq_2]
      have hlt : tr₁.length < (tr_bef.append (NetE msgTerm)).length := by
        dsimp [tr_bef, tr_mk, tr_s, tr_k, tr_r2, tr_r1]
        simp only [hlen_app]; omega
      simp only [hlt, ↓reduceIte]
      have hidx : (tr_bef.append (NetE msgTerm)).length - 1 = tr_bef.length := by
        rw [hlen_app]; omega
      rw [hidx]
      exact rpkT_getMessageSentAt_of_at? (Symbolic.Swarm.CREF.at?_append_length tr_bef (NetE msgTerm))

def dummyRunEvent : RunEvent :=
  { party := "", cmd := .send ⟨"", 0⟩, input := [], coins := [], exit := none }

def pqxdhEv0 : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.PqxdhKemSsOmittedCli.trace with
  | .run e0 :: _ => e0
  | _ => dummyRunEvent

def pqxdhEv1 : RunEvent :=
  match Symbolic.BugInjection.Synthetic.Witnesses.PqxdhKemSsOmittedCli.trace with
  | _ :: .run e1 :: _ => e1
  | _ => dummyRunEvent

def pqxdhOut1 : HwBytes :=
  match pqxdhEv1.exit with
  | some (_, out) => out
  | none => []

private def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

private theorem hexBytes_ofList (cs : List Char) :
    Symbolic.BugInjection.hexBytes (String.ofList cs) =
      Symbolic.BugInjection.hexBytes.go hexDigit cs := by
  unfold Symbolic.BugInjection.hexBytes hexDigit; rw [String.toList_ofList]

attribute [local irreducible] Symbolic.BugInjection.hexBytes

local elab "chars_of_hex_out" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

local elab "str_of_hex_out" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let args := eWhnf.getAppArgs
  let sLit ← Lean.Meta.whnf args[0]!
  return sLit

private def pqxdhOut1Chars : List Char := chars_of_hex_out pqxdhOut1
private theorem pqxdhOut1_eq_hex :
    pqxdhOut1 = Symbolic.BugInjection.hexBytes (str_of_hex_out pqxdhOut1) := rfl
private theorem pqxdhOut1Str_eq : (str_of_hex_out pqxdhOut1) = String.ofList pqxdhOut1Chars := rfl
private def pqxdhOut1Fast : HwBytes := Symbolic.BugInjection.hexBytes.go hexDigit pqxdhOut1Chars

private theorem pqxdhOut1_eq_fast : pqxdhOut1 = pqxdhOut1Fast := by
  change pqxdhOut1 = Symbolic.BugInjection.hexBytes.go hexDigit pqxdhOut1Chars
  rw [pqxdhOut1_eq_hex, pqxdhOut1Str_eq, hexBytes_ofList]

private theorem pqxdhEv0_not_rej : ¬ RunRejected pqxdhEv0 := by
  intro h; exact h (Symbolic.BugInjection.hexBytes "") rfl

private theorem pqxdhEv1_not_rej : ¬ RunRejected pqxdhEv1 := by
  intro h; exact h pqxdhOut1 rfl

private theorem pqxdhEv1_wrapped : runWrapped pqxdhEv1 = true := by
  have hexit : pqxdhEv1.exit = some (0, pqxdhOut1) := rfl
  unfold runWrapped
  rw [hexit, pqxdhOut1_eq_fast]
  decide +kernel

private theorem pqxdhOut1_lt : pqxdhOut1.length < 2 ^ 63 := by
  rw [pqxdhOut1_eq_fast]; decide +kernel

private theorem pqxdhOut1_parse_untagged :
    ∃ p : PreKeyFields,
      parsePreKeyWire pqxdhOut1 = some p ∧
      (p.message.drop (p.message.length - 8)).take 4 ≠ compTag4 := by
  rw [pqxdhOut1_eq_fast]
  have h : ((parsePreKeyWire pqxdhOut1Fast).map fun p =>
      (p.message.drop (p.message.length - 8)).take 4 != compTag4) = some true := by
    decide +kernel
  rcases hp : parsePreKeyWire pqxdhOut1Fast with _ | p
  · rw [hp] at h; cases h
  · rw [hp, Option.map_some, Option.some.injEq, bne_iff_ne] at h
    exact ⟨p, rfl, h⟩

theorem not_explains_prefix2
    (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ss : List Step) (vis : List VisEntry) (tail : List CliEvent)
    (hex : Explains pqxdhI0 r S g ss vis (.run pqxdhEv0 :: .run pqxdhEv1 :: tail)) :
    False := by
  obtain ⟨_, hgwf, ⟨_, _, hwf_ss, _⟩, hme⟩ := hex
  obtain ⟨pre₀, s₀, ss₁, v₀, vs₁, hnet₀, hwf₁, hrm₀, hv₀_sub, hvs₁_sub, hme₁⟩ :=
    matchesEventsAt_run_peel pqxdhEv0_not_rej hwf_ss hme (fun _ h => h)
  have hinv₁ : AliceInv S g (s₀.next (runSteps pre₀ (setupTrace r))) :=
    alice_init_step_inv hgwf (aliceInv_setupTrace S g r) hnet₀
      ⟨rfl, _, _, rfl⟩ hrm₀ hv₀_sub
  obtain ⟨pre₁, s₁, _, v₁, _, hnet₁, _, hrm₁, _, _, _⟩ :=
    matchesEventsAt_run_peel pqxdhEv1_not_rej hwf₁ hme₁ hvs₁_sub
  set tr₁ := runSteps pre₁ (s₀.next (runSteps pre₀ (setupTrace r)))
  have hinv_tr₁ : AliceInv S g tr₁ := aliceInv_runSteps_network pre₁ _ hnet₁ hinv₁
  obtain ⟨_, hparty₁, hfits₁, _, hok₁, _, hv₁_eq, inp₁, drs₁, outs₁, hv₁_split,
    _, _, houts₁, _, _⟩ := hrm₁
  have hcmd₁ : pqxdhEv1.cmd = .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ := rfl
  have hexit₁ : pqxdhEv1.exit = some (0, pqxdhOut1) := rfl
  have hp₁ : pqxdhEv1.party = "alice" := rfl
  rw [hp₁] at hparty₁; rw [hcmd₁] at hfits₁
  cases s₁ with
  | messageEncryptAbort me stateIdx =>
    rw [step_ok_encryptAbort_false] at hok₁; cases hok₁
  | messageEncrypt me stateIdx cl pq =>
    simp only [Step.party?, Option.some.injEq] at hparty₁; subst hparty₁
    obtain ⟨st, pqSalt, wire, hat_st, hls⟩ := messageEncrypt_lastSent hok₁
    have hcks_tt : TT S g st.cks := hinv_tr₁ stateIdx st hat_st
    have hmac_tag := computeMac_tagged_of_tt st.myIk st.peerIk wire
      (tt_trMsgKeys_macKey pqSalt (tt_kdfCk_snd hcks_tt))
    unfold OutputsMatch at houts₁
    rw [hexit₁, hcmd₁] at houts₁
    obtain ⟨v_out, rfl, hbme_out⟩ := houts₁
    have hv_in_v₁ : v_out ∈ v₁ := by
      rw [hv₁_split]; exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
    rw [hv₁_eq] at hv_in_v₁
    unfold stepView at hv_in_v₁
    simp only [hok₁, ↓reduceIte] at hv_in_v₁
    have hv_in_enc : v_out ∈ encSendEntry tr₁
        ((Step.messageEncrypt "alice" stateIdx cl pq).next tr₁) stateIdx (runWrapped pqxdhEv1) := by
      rcases List.mem_append.mp hv_in_v₁ with hown | hexp
      · rcases List.mem_append.mp hown with hdr | henc
        · exact False.elim (not_send_mem_encDraws hdr hbme_out.1.symm)
        · exact henc
      · exact False.elim (not_send_mem_exposures hexp hbme_out.1.symm)
    rw [pqxdhEv1_wrapped] at hv_in_enc
    unfold encSendEntry at hv_in_enc
    rw [hls] at hv_in_enc
    dsimp only at hv_in_enc
    rcases hppk : pendingPreKey tr₁ stateIdx with _ | ⟨ekT, ctT⟩ <;> rw [hppk] at hv_in_enc
    · cases hv_in_enc
    · rcases List.mem_singleton.mp hv_in_enc with rfl
      unfold BytesMatchEntry SendMatches at hbme_out
      obtain ⟨_, preKeyId, spkId, kpkId, _, hout_eq⟩ := hbme_out
      obtain ⟨p1, hp1, huntag1⟩ := pqxdhOut1_parse_untagged
      have hmsg_eq :=
        (parsePreKeyWire_preKeyWire_inv hout_eq pqxdhOut1_lt hp1).2.2.2
      rw [gamma_concatP] at hmsg_eq
      let macBytes := gamma pqxdhI0 S g
        (computeMac (trMsgKeys pqSalt (kdfCk st.cks).2).macKey st.myIk st.peerIk wire)
      let wireBytes := gamma pqxdhI0 S g wire
      change p1.message = wireBytes ++ macBytes at hmsg_eq
      have hdrop : p1.message.drop (p1.message.length - 8) = macBytes := by
        rw [hmsg_eq, List.length_append, hmac_tag.1,
            show wireBytes.length + 8 - 8 = wireBytes.length by omega]
        exact List.drop_left' rfl
      exact huntag1 (by rw [hdrop]; exact hmac_tag.2)
  | _ => cases hfits₁

end Symbolic.BugInjection.Proofs.SyntheticPqxdhKemSsOmitted.NoPrefixExplains
