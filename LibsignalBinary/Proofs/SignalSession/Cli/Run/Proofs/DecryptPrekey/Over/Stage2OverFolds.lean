/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ArmsB -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Bridges -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Folds -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.Canon
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.InitInv
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.MatchedMatchFold
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Agree
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1Base
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.StagesInst.Stage2V1OkFold
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4KyberRefused -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathAKeys
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.E2E.Seed.Defs

/-!
# CLI Poll Stage P2 Over-Path (`Path C`) Spatial and Encoding Folds

Provides the `+0x0868` entry spatial unpack (`stageP2_entry_unpack_pathCOver`), `+0x1778` `Prev1`
normal-exit spatial fold (`p2OverOkPost_fold_pathCOver`), 32-bit encoded-session length bound
(`encSessionMem_clearPending_lt_32`), stack-budget bound, and `subroutine_ok` ghost-struct transport
helpers.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeySavedRegsAt)

/-- Stage P3 (`+0x1778`) extra precondition on the Over-path (`Prev1`), definitionally (`rfl`) equal
to `Over.stageP3Sub5ExtraPrePrev1` (`ClosureOver.lean`). -/
@[expose] def p2StageP3Sub5ExtraPrePrev1 (A : RustAlloc) (s0 s : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr : BitVec 64)
    (enc : List (BitVec 8)) (b_2c0 : BitVec 8) : SepProp :=
  ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x448#64) 240 ∗
  OverP2.prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0

namespace OverP2Inst

open Arm64.Process ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## 1. Generic `subroutine_ok` Ghost-Struct Transport -/

/-- Transport `subroutine_ok prog fn s1` along a ghost-type reindexing `f : β → α` when
`pre`, `post`, `onPanic`, `onExit`, and `onOom` agree point-for-point (`rfl` across nominal ghost structures). -/
theorem subroutine_ok_of_spec_map {α β : Type} {prog : Program} {fn : BitVec 64}
    {s1 : Spec α} {s2 : Spec β}
    (f : β → α)
    (hpre : ∀ (y : β) (st : State), s1.pre (f y) st = s2.pre y st)
    (hpost : ∀ (y : β) (s0 sf : State), s1.post (f y) s0 sf = s2.post y s0 sf)
    (hpan : ∀ (y : β) (s0 sf : State), s1.onPanic (f y) s0 sf = s2.onPanic y s0 sf)
    (hexit : ∀ (y : β) code (s0 sf : State), s1.onExit (f y) code s0 sf = s2.onExit y code s0 sf)
    (hoom : ∀ (y : β) (s0 sf : State), s1.onOom (f y) s0 sf = s2.onOom y s0 sf)
    (hok : subroutine_ok prog fn s1) :
    subroutine_ok prog fn s2 := by
  refine subroutine_ok_outcome_intro fun y R s0 hpc hrun hm halign => ?_
  rw [← hpre y s0] at hm
  refine hok.mono_outcome (f y) R s0 hpc hrun hm halign fun sf hout => ?_
  rcases hout with ⟨hret, hcs, hp⟩ | ⟨hpanst, hpanp⟩ | ⟨code, hexst, hexp⟩ | ⟨hoomst, hoomp⟩
  · rw [hpost y s0 sf] at hp
    exact Or.inl ⟨hret, hcs, hp⟩
  · rw [hpan y s0 sf] at hpanp
    exact Or.inr (Or.inl ⟨hpanst, hpanp⟩)
  · rw [hexit y code s0 sf] at hexp
    exact Or.inr (Or.inr (Or.inl ⟨code, hexst, hexp⟩))
  · rw [hoom y s0 sf] at hoomp
    exact Or.inr (Or.inr (Or.inr ⟨hoomst, hoomp⟩))

theorem p2Over_serBytes_len (m : PreKeyMessageFields) :
    (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk).length = 33 := by
  dsimp only [mkPathAHdr]
  rw [bytesToBv8_vecU8 m.baseKey]
  simp [m.baseKey.toList_length]

theorem p2Over_not_sessMatchesMsg (sess : Session (List (BitVec 8)))
    (pm : PreKeySignalMessage) (m : PreKeyMessageFields) (i : SignalMessage)
    (hpm : pm = pmOfE m i) (hnot : ¬ SessMatchesPm sess pm) :
    ¬ Over.P2SessMatchesMsg sess 4#8 (5#8 :: bytesToBv8 (mkPathAHdr m).ekAPk) := by
  intro ⟨hver, hbk⟩
  apply hnot
  subst hpm
  obtain ⟨hmver, _, _, _, hbase, _, _, _⟩ := pmOfE_fields m i
  refine ⟨?_, ?_⟩
  · rw [hmver]; exact hver
  · dsimp only [PublicKey.serialize]
    rw [hbase]
    dsimp only [mkPathAHdr] at hbk
    rw [bytesToBv8_vecU8 m.baseKey] at hbk
    exact hbk

theorem sessionAt_dup_canonSession (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (s : Session (List (BitVec 8))) :
    sessionStateReprAt A ss G s ⊢
      ⌜E2E.Record.Serialization.CanonSession G s⌝ ∗ sessionStateReprAt A ss G s :=
  ProofLib.Entails.extract_heap_fact (E2E.InMem.SessionStoreImpl.canonSession_of_sessionAt A ss G s)

theorem pathAMsgRemInnerAt_dup_kyberPtr (g : PreKeyMsgGhost) (msgA : BitVec 64)
    (m : PreKeyMessageFields) (i : SignalMessage) :
    pathAMsgRemInnerAt g msgA m i ⊢
      ⌜g.kyberPtr ≠ 0#64⌝ ∗ pathAMsgRemInnerAt g msgA m i := by
  unfold pathAMsgRemInnerAt
  refine Entails.pure_left fun h => ?_
  have hne : g.kyberPtr ≠ 0#64 := h.1
  exact Entails.pure_right hne (Entails.pure_right h (Entails.refl _))

theorem canonSession_clearPending {G : SessionGhost} {s : Session (List (BitVec 8))}
    (h : E2E.Record.Serialization.CanonSession G s) :
    E2E.Record.Serialization.CanonSession (OverP2.clearPendingGhost G) (OverP2.clearPending s) := by
  obtain ⟨hl, hr, hs, hlen, hc, _hp⟩ := h
  exact ⟨hl, hr, hs, hlen, hc, trivial⟩

theorem encSessionMem_clearPending_eq {G : SessionGhost} {s : Session (List (BitVec 8))}
    (h : E2E.Record.Serialization.CanonSession G s) :
    E2E.Record.Serialization.encSessionMem
      (OverP2.clearPendingGhost G) (OverP2.clearPending s) =
      E2E.Record.encSession (OverP2.clearPending s) :=
  E2E.Record.Serialization.encSessionMem_eq_of_canon _ _ (canonSession_clearPending h)

theorem encSessionMem_clearPending_lt_32 {r : SessionRecord (List (BitVec 8))}
    {G : SessionGhost} {s : Session (List (BitVec 8))}
    (hIn : Slots.scopeIn r) (hcur : r.currentSession = some s)
    (hcanon : E2E.Record.Serialization.CanonSession G s) :
    (E2E.Record.Serialization.encSessionMem
      (OverP2.clearPendingGhost G) (OverP2.clearPending s)).length < 2 ^ 32 := by
  rw [encSessionMem_clearPending_eq hcanon]
  rcases r with ⟨curOpt⟩
  dsimp only at hcur
  subst hcur
  rcases hIn with ⟨⟨hin, hpq, hrepr⟩, s', hs', hss⟩
  injection hs' with hs_eq; subst hs_eq
  have hb_strip : E2E.RecordX.DeserializeScopeBounded
      ⟨some (Slots.PqValid.stripPq (OverP2.clearPending s))⟩ := by
    apply E2E.RecordX.deserializeScopeBounded_of_deserializeScopeP
    refine ⟨⟨?_, ?_, ?_⟩, Slots.PqValid.stripPq (OverP2.clearPending s), rfl, ?_⟩
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
      have hin0 := hin s rfl
      exact ⟨hin0.1, hin0.2.1, fun k hk => by simp [OverP2.clearPending, Slots.PqValid.stripPq] at hk⟩
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq; rfl
    · intro s1 hs1; injection hs1 with hs1_eq; subst hs1_eq
      obtain ⟨hr1, hr2, _hwf, hr4⟩ := hrepr s rfl
      exact ⟨hr1, hr2, rfl, hr4⟩
    · exact ⟨hss.1, fun p hp => by simp [OverP2.clearPending, Slots.PqValid.stripPq] at hp,
        fun k hk => by simp [OverP2.clearPending, Slots.PqValid.stripPq] at hk, hss.2.2.2⟩
  have h21 :
      (E2E.Record.encodeRecord
        ⟨some (Slots.PqValid.stripPq (OverP2.clearPending s))⟩).length < 2 ^ 21 :=
    E2E.RecordX.encodeRecord_length_lt_21_of_bounded hb_strip
  have hge :
      (E2E.Record.encSession
        (Slots.PqValid.stripPq (OverP2.clearPending s))).length ≤
        (E2E.Record.encodeRecord
          ⟨some (Slots.PqValid.stripPq (OverP2.clearPending s))⟩).length := by
    unfold E2E.Record.encodeRecord E2E.Record.msgField
    dsimp only [Option.map_some]
    exact E2E.RecordX.lenField_length_ge' 1
      (E2E.Record.encSession (Slots.PqValid.stripPq (OverP2.clearPending s)))
  have heq :
      (E2E.Record.encSession (OverP2.clearPending s)).length =
        (E2E.Record.encSession
          (Slots.PqValid.stripPq (OverP2.clearPending s))).length +
          (E2E.Record.bytesField 15
            (OverP2.clearPending s).state.pqRatchetState).length := by
    simp only [E2E.Record.encSession, Slots.PqValid.stripPq,
      show (E2E.Record.bytesField 15 []).length = 0 from rfl,
      List.length_append]
    omega
  have hb15 :
      (E2E.Record.bytesField 15
        (OverP2.clearPending s).state.pqRatchetState).length ≤
        (OverP2.clearPending s).state.pqRatchetState.length + 20 :=
    E2E.RecordX.bytesField_length_le' 15 (OverP2.clearPending s).state.pqRatchetState
  have hpq31 : (OverP2.clearPending s).state.pqRatchetState.length < 2 ^ 31 :=
    (hpq s rfl).2
  omega

/-! ## 3. Stack Budget Bound for `stageP2OverV1CallStack` -/

theorem stageP2OverV1CallStack_le_subStack {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost)
    (spkId kpkId opkIdWord : BitVec 32) (kbk : PublicKey) (B : RunBudgets) :
    Over.stageP2OverV1CallStack
      (cliPollSpkKit A b F0 spkId (cliKitStk B))
      (cliPollKpkKit A b F0 kpkId spkId kbk (cliKitStk B))
      (cliPollPkKit A b F0 opkIdWord (cliKitStk B))
      (cliPollSelfKit A b F0 peer (cliKitStk B)) ≤ dpClosSubStack B := by
  have hv1 := stageP2V1CallStack_le_subStack (A := A) b F0 peer spkId kpkId opkIdWord kbk B
  have hoverPure : Over.stageP2OverPureAndErrStack ≤ dpClosSubStack B := by
    have h0 : Over.stageP2OverPureAndErrStack ≤ 1048576 - 3280 := by decide
    exact Nat.le_trans h0 (Nat.le_add_right _ _)
  exact Nat.max_le.mpr ⟨hv1, hoverPure⟩

/-! ## 4. Spatial Entry Unpack & `+0x1778` Success-Exit Fold (`Path C` Over) -/

private theorem pull_pure_after1 {A1 Rest : SepProp} {φ : Prop} :
    A1 ∗ (⌜φ⌝ ∗ Rest) = ⌜φ⌝ ∗ (A1 ∗ Rest) := by
  ac_rfl

private theorem pull_pure_msg_group {M1 M2 M3 Tail : SepProp} {φ : Prop} :
    (M1 ∗ M2 ∗ (⌜φ⌝ ∗ M3)) ∗ Tail = ⌜φ⌝ ∗ ((M1 ∗ M2 ∗ M3) ∗ Tail) := by
  ac_rfl

private theorem pull_pure_after7 {A1 A2 A3 A4 A5 A6 A7 Rest : SepProp} {φ : Prop} :
    A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (A5 ∗ (A6 ∗ (A7 ∗ (⌜φ⌝ ∗ Rest))))))) =
      ⌜φ⌝ ∗ (A1 ∗ (A2 ∗ (A3 ∗ (A4 ∗ (A5 ∗ (A6 ∗ (A7 ∗ Rest))))))) := by
  ac_rfl

end OverP2Inst
end CryptoVerification.SignalSession.Cli.RunProofs.Poll
