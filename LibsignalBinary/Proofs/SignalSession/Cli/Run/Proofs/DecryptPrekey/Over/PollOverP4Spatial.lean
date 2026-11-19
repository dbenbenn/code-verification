/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Over.PollOverP4 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathA -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.ClosureOver
import LibsignalBinary.Proofs.E2E.RecordX.Length
import LibsignalBinary.Proofs.E2E.RecordX.LengthP
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosureExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathAP4Cont
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.ClosurePathB
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Top.StateSize
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.DecryptPrekey.Poll.AgreePathB
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP3a2
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# CLI Poll Overwrite-Path (`Path C`) Stage P4 Spatial and Record-Length Bridges

Proves the `< 2 ^ 32` serialized 2-session record length bound `pathC_recPrev1Ok_of_tryDecrypt`,
repacks the `Prev1` session-store kit and remaining five CLI store kits into `storesAt`, and proves
the `StageP3Prev1` → `StageP4Prev1` → `dpPollSpecState.post` spatial bridges.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Poll

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
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
open CryptoVerification.SignalSession.Cli.KitInst

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 1. Canonicality & 32-Bit Record-Length Bound (`pathC_recPrev1Ok_of_tryDecrypt`) -/

theorem canonSession_of_sessionStateAt_extraRel {A : RustAlloc} {ss : BitVec 64}
    {G : SessionGhost} {s : Session (List (BitVec 8))} {Rest : SepProp} {m : Memory}
    (hex : SessionExtraRel G s)
    (hm : m ⊨ sessionStateAt A ss G s.state ∗ Rest) :
    E2E.Record.Serialization.CanonSession G s := by
  have hm' : m ⊨ sessionStateReprAt A ss G s ∗ Rest := by
    refine Arm64.Satisfies.mono (sepConj_mono_left ?_) hm
    unfold sessionStateReprAt
    exact Entails.pure_right hex (Entails.refl _)
  exact E2E.InMem.SessionStoreImpl.canonSession_of_satisfies_sessionAt A ss G s m
    (ProofLib.Satisfies.of_sep_left hm')

private theorem spqrV1Init_length_lt_4096 (F : ShaCompress)
    (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    (dir : SpqrDirection) (k : BitVec 256) :
    (CryptoVerification.LibsignalSpqrV1.spqrV1Init F K dir k).length < 4096 := by
  unfold CryptoVerification.LibsignalSpqrV1.spqrV1Init
    CryptoVerification.LibsignalSpqrV1.spqrV1InitialStateFor
  split
  · rename_i st hst
    simp only [CryptoVerification.LibsignalSpqrV1.initialState,
      CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams] at hst
    rcases hi : CryptoVerification.LibsignalSpqrV1.initInner
        (CryptoVerification.LibsignalSpqrV1.spqrDeps F K)
        CryptoVerification.LibsignalSpqrV1.Version.v1
        (CryptoVerification.LibsignalSpqrV1.Direction.ofSpqrDirection dir)
        (CryptoGames.HMAC.keyToBytes32 k) with p | inner
    · rw [hi] at hst; cases hst
    · rw [hi] at hst
      have hst' := Except.ok.inj hst
      subst hst'
      have hin := CryptoVerification.SpqrV1.Top.StateSize.initInner_spqrDeps_raw_le hi
      have hk : (CryptoGames.HMAC.keyToBytes32 k).length = 32 := by
        simp [CryptoGames.HMAC.keyToBytes32]
      refine Nat.lt_of_le_of_lt
        (CryptoVerification.SpqrV1.Top.StateSize.encodeState_length_le_rawPqState _) ?_
      simp only [CryptoVerification.SpqrV1.Top.StateSize.rawPqState,
        CryptoVerification.LibsignalSpqrV1.pbToPqRatchetState,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_some,
        CryptoVerification.SpqrV1.Top.StateSize.optRaw_none,
        CryptoVerification.SpqrV1.Top.StateSize.rawVN, hk]
      omega
  · decide

set_option maxHeartbeats 800000 in
theorem pathC_recPrev1Ok_of_tryDecrypt {A : RustAlloc} {b : BitVec 64} {W : PEParams}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer me : AddrGhost} {σ : DpKitStk}
    {pm : PreKeySignalMessage} {coins : List (BitVec 8)}
    {s_old : Session (List (BitVec 8))}
    {m : PreKeyMessageFields} {k : ResponderPreKeySecrets} {kp : RecordCodecs.IdentityKeyPair} {reg : BitVec 32}
    {dk : SignalPqxdh.DRKey} {pt : List (BitVec 8)}
    {G' : SessionGhost} {ss : BitVec 64} {Rest : SepProp} {mem : Memory}
    (hs_old : Slots.scopeIn ⟨some s_old⟩)
    (hd : DecPkOkD2c W Scope F peer.val me.val pm)
    (hver : (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk).version =
      pm.message.messageVersion.zeroExtend 32)
    (hok : (genP3S5Model W.C W.Q.K peer me pm.message coins
      (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).1 = .ok pt)
    (hex' : SessionExtraRel G'
      { pathAInitSession W ⟨kp.privateKey.bytes, reg⟩ k m dk with
        state := (genP3S5Model W.C W.Q.K peer me pm.message coins
          (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).2
        pendingPreKey := none
        pendingKyberPreKey := none })
    (hmem : mem ⊨ sessionStateAt A ss G'
      (genP3S5Model W.C W.Q.K peer me pm.message coins
        (pathAInitState W ⟨kp.privateKey.bytes, reg⟩ k m dk)).2 ∗ Rest) :
    let meE : LocalIdentity := ⟨kp.privateKey.bytes, reg⟩
    let st' := (genP3S5Model W.C W.Q.K peer me pm.message coins (pathAInitState W meE k m dk)).2
    let ses' : Session (List (BitVec 8)) :=
      { pathAInitSession W meE k m dk with
        state := st', pendingPreKey := none, pendingKyberPreKey := none }
    (cliPollStorePrev1Ops (A := A) (b := b) (F0 := F) (peer := peer) (σ := σ)).RecPrev1Ok
      G' ses' (E2E.Record.encSession (Over.clearPending s_old)) := by
  intro meE st' ses'
  change E2E.Record.Serialization.CanonSession G' ses' ∧
    (Over.encodeRecordPrev1 ses' (E2E.Record.encSession (Over.clearPending s_old))).length < 2 ^ 32
  have hd0 := hd.toDecPkOk₀_emptyScope
  let st0 := pathAInitState W meE k m dk
  refine ⟨canonSession_of_sessionStateAt_extraRel hex' hmem, ?_⟩
  have hok_pair : genP3S5Model W.C W.Q.K peer me pm.message coins st0 = (.ok pt, st') := by
    rcases hg : genP3S5Model W.C W.Q.K peer me pm.message coins st0 with ⟨r1, r2⟩
    have hr1 : r1 = .ok pt := by rw [hg] at hok; exact hok
    subst hr1
    have hr2 : r2 = st' := by dsimp only [st', st0]; rw [hg]
    subst hr2
    rfl
  have htry : SessionState.tryDecryptFromRecord W.C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) st0 = (.ok pt, st') := by
    change SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W) _ _ _ _ _ = _
    rw [tryDecryptFromRecord_preKey_ver_eq hd0 hver, hok_pair]
  have hIn0 := (pathAInitSession_scopeIn W meE k m dk).1
  obtain ⟨⟨hInP0, _hPq0, _hRep0⟩, ses₀, hCur₀, ⟨hRC0, _, _, _⟩⟩ := hIn0
  injection hCur₀ with hses₀; subst hses₀
  obtain ⟨hSeeds0, _, _⟩ := hInP0 (pathAInitSession W meE k m dk) rfl
  obtain ⟨_hSeeds', _hRC', _, _, key, hRecv⟩ :=
    CryptoVerification.E2E.V1.tryDecryptFromRecord_ok_props_gen W.C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 W.C.F W.Q.K).spqr
      ((pqxdhSessionParams W).expectedAddrs (initParty peer.val))
      pm.message .preKey (pkRecvCoins coins) st0 st' pt hSeeds0 hRC0 htry
  have hVal0 : CryptoVerification.SpqrV1.Top.StateSize.ValidState st0.pqRatchetState :=
    (spqrV1Init_pqInV1 W.C.F W.Q.K .b2a (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))).1
  have hLen0 : st0.pqRatchetState.length < 4096 :=
    spqrV1Init_length_lt_4096 W.C.F W.Q.K .b2a (CryptoGames.HKDF.bytesToKey32 (ofU8 dk.pqrKey))
  have hPqGrow :=
    (CryptoVerification.SpqrV1.Top.StateSize.spqrV1_recv_validState_length_le
      W.C.F W.Q.K st0.pqRatchetState pm.message.pqRatchet st'.pqRatchetState key
      hVal0 (by omega) hRecv).2
  obtain ⟨hKit', _⟩ := pathA_recOk_of_tryDecrypt hd0 hver hok
  have hb_strip : E2E.RecordX.DeserializeScopeBounded
      ⟨some (Slots.PqValid.stripPq ses')⟩ := by
    apply E2E.RecordX.deserializeScopeBounded_of_deserializeScopeP
    rcases hKit' with ⟨⟨hin, _hpq, hrepr⟩, s1, hs1, hss⟩
    injection hs1 with hs1_eq; subst hs1_eq
    refine ⟨⟨?_, ?_, ?_⟩, Slots.PqValid.stripPq ses', rfl, ?_⟩
    · intro s2 hs2; injection hs2 with hs2_eq; subst hs2_eq
      have hin0 := hin ses' rfl
      exact ⟨hin0.1, hin0.2.1, fun k1 hk1 => by simp [ses', Slots.PqValid.stripPq] at hk1⟩
    · intro s2 hs2; injection hs2 with hs2_eq; subst hs2_eq; rfl
    · intro s2 hs2; injection hs2 with hs2_eq; subst hs2_eq
      obtain ⟨hr1, hr2, hwf, hr4⟩ := hrepr ses' rfl
      exact ⟨hr1, hr2, hwf, hr4⟩
    · exact ⟨hss.1, fun p hp => by simp [ses', Slots.PqValid.stripPq] at hp,
        fun k1 hk1 => by simp [ses', Slots.PqValid.stripPq] at hk1, hss.2.2.2⟩
  have h21 :
      (E2E.Record.encodeRecord ⟨some (Slots.PqValid.stripPq ses')⟩).length < 2 ^ 21 :=
    E2E.RecordX.encodeRecord_length_lt_21_of_bounded hb_strip
  have hge :
      (E2E.Record.encSession (Slots.PqValid.stripPq ses')).length ≤
        (E2E.Record.encodeRecord ⟨some (Slots.PqValid.stripPq ses')⟩).length := by
    unfold E2E.Record.encodeRecord E2E.Record.msgField
    dsimp only [Option.map_some]
    exact E2E.RecordX.lenField_length_ge' 1 (E2E.Record.encSession (Slots.PqValid.stripPq ses'))
  have heq :
      (E2E.Record.encSession ses').length =
        (E2E.Record.encSession (Slots.PqValid.stripPq ses')).length +
          (E2E.Record.bytesField 15 ses'.state.pqRatchetState).length := by
    simp only [E2E.Record.encSession, Slots.PqValid.stripPq,
      show (E2E.Record.bytesField 15 []).length = 0 from rfl,
      List.length_append]
    omega
  have hb15 :
      (E2E.Record.bytesField 15 ses'.state.pqRatchetState).length ≤
        ses'.state.pqRatchetState.length + 20 :=
    E2E.RecordX.bytesField_length_le' 15 ses'.state.pqRatchetState
  have hlf1 :
      (E2E.Record.lenField 1 (E2E.Record.encSession ses')).length ≤
        (E2E.Record.encSession ses').length + 20 :=
    E2E.RecordX.lenField_length_le' 1 (E2E.Record.encSession ses')
  have hlf2 := Over.lenField2_clearPending_length_lt hs_old
  have hst'_len : ses'.state.pqRatchetState.length = st'.pqRatchetState.length := rfl
  unfold Over.encodeRecordPrev1 E2E.Record.encodeRecord E2E.Record.msgField
  dsimp only [Option.map_some]
  rw [List.length_append]
  omega

/-! ## 2. Spatial Bridges (`StageP3Prev1` Ok → `stageP4Prev1Pre` → `dpPollSpecState.post`) -/

private theorem add_0x78_0x28 (a : BitVec 64) : (a + 0x78#64) + 0x28#64 = a + 0xa0#64 := by
  rw [BitVec.add_assoc]; rfl

theorem cliPollPrev1StoresKitsAt_entails_storesAt {A : RustAlloc} (b : BitVec 64)
    (F0 : FsFiles) (peer : AddrGhost) (pid spkId kpkId : BitVec 32) (kbk : PublicKey)
    (σ : DpKitStk) (ptr : BitVec 64) (g : StoresGhost) :
    (cliPollSessPrev1Kit A b F0 peer σ).storeAt (ptr + 0xf0#64) g.sessions ∗
    (cliPollIdKit A b F0 peer σ).identityAt ptr g.identity ∗
    (cliPollPkKit A b F0 pid σ).storeAt (ptr + 0xc8#64) g.oneTime ∗
    (cliPollSpkKit A b F0 spkId σ).storeAt (ptr + 0x50#64) g.signed ∗
    (cliPollKpkKit A b F0 kpkId spkId kbk σ).storeAt (ptr + 0x78#64) g.kyber ∗
    dirAt A (ptr + 0x118#64) g.pub ⊢
    storesAt A ptr g := by
  unfold storesAt
  dsimp only [cliPollSessPrev1Kit, cliSessPrev1StoreAt, cliPollIdKit, cliPollPkKit, cliPollSpkKit,
    cliPollKpkKit, cliIdStoreSpecFull, cliPreKeyStoreSpec, cliSignedPreKeyStoreSpec,
    cliKpkStoreSpecFull, cliIdStoreAtFull, cliIdStoreAt, cliPkStoreAt,
    cliSpkStoreAt, cliKpkStoreAtFull]
  rw [add_0x78_0x28 ptr]
  have drop1 (P : Prop) (Q : SepProp) : ⌜P⌝ ∗ Q ⊢ Q := Entails.pure_left fun _ => Entails.refl _
  have drop2 (P1 P2 : Prop) (Q : SepProp) : ⌜P1⌝ ∗ (⌜P2⌝ ∗ Q) ⊢ Q :=
    Entails.pure_left fun _ => drop1 P2 Q
  refine Entails.trans
    (sepConj_mono (drop1 _ _)
      (sepConj_mono (drop2 _ _ _)
        (sepConj_mono (drop1 _ _)
          (sepConj_mono (drop1 _ _)
            (sepConj_mono (drop1 _ _) (Entails.refl _)))))) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SignalSession.Cli.RunProofs.Poll
