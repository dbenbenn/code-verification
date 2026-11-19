/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.LoadRec -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.ScopeIn -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordMin.Deserialize -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOk -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionKitOk -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.FsTraced -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Epochs
import LibsignalBinary.Proofs.E2E.HooksE.TripleRatchetHooksCommon
import LibsignalBinary.Proofs.E2E.V1.ReachSteps
import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.B3DeserQ
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityKitOkCli -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Glue.BcmpHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSat
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.TrapBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Store.SerGlueX
import LibsignalBinary.Proofs.TripleRatchet.Glue
import LibsignalBinary.Proofs.TripleRatchet.Hooks
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsX -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# CLI Store Kit Answer Determinism, Record Scope Preservation, and Trap-Program Kit Glue

Proves functional answer relations for the CLI session and identity store kits (`cliSessLoadRel_eq`,
`cliSessStoreRel_eq`, `cliIdTrustRel_eq`, `cliIdSaveRel_eq`), `scopeKit` projections, record scope
and `< 2^32` encoded-length preservation across SPQR V1 decrypt/encrypt steps (`decryptRecord_recOk_of_scopeIn`,
`storedRecord_recOk_of_scopeIn`, `cliDecModelRecOkAt_opened`, `cliEncRecOk_opened`), and session and
identity kit contract bundles on `cliExterns W`, `trTrapExterns W.C (cliExterns W)`, and
`cliExternsWith ext`.
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Slots

open Arm64 ProofLib ProofLib.Variant SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.KitInst
open CryptoVerification.SignalSession.Cli.KitInst.SessKit
open CryptoVerification.SignalSession.Cli.KitInst.IdKit
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

/-! ## 1. Functional answer relations of the CLI store kits -/

/-- `loadRel` is functional for any `DirGhost` whenever `encodeRecord` is injective on `Scope`. -/
theorem cliSessLoadRel_eq {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {d : DirGhost} {rem : AddrVal}
    {ans₁ ans₂ : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (hinj : ∀ ⦃r₁ r₂⦄, Scope r₁ → Scope r₂ →
      E2E.Record.encodeRecord r₁ = E2E.Record.encodeRecord r₂ → r₁ = r₂)
    (h₁ : (cliSessionStoreSpec A b rd F pathOk Scope peer s1 s2 s3 s4).loadRel d rem ans₁)
    (h₂ : (cliSessionStoreSpec A b rd F pathOk Scope peer s1 s2 s3 s4).loadRel d rem ans₂) :
    ans₁ = ans₂ := by
  obtain ⟨bs₁, hg₁, ha₁⟩ := h₁
  obtain ⟨bs₂, hg₂, ha₂⟩ := h₂
  rw [hg₁] at hg₂
  injection hg₂ with hbs
  subst hbs
  cases bs₁ with
  | nil =>
    exact ha₁.trans ha₂.symm
  | cons x xs =>
    obtain ⟨r₁, hr₁, he₁, hs₁⟩ := ha₁
    obtain ⟨r₂, hr₂, he₂, hs₂⟩ := ha₂
    have hreq : r₁ = r₂ := hinj hs₁ hs₂ (he₁.trans he₂.symm)
    subst hreq
    exact hr₁.trans hr₂.symm

/-- Specialization of `cliSessLoadRel_eq` at `StoresGhost.opened.sessions`. -/
theorem cliSessLoadRel_opened_eq {A : RustAlloc} {b : BitVec 64}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {ans₁ ans₂ : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (hinj : ∀ ⦃r₁ r₂⦄, Scope r₁ → Scope r₂ →
      E2E.Record.encodeRecord r₁ = E2E.Record.encodeRecord r₂ → r₁ = r₂)
    (_hok : FilesOkPeer Scope F peer.val)
    (h₁ : (cliSessionStoreSpec A b cliIo.rd F pathOk Scope peer s1 s2 s3 s4).loadRel
      StoresGhost.opened.sessions peer.val ans₁)
    (h₂ : (cliSessionStoreSpec A b cliIo.rd F pathOk Scope peer s1 s2 s3 s4).loadRel
      StoresGhost.opened.sessions peer.val ans₂) :
    ans₁ = ans₂ :=
  cliSessLoadRel_eq hinj h₁ h₂

theorem cliSessLoadRel_eq_loadRec {A : RustAlloc} {b : BitVec 64}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrGhost} {rem : AddrVal} {s1 s2 s3 s4 : Nat}
    {ans : Except Unit (Option (SessionRecord (List (BitVec 8))))}
    (hinj : EncodeInjOn Scope)
    (h : (cliSessionStoreSpec A b cliIo.rd F pathOk Scope peer s1 s2 s3 s4).loadRel
      StoresGhost.opened.sessions rem ans) :
    ans = loadRec Scope F rem := by
  obtain ⟨bs, hget, hans⟩ := h
  exact loadRec_unique hinj (hget ▸ hans)

/-- On a well-formed peer file (`FilesOkPeer Scope₁ F peer`), enlarging `Scope₁` to `Scope₂` with `EncodeInjOn Scope₂` leaves `loadRec` unchanged. -/
theorem loadRec_of_sub {Scope₁ Scope₂ : SessionRecord (List (BitVec 8)) → Prop}
    {F : FsFiles} {peer : AddrVal}
    (hinj₂ : EncodeInjOn Scope₂)
    (hsub : ∀ r, Scope₁ r → Scope₂ r)
    (hok : FilesOkPeer Scope₁ F peer) :
    loadRec Scope₁ F peer = loadRec Scope₂ F peer := by
  have hans₁ : SessLoadAns Scope₁ (StoresGhost.opened.sessions.get cliIo.rd F (addressText peer))
      (loadRec Scope₁ F peer) := sessLoadAns_loadRec hok
  have hans₂ : SessLoadAns Scope₂ (StoresGhost.opened.sessions.get cliIo.rd F (addressText peer))
      (loadRec Scope₁ F peer) := by
    rcases hget : StoresGhost.opened.sessions.get cliIo.rd F (addressText peer) with _ | bs
    · rw [hget] at hans₁; exact hans₁
    · cases bs with
      | nil => rw [hget] at hans₁; exact hans₁
      | cons b bs' =>
        rw [hget] at hans₁
        obtain ⟨r, hr, henc, hsc⟩ := hans₁
        exact ⟨r, hr, henc, hsub r hsc⟩
  exact loadRec_unique hinj₂ hans₂

theorem cliSessStoreRel_eq {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {d : DirGhost} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))} {ans₁ ans₂ : Except Unit Unit}
    (h₁ : (cliSessionStoreSpec A b rd F pathOk Scope peer s1 s2 s3 s4).storeRel d rem r ans₁)
    (h₂ : (cliSessionStoreSpec A b rd F pathOk Scope peer s1 s2 s3 s4).storeRel d rem r ans₂) :
    ans₁ = ans₂ :=
  h₁.trans h₂.symm

theorem cliIdTrustRel_eq {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {g : IdGhost} {rem : AddrVal} {k : IdentityKey} {dir : Direction}
    {ans₁ ans₂ : Except Unit Bool}
    (h₁ : (cliIdentityStoreSpec A b rd F pathOk peer s1 s2 s3 s4).trustRel g rem k dir ans₁)
    (h₂ : (cliIdentityStoreSpec A b rd F pathOk peer s1 s2 s3 s4).trustRel g rem k dir ans₂) :
    ans₁ = ans₂ := by
  obtain ⟨t₁, ht₁, ha₁⟩ := h₁
  obtain ⟨t₂, ht₂, ha₂⟩ := h₂
  rw [ht₁] at ht₂
  injection ht₂ with ht
  subst ht
  exact ha₁.trans ha₂.symm

theorem cliIdSaveRel_eq {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {g : IdGhost} {rem : AddrVal} {k : IdentityKey}
    {ans₁ ans₂ : Except Unit IdentityChange}
    (h₁ : (cliIdentityStoreSpec A b rd F pathOk peer s1 s2 s3 s4).saveRel g rem k ans₁)
    (h₂ : (cliIdentityStoreSpec A b rd F pathOk peer s1 s2 s3 s4).saveRel g rem k ans₂) :
    ans₁ = ans₂ := by
  obtain ⟨c₁, hc₁, ha₁⟩ := h₁
  obtain ⟨c₂, hc₂, ha₂⟩ := h₂
  rw [hc₁] at hc₂
  injection hc₂ with hc
  subst hc
  exact ha₁.trans ha₂.symm

/-! ## 2. Scope projections from `Slots.scopeKit` -/

theorem scopeKit_recordInScopeP {r : SessionRecord (List (BitVec 8))} (h : scopeKit r) :
    CryptoVerification.E2E.RecordX.RecordInScopeP r :=
  h.1.1

theorem scopeKit_recordInScopeEnc {r : SessionRecord (List (BitVec 8))} (h : scopeKit r) :
    MessageEncrypt.RecordInScopeEnc r := by
  intro s hs
  obtain ⟨hseeds, hrc, hky⟩ := h.1.1 s hs
  exact ⟨trivial, hseeds, hrc, hky⟩

theorem scopeKit_pqrState_lt {r : SessionRecord (List (BitVec 8))} (h : scopeKit r)
    (s : Session (List (BitVec 8))) (hs : r.currentSession = some s) :
    s.state.pqRatchetState.length < 2 ^ 32 :=
  h.1.2.1 s hs

/-! ## 3. Opened-store scope pinning and record bounds -/

/-- At `StoresGhost.opened.sessions`, any record in `ScopeAt scopeKit` on a well-formed peer file
(`FilesOkPeer Scope₀ F0 peer.val`, `Scope₀ ⊆ scopeIn`) lies in `Scope₀` and hence in `scopeIn`. -/
theorem cliSess_scopeIn_of_opened {A : RustAlloc} {b : BitVec 64}
    {pathOk : List (BitVec 8) → Prop} {Scope₀ : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {peer : AddrGhost} {s1 s2 s3 s4 : Nat} {rem : AddrVal}
    {r : SessionRecord (List (BitVec 8))}
    (hsub : ∀ r', Scope₀ r' → scopeIn r')
    (hok : FilesOkPeer Scope₀ F0 peer.val)
    (haddr : (cliSessionStoreSpec A b cliIo.rd F0 pathOk scopeKit peer s1 s2 s3 s4).addrOk rem)
    (hsc : (cliSessionStoreSpec A b cliIo.rd F0 pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
      scopeKit StoresGhost.opened.sessions rem r) :
    Scope₀ r ∧ scopeIn r := by
  have hrem : rem = peer.val := haddr
  subst hrem
  obtain ⟨hkit, bs, hget, hans⟩ := hsc
  obtain ⟨bs₀, hget₀, hwf⟩ := hok.sessGet
  rw [hget] at hget₀
  injection hget₀ with hbs
  subst hbs
  cases bs with
  | nil => cases hans
  | cons b₀ bs' =>
    obtain ⟨r', hr', henc, _⟩ := hans
    injection hr' with hr'
    injection hr' with hr'
    subst hr'
    rcases hwf with hnil | ⟨r₀, henc₀, hsc₀⟩
    · cases hnil
    · have hkit₀ : scopeKit r₀ := scopeKit_of_scopeIn (hsub r₀ hsc₀)
      have heq : r = r₀ :=
        encodeInjOn_deserializeScopeP_Q r r₀ hkit hkit₀ (henc.trans henc₀.symm)
      subst heq
      exact ⟨hsc₀, hsub r hsc₀⟩

private theorem stripPq_bounded_of_parts {s : Session (List (BitVec 8))}
    (hseeds : SeedsLen32 s.state)
    (hrc : s.state.receiverChains.length ≤ maxReceiverChains)
    (hrep : CryptoVerification.E2E.Reach.SessRepr s.state)
    (hwf : s.Wf)
    (hp : ∀ p, s.pendingPreKey = some p → p.timestamp = 0)
    (hk : ∀ k, s.pendingKyberPreKey = some k → k.ciphertext.length = 1569)
    (ha : s.aliceBaseKey = [] ∨ s.aliceBaseKey.length = 33) :
    CryptoVerification.E2E.RecordX.DeserializeScopeBounded ⟨some (PqValid.stripPq s)⟩ := by
  have hscP : CryptoVerification.E2E.RecordX.SessionScopeP (PqValid.stripPq s) := by
    refine ⟨hrc, hp, hk, ha⟩
  refine ⟨⟨?_, ?_, ?_⟩, PqValid.stripPq s, rfl,
    CryptoVerification.E2E.RecordX.sessionScopeBounded_of_sessionScopeP hscP⟩
  · intro t ht
    injection ht with ht; subst ht
    refine ⟨hseeds, Nat.lt_of_le_of_lt hrc (by decide), fun k hk' => ?_⟩
    rw [hk k hk']; decide
  · intro t ht
    injection ht with ht; subst ht
    rfl
  · intro t ht
    injection ht with ht; subst ht
    refine ⟨hrep.1, hrep.2, hwf, ?_⟩
    dsimp only [PqValid.stripPq]
    rcases ha with ha | ha <;> rw [ha] <;> decide

/-- A successful `decryptRecord` step at `spqrV1 C.F K` maps any `scopeIn` record to a `scopeKit`
record whose canonical encoding has length `< 2^32`. -/
theorem decryptRecord_recOk_of_scopeIn {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    {parse : UuidParser} {x : DecryptGhost}
    {rec rec' : SessionRecord (List (BitVec 8))} {pt : List (BitVec 8)}
    (hIn : scopeIn rec)
    (hDec : MessageDecrypt.decryptRecord C (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K)
      parse x rec = .ok (pt, rec')) :
    scopeKit rec' ∧ (E2E.Record.encodeRecord rec').length < 2 ^ 32 := by
  obtain ⟨⟨hInP, hPqIn, hRep⟩, ses, hCur, hSessSc⟩ := hIn
  unfold MessageDecrypt.decryptRecord SessionRecord.tryDecryptFromRecord at hDec
  rw [hCur] at hDec
  dsimp only at hDec
  rcases hTry : SessionState.tryDecryptFromRecord C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr
      (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val)
      x.msg .whisper (coinsOf x.rest) ses.state with ⟨e | ptext, st'⟩
  · rw [hTry] at hDec; cases hDec
  · rw [hTry] at hDec
    simp only [Except.ok.injEq, Prod.mk.injEq] at hDec
    rcases hDec with ⟨rfl, rfl⟩
    obtain ⟨hSeeds, _, _⟩ := hInP ses hCur
    have hPqSes : PqValid.PqInV1 ses.state.pqRatchetState := hPqIn ses hCur
    obtain ⟨hRep1, hRep2, _, _⟩ := hRep ses hCur
    obtain ⟨hRC, _, _, hAbk⟩ := hSessSc
    obtain ⟨hSeeds', hRC', _, _, key, hRecv⟩ :=
      CryptoVerification.E2E.V1.tryDecryptFromRecord_ok_props_gen C
        (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr
        (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val)
        x.msg .whisper (coinsOf x.rest) ses.state st' ptext hSeeds hRC hTry
    have hRep' : CryptoVerification.E2E.Reach.SessRepr st' :=
      CryptoVerification.E2E.V1.sessRepr_tryDecryptFromRecord_gen C
        (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr
        (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val)
        x.msg .whisper (coinsOf x.rest) ses.state st' ptext ⟨hRep1, hRep2⟩ hTry
    have hPqOut : PqValid.PqOutV1 st'.pqRatchetState :=
      (PqValid.pqStep_spqrV1 C.F K).recv ses.state.pqRatchetState x.msg.pqRatchet
        st'.pqRatchetState key hPqSes hRecv
    have hPqLt : st'.pqRatchetState.length < 2 ^ 32 :=
      (PqValid.pqStep_spqrV1 C.F K).out_bound st'.pqRatchetState hPqOut
    have hPendFalse : st'.pendingPreKey = false := by
      unfold SessionState.tryDecryptFromRecord at hTry
      split_ifs at hTry
      · simp at hTry
      · rcases hd : Mut.exec (SessionState.tryDecryptWithState C
            (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr
            (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val)
            x.msg .whisper (coinsOf x.rest)) ses.state with ⟨e | ptext', updated⟩
        · simp [hd] at hTry
        · rw [hd] at hTry
          simp only [Prod.mk.injEq] at hTry
          rcases hTry with ⟨_, rfl⟩
          unfold SessionState.tryDecryptWithState TripleRatchet.fromSessionState
            SessionState.takeRatchetState SessionState.takePqRatchetState at hd
          rcases hrem : ses.state.remoteIdentity with _ | remote
          · simp [hrem, CryptoVerification.E2E.Epochs.exec_bind,
              CryptoVerification.E2E.Epochs.exec_modifyGet,
              CryptoVerification.E2E.Epochs.exec_get,
              CryptoVerification.E2E.Epochs.exec_throw] at hd
          · simp only [hrem, CryptoVerification.E2E.Epochs.exec_bind,
              CryptoVerification.E2E.Epochs.exec_modifyGet,
              CryptoVerification.E2E.Epochs.exec_get,
              CryptoVerification.E2E.Epochs.exec_pure] at hd
            rcases hdec : Mut.exec (TripleRatchet.decrypt C
                (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr
                (serializeAddrVals (serviceIdParse parse) x.rem.val x.loc.val)
                x.msg .whisper (coinsOf x.rest))
                ⟨⟨ses.state.rootKey, ses.state.senderChain, ses.state.receiverChains,
                  ses.state.previousCounter, maxForwardJumps⟩,
                  ses.state.pqRatchetState, ses.state.localIdentity, remote⟩ with ⟨e | pt', tr'⟩
            · rw [hdec] at hd
              simp [CryptoVerification.E2E.Epochs.exec_liftE] at hd
            · rw [hdec] at hd
              simp only [CryptoVerification.E2E.Epochs.exec_liftE,
                CryptoVerification.E2E.Epochs.exec_modify,
                Prod.mk.injEq, Except.ok.injEq] at hd
              rcases hd with ⟨_, rfl⟩
              rfl
    let ses' : Session (List (BitVec 8)) :=
      { ses with state := st', pendingPreKey := none, pendingKyberPreKey := none }
    have hWf' : ses'.Wf := by
      unfold Session.Wf
      dsimp only [ses']
      exact hPendFalse
    have hPendTs' : ∀ p, ses'.pendingPreKey = some p → p.timestamp = 0 := by
      intro _ hp; cases hp
    have hKyber' : ∀ k, ses'.pendingKyberPreKey = some k → k.ciphertext.length = 1569 := by
      intro _ hk; cases hk
    have hScP' : CryptoVerification.E2E.RecordX.SessionScopeP ses' :=
      ⟨hRC', hPendTs', hKyber', hAbk⟩
    have hKit' : scopeKit ⟨some ses'⟩ := by
      refine ⟨⟨?_, ?_, ?_⟩, ses', rfl, hScP'⟩
      · intro s hs; injection hs with hs; subst hs
        exact ⟨hSeeds', Nat.lt_of_le_of_lt hRC' (by decide), fun _ hk => by cases hk⟩
      · intro s hs; injection hs with hs; subst hs
        exact hPqLt
      · intro s hs; injection hs with hs; subst hs
        refine ⟨hRep'.1, hRep'.2, hWf', ?_⟩
        dsimp only [ses']
        rcases hAbk with ha | ha <;> rw [ha] <;> decide
    have hBdd' : CryptoVerification.E2E.RecordX.DeserializeScopeBounded
        ⟨some (PqValid.stripPq ses')⟩ :=
      stripPq_bounded_of_parts hSeeds' hRC' hRep' hWf' hPendTs' hKyber' hAbk
    exact ⟨hKit', PqValid.encodeRecord_length_lt_32_of_stripPq_bounded hBdd' hPqOut⟩

private theorem messageEncrypt_of_from_encrypt {C : Crypto} {codec : SignalMessageProtoCodec}
    {S : Spqr (List (BitVec 8)) (List (BitVec 8))}
    {addrs : Option (List (BitVec 8))} {ptext coins : List (BitVec 8)}
    {st taken : SessionState (List (BitVec 8))}
    {otr otr' : OutgoingTripleRatchet (List (BitVec 8))} {sm : SignalMessage}
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState st = .ok (otr, taken))
    (henc : execOk (OutgoingTripleRatchet.encrypt C codec S ptext
        (st.encryptAddresses addrs) coins) otr = .ok (sm, otr')) :
    SessionState.messageEncrypt C codec S addrs ptext coins st =
      (.ok sm, otr'.applyToSessionState taken) := by
  unfold SessionState.messageEncrypt
  unfold execOk at hfrom henc
  rcases hf : Mut.exec OutgoingTripleRatchet.fromSessionState st with ⟨e | otr₀, taken₀⟩
  · rw [hf] at hfrom; cases hfrom
  · rw [hf] at hfrom
    injection hfrom with hfrom
    injection hfrom with hotr htak
    subst hotr htak
    dsimp only
    rcases he : Mut.exec (OutgoingTripleRatchet.encrypt C codec S ptext
        (st.encryptAddresses addrs) coins) otr₀ with ⟨e | sm₀, otr₁⟩
    · rw [he] at henc; cases henc
    · rw [he] at henc
      injection henc with henc
      injection henc with hsm hotr'
      subst hsm hotr'
      rfl

set_option linter.unusedSimpArgs false in
private theorem fromSessionState_pendingPreKey {s taken : SessionState (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))}
    (h : execOk OutgoingTripleRatchet.fromSessionState s = .ok (otr, taken)) :
    taken.pendingPreKey = s.pendingPreKey := by
  unfold execOk Mut.exec OutgoingTripleRatchet.fromSessionState
    SessionState.takePqRatchetState at h
  rcases hs : s.senderChain with _ | sc <;> rcases hr : s.remoteIdentity with _ | rk <;>
    simp only [hs, hr, modifyGet, MonadStateOf.modifyGet, ExceptT.run, StateT.run, bind,
      ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.bindCont, StateT.bind, Pure.pure,
      ExceptT.pure, StateT.pure, StateT.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM,
      monadLift, MonadLift.monadLift, MonadLiftT.monadLift, StateT.map, Functor.map, get, getThe,
      MonadStateOf.get, StateT.get, reduceCtorEq] at h
  all_goals (try split_ifs at h) <;>
    simp only [ExceptT.bindCont, StateT.bind, StateT.pure, Pure.pure, bind, reduceCtorEq,
      Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2 ▸ rfl

/-- A successful `StepsThroughEncrypt` step at `spqrV1 C.F K` from a `scopeIn` record produces a
`storedRecord` in `scopeKit` whose canonical encoding has length `< 2^32`. -/
theorem storedRecord_recOk_of_scopeIn {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem}
    {parse : UuidParser} {x : MessageEncrypt.WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr otr' : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    (hStep : MessageEncrypt.StepsThroughEncrypt scopeIn C
      (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K) parse x r sess otr taken k m otr') :
    scopeKit (MessageEncrypt.storedRecord sess otr' taken) ∧
      (E2E.Record.encodeRecord (MessageEncrypt.storedRecord sess otr' taken)).length < 2 ^ 32 := by
  obtain ⟨hCur, hIn, hFrom, _, hEncStep⟩ := hStep
  obtain ⟨⟨hInP, hPqIn, hRep⟩, ses₀, hCur₀, hSessSc⟩ := hIn
  rw [hCur] at hCur₀; injection hCur₀ with hses; subst hses
  obtain ⟨hSeeds, _, _⟩ := hInP sess hCur
  have hPqSes : PqValid.PqInV1 sess.state.pqRatchetState := hPqIn sess hCur
  obtain ⟨hRep1, hRep2, hWf, hAbk32⟩ := hRep sess hCur
  obtain ⟨hRC, hPendTs, hKyber, hAbk⟩ := hSessSc
  let addrs := serializeAddrVals (serviceIdParse parse) x.loc.val x.rem.val
  have hExEnc : ∃ sm,
      execOk (OutgoingTripleRatchet.encrypt C protoSignalCodec
        (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr x.ptext
        (sess.state.encryptAddresses addrs) x.rest) otr = .ok (sm, otr') := by
    unfold MessageEncrypt.EncEncryptStep at hEncStep
    cases hp : sess.pendingPreKey with
    | none =>
      rw [hp] at hEncStep
      obtain ⟨sm, henc, _⟩ := hEncStep
      have hpf : sess.state.pendingPreKey = false := by
        unfold Session.Wf at hWf; rw [hWf, hp]; rfl
      have hea : sess.state.encryptAddresses addrs = none := by
        simp [SessionState.encryptAddresses, hpf]
      rw [hea]
      exact ⟨sm, henc⟩
    | some items =>
      rw [hp] at hEncStep
      obtain ⟨_, _, sm, _, _, _, henc, _⟩ := hEncStep
      have hpt : sess.state.pendingPreKey = true := by
        unfold Session.Wf at hWf; rw [hWf, hp]; rfl
      have hea : sess.state.encryptAddresses addrs = addrs := by
        simp [SessionState.encryptAddresses, hpt]
      rw [hea]
      exact ⟨sm, henc⟩
  obtain ⟨sm, hEnc⟩ := hExEnc
  have hMsgEnc := messageEncrypt_of_from_encrypt hFrom hEnc
  let st' := otr'.applyToSessionState taken
  obtain ⟨hSeeds', hRC', _, _, key, pm, hSend, _⟩ :=
    CryptoVerification.E2E.V1.messageEncrypt_ok_props_gen C protoSignalCodec
      (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr addrs x.ptext x.rest
      sess.state st' sm hSeeds hRC hMsgEnc
  have hRep' : CryptoVerification.E2E.Reach.SessRepr st' :=
    CryptoVerification.E2E.V1.sessRepr_messageEncrypt_gen C protoSignalCodec
      (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K).spqr addrs x.ptext x.rest
      sess.state st' sm ⟨hRep1, hRep2⟩ hMsgEnc
  have hPqOut : PqValid.PqOutV1 st'.pqRatchetState :=
    (PqValid.pqStep_spqrV1 C.F K).send sess.state.pqRatchetState x.rest st'.pqRatchetState
      key pm hPqSes hSend
  have hPqLt : st'.pqRatchetState.length < 2 ^ 32 :=
    (PqValid.pqStep_spqrV1 C.F K).out_bound st'.pqRatchetState hPqOut
  have hPendEq : st'.pendingPreKey = sess.state.pendingPreKey := by
    simpa [st', OutgoingTripleRatchet.applyToSessionState] using
      fromSessionState_pendingPreKey hFrom
  let ses' : Session (List (BitVec 8)) := { sess with state := st' }
  have hWf' : ses'.Wf := by
    unfold Session.Wf at hWf ⊢
    dsimp only [ses']
    exact hPendEq.trans hWf
  have hScP' : CryptoVerification.E2E.RecordX.SessionScopeP ses' :=
    ⟨hRC', hPendTs, hKyber, hAbk⟩
  have hKit' : scopeKit (MessageEncrypt.storedRecord sess otr' taken) := by
    refine ⟨⟨?_, ?_, ?_⟩, ses', rfl, hScP'⟩
    · intro s hs; injection hs with hs; subst hs
      refine ⟨hSeeds', Nat.lt_of_le_of_lt hRC' (by decide), fun ky hky => ?_⟩
      rw [hKyber ky hky]; decide
    · intro s hs; injection hs with hs; subst hs
      exact hPqLt
    · intro s hs; injection hs with hs; subst hs
      exact ⟨hRep'.1, hRep'.2, hWf', hAbk32⟩
  have hBdd' : CryptoVerification.E2E.RecordX.DeserializeScopeBounded
      ⟨some (PqValid.stripPq ses')⟩ :=
    stripPq_bounded_of_parts hSeeds' hRC' hRep' hWf' hPendTs hKyber hAbk
  exact ⟨hKit', PqValid.encodeRecord_length_lt_32_of_stripPq_bounded hBdd' hPqOut⟩

/-- `DecModelRecOk` for `cliSessionStoreSpec` whenever `Scope ⊆ scopeIn` and `scopeKit ⊆ KitScope`. -/
theorem cliDecModelRecOk_of_scopeIn {A : RustAlloc} {b : BitVec 64} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop}
    {KitScope Scope : SessionRecord (List (BitVec 8)) → Prop}
    {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem} {parse : UuidParser}
    (hIn : ∀ r, Scope r → scopeIn r)
    (hOut : ∀ r', scopeKit r' → KitScope r') :
    MessageDecrypt.DecModelRecOk
      (cliSessionStoreSpec A b rd F0 pathOk KitScope peer s1 s2 s3 s4)
      C (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K) parse Scope := by
  intro x _st0 rec rec' pt hScopeAt hDec
  obtain ⟨hKit, hLen⟩ := decryptRecord_recOk_of_scopeIn (hIn rec hScopeAt.1) hDec
  exact ⟨hOut rec' hKit, hLen⟩

/-- Fixed-`st0`, `kit.addrOk`-guarded variant of `DecModelRecOk`. -/
@[expose] def DecModelRecOkAt {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  ∀ (x : DecryptGhost) (rec rec' : SessionRecord (List (BitVec 8)))
    (pt : List (BitVec 8)),
    kit.addrOk x.rem.val →
    kit.ScopeAt Scope st0 x.rem.val rec →
    MessageDecrypt.decryptRecord C S parse x rec = .ok (pt, rec') →
    kit.RecOk rec'

/-- `DecModelRecOkAt` at `StoresGhost.opened.sessions` and `scopeKit` on a well-formed peer file (`Scope₀ ⊆ scopeIn`). -/
theorem cliDecModelRecOkAt_opened {A : RustAlloc} {b : BitVec 64}
    {pathOk : List (BitVec 8) → Prop} {Scope₀ : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem} {parse : UuidParser}
    (hsub : ∀ r', Scope₀ r' → scopeIn r')
    (hok : FilesOkPeer Scope₀ F0 peer.val) :
    DecModelRecOkAt
      (cliSessionStoreSpec A b cliIo.rd F0 pathOk scopeKit peer s1 s2 s3 s4)
      StoresGhost.opened.sessions
      C (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K) parse scopeKit := by
  intro x rec rec' pt haddr hsc hdec
  have hIn : scopeIn rec := (cliSess_scopeIn_of_opened hsub hok haddr hsc).2
  exact decryptRecord_recOk_of_scopeIn hIn hdec

/-- `storedRecord` satisfies `kit.RecOk` at `StoresGhost.opened.sessions` and `scopeKit` on a well-formed peer file (`Scope₀ ⊆ scopeIn`). -/
theorem cliEncRecOk_opened {A : RustAlloc} {b : BitVec 64}
    {pathOk : List (BitVec 8) → Prop} {Scope₀ : SessionRecord (List (BitVec 8)) → Prop}
    {F0 : FsFiles} {peer : AddrGhost} {s1 s2 s3 s4 : Nat}
    {C : Crypto} {K : CryptoVerification.LibsignalSpqrV1.MlKem} {parse : UuidParser}
    {x : MessageEncrypt.WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr otr' : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    (hsub : ∀ r', Scope₀ r' → scopeIn r')
    (hok : FilesOkPeer Scope₀ F0 peer.val)
    (haddr : (cliSessionStoreSpec A b cliIo.rd F0 pathOk scopeKit peer s1 s2 s3 s4).addrOk x.rem.val)
    (hStep : MessageEncrypt.StepsThroughEncrypt
      ((cliSessionStoreSpec A b cliIo.rd F0 pathOk scopeKit peer s1 s2 s3 s4).ScopeAt
        scopeKit StoresGhost.opened.sessions x.rem.val)
      C (CryptoVerification.LibsignalSpqrV1.spqrV1 C.F K) parse x r sess otr taken k m otr') :
    (cliSessionStoreSpec A b cliIo.rd F0 pathOk scopeKit peer s1 s2 s3 s4).RecOk
      (MessageEncrypt.storedRecord sess otr' taken) := by
  obtain ⟨hCur, hScAt, hFrom, hRemId, hEnc⟩ := hStep
  have hIn : scopeIn r := (cliSess_scopeIn_of_opened hsub hok haddr hScAt).2
  exact storedRecord_recOk_of_scopeIn ⟨hCur, hIn, hFrom, hRemId, hEnc⟩

/-! ## 4. `Stage2ContractsMin`, `SessionRecord::deserialize` at `scopeKit`, and trap-program kit glue -/

theorem trTrapExterns_cli_eq (W : CliHooks) {n : String}
    (hn : n ≠ rngFillName) (hnp : Rust.isPanicSymbol n = false) :
    trTrapExterns W.C (cliExterns W) n = cliExterns W n := by
  have h1 : Rust.withPanics (trTrapExterns W.C (cliExterns W)) n =
      trTrapExterns W.C (cliExterns W) n := by
    simp [Rust.withPanics, hnp]
  rw [← h1, withPanics_trTrap_ne W.C (cliExterns W) hn,
    cliExterns_agree W 0#64 hn, congrFun (withPanics_cliExterns W) n]

theorem hookSat_trTrap_of_cli {α : Type} (W : CliHooks) {n : String} {spec : Spec α}
    (hn : n ≠ rngFillName) (hnp : Rust.isPanicSymbol n = false)
    (h : HookSat (cliExterns W) n spec) :
    HookSat (trTrapExterns W.C (cliExterns W)) n spec := by
  rcases h with ⟨fn, hfn, hok⟩
  exact ⟨fn, (trTrapExterns_cli_eq W hn hnp).trans hfn, hok⟩

private theorem hookOk_withExternStackFromAlloc' {α : Type} {fn : State → State} {spec : Spec α}
    (h : HookOk fn spec)
    (hpan : ∀ x R s0 sf, sf.mem ⊨ spec.onPanic x s0 sf ∗ (memRegion (s0.sp - 16384#64) 12288 ∗ R) →
      sf.mem ⊨ spec.onPanic x s0 sf ∗ R)
    (hexit : ∀ x code R s0 sf,
      ¬ (sf.mem ⊨ spec.onExit x code s0 sf ∗ (memRegion (s0.sp - 16384#64) 12288 ∗ R)))
    (hoom : ∀ x R s0 sf,
      ¬ (sf.mem ⊨ spec.onOom x s0 sf ∗ (memRegion (s0.sp - 16384#64) 12288 ∗ R))) :
    HookOk fn spec.withExternStackFromAlloc' := by
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ spec.pre x s0 ∗ (memRegion (s0.sp - 16384#64) 12288 ∗ R) := by
    simpa only [Spec.withExternStackFromAlloc', sepConj_assoc] using hpre
  obtain ⟨hkf, hsym, hout⟩ := h x (memRegion (s0.sp - 16384#64) 12288 ∗ R) s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hp_st, hp⟩ | ⟨code, hex_st, he⟩ | ⟨htrap, ho⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    simpa only [Spec.withExternStackFromAlloc', sepConj_assoc] using hpost
  · exact Or.inr (Or.inl ⟨hp_st, hpan x R s0 (fn s0) hp⟩)
  · exact False.elim (hexit x code R s0 (fn s0) he)
  · exact False.elim (hoom x R s0 (fn s0) ho)

private theorem deallocLayoutHook0_ok :
    HookOk E2E.deallocHook (Proofs.libsignal.Hooks2.rustDeallocLayoutSpec' E2E.HooksE.A0) := by
  intro ⟨p, size, align⟩ R s0 hrun hpre hsp
  dsimp only [Proofs.libsignal.Hooks2.rustDeallocLayoutSpec'] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact E2E.HooksE.deallocHook_ok (p, size, align) R s0 hrun hpre.2 hsp

private theorem hookOk_withHookStack {α : Type} {fn : State → State} {spec : Spec α}
    (h : HookOk fn spec) (stk : Nat)
    (hpan : ∀ x R s0 sf, ¬ (sf.mem ⊨ spec.onPanic x s0 sf ∗ (stackAt s0.sp stk ∗ R)))
    (hexit : ∀ x code R s0 sf, ¬ (sf.mem ⊨ spec.onExit x code s0 sf ∗ (stackAt s0.sp stk ∗ R)))
    (hoom : ∀ x R s0 sf, ¬ (sf.mem ⊨ spec.onOom x s0 sf ∗ (stackAt s0.sp stk ∗ R))) :
    HookOk fn (spec.withHookStack stk) := by
  intro x R s0 hrun hpre hsp
  have hpre' : s0.mem ⊨ spec.pre x s0 ∗ (stackAt s0.sp stk ∗ R) := by
    simpa only [Spec.withHookStack, sepConj_assoc] using hpre
  obtain ⟨hkf, hsym, hout⟩ := h x (stackAt s0.sp stk ∗ R) s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    simpa only [Spec.withHookStack, sepConj_assoc] using hpost
  · exact False.elim (hpan x R s0 (fn s0) hp)
  · exact False.elim (hexit x code R s0 (fn s0) he)
  · exact False.elim (hoom x R s0 (fn s0) ho)

private theorem rngTrap_fsT : HookFsTraced RunGlue.IsFsC rngTrap :=
  fun _ => FsTraced.of_eq rfl rfl

theorem fsTHooks_withPanics_trTrap (W : CliHooks) :
    RunGlue.FsTHooks (Rust.withPanics (trTrapExterns W.C (cliExterns W))) := by
  intro n f h
  by_cases hr : n = rngFillName
  · subst hr
    unfold Rust.withPanics trTrapExterns ProofLib.Variant.trapAt at h
    split at h
    · cases h; exact RunGlue.panicked_fsT
    · simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h; exact rngTrap_fsT
  · rw [withPanics_trTrap_ne W.C (cliExterns W) hr, cliExterns_agree W 0#64 hr] at h
    exact RunGlue.fsTHooks_withPanics (RunGlue.fsTHooks_cliExterns W) n f h

section ExtKitGlue

end ExtKitGlue

end CryptoVerification.SignalSession.Cli.Slots
