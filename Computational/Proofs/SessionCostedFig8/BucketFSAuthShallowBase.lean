/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth -- proof-setup: allow-public-import
public import Computational.Proofs.SessionCostedFig8.BundlesCompilers -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.Fig8Atomic -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.SM.RedFS

/-!
# Shallow Game & Hook State-Preservation Base for `(tL, par)`-Bucket Multi-Session FS-AEAD

Defines the shallow `OracleComp (unifSpec + FSMultiSpec ...)` reduction `redFSAuthMultiBucket`,
`redFSAuthMultiBucketShallowBase`, and proves the hook table/session/book length-preservation
invariants shared by `BucketFSAuthEvalHooks`, `BucketFSAuthEvalStep`, and `BucketFSAuthShallow`.-/

namespace Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase

public section

set_option autoImplicit false

open OracleSpec OracleComp
open _root_.CryptoGames (Party CKAScheme PRFPRNG FSAEADScheme)
open _root_.CryptoGames.CBC (Plain)
open _root_.CryptoGames.CKA (DHFun)
open _root_.CryptoGames.FSAEAD (RatchetSenderState RatchetReceiverState)
open _root_.CryptoGames.PRFPRNG (prngSig prngOps prngSMCodec)
open _root_.CryptoGames.SM (GameState Record senderOfE senderOfE_eval validGuessE
  validGuessE_eval ltOpt ltOptE)
open _root_.CryptoGames.SM.Construction (PartyState SchemeAdversary Header healEpoch FSMultiSpec
  FSMultiBook mkParties realParty sampleT bucketAuthCfgEC fsaeadMultiHeaderAdIface)
open _root_.CryptoGames.SM.Engine (VP Ctx HM TComp EState Hooks ConfigECAgrees optNatLit
  cGsTy cGsEnc cGsTL vSend deliverE injectE)
open _root_.CryptoGames.Ratchet.LibsignalInst (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32)
open _root_.CryptoGames.Ratchet.LibsignalSim (Fig8St Fig8C)
open _root_.CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey maxForwardJumps)
open _root_.ReductionDsl (Ops Ty Env Expr CostedReduction)
open Computational.Proofs.SessionCostedFig8.BundlesCompilers (fig8CkaOpsShallow)
open Computational.Proofs.CryptoGames.SM.Theorem8.BucketPRNGAuth (postLeak fsMultiBucketHsTy
  postLeakBucketE validGuessBucketParAuthE bucketAuthCfg redFSAuthMultiBucketProg)

/-- Shallow-ops instantiation of `BucketPRNGAuth.redFSAuthMultiBucketProg` over
`BundlesCompilers.fig8CkaOpsShallow` and `fsaeadMultiHeaderAdIface`. -/
@[expose] def redFSAuthMultiBucketShallowBase
    (ℓ : ℕ) (Pt : Type) [DecidableEq Pt] [Zero Pt] [SampleableType Pt]
    (C : Crypto) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (idOf : Party → IdentityKey) (lam : Pt)
    (L B0 qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool) :
    CostedReduction (fig8CkaOpsShallow ℓ Pt C Dh encPt encT idOf lam B0)
      (fsaeadMultiHeaderAdIface (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32)
        ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ (BitVec 256)) ($ᵗ Pt) ($ᵗ (BitVec 256)))
      (CryptoGames.SM.spec (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
      (prngSMCodec (BitVec 256) (CryptoGames.CKA.DDH.State (BitVec 256) Pt)
        (BitVec 256) Pt Pt (BitVec 256) (BitVec 256) (BitVec 256)
        (RatchetSenderState (BitVec 256)) (RatchetReceiverState (BitVec 256) (BitVec 256))
        (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
      .unit .unit .bool .bool :=
  let _ : Inhabited Pt := ⟨0⟩
  redFSAuthMultiBucketProg L B0 1 qep maxForwardJumps gMain la tL par

structure FSMultiBucketAuthState (T RSt K I E : Type) where
  cache : ℕ → Option (T × RSt × K × Option ℕ) := fun _ => none
  fTable : ℕ → List (I × K) := fun _ => []
  sessions : ℕ → List I := fun _ => []
  book : ℕ → Option (FSMultiBook T E) := fun _ => none
  lfWin : Bool := false

@[expose] def liftFSMultiBucket {SS RS T M E RSt K I : Type} (sIdx : ℕ) {α : Type}
    (x : _root_.CryptoGames.FSAEAD.AdversaryComp SS RS (Header T) M E α) :
    HM (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E) α :=
  let liftImpl : QueryImpl (unifSpec + _root_.CryptoGames.FSAEAD.spec SS RS (Header T) M E)
      (TComp (FSMultiSpec SS RS T M E)) := fun
    | .inl n => query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n)
    | .inr q => query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inr ⟨sIdx, q⟩)
  StateT.lift (simulateQ liftImpl x)

@[expose] def lookupMultiBucketF {SS RS T M E RSt K I : Type} [DecidableEq I] [SampleableType K]
    (t0 : ℕ) (ik : I) :
    HM (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E) K := do
  let tb0 := (← get).fTable t0
  match tb0.lookup ik with
  | some k => return k
  | none =>
    let k ← StateT.lift (sampleT K)
    modify fun s => { s with fTable := Function.update s.fTable t0 ((ik, k) :: tb0) }
    return k

@[expose] def regSessMultiBucket {T RSt K I E : Type} [DecidableEq I]
    (L : ℕ) (gMain : Bool) (tL : Option ℕ) (t0 : ℕ) (ik : I)
    (s : FSMultiBucketAuthState T RSt K I E) : ℕ × FSMultiBucketAuthState T RSt K I E :=
  let ses0 := s.sessions t0
  let base := L * (t0 - healEpoch tL)
  let off := if gMain then 0 else 1
  if ik ∈ ses0 then
    (base + ses0.idxOf ik + off, s)
  else
    (base + ses0.length + off, { s with sessions := Function.update s.sessions t0 (ses0 ++ [ik]) })

@[expose] def regSessOptMultiBucket {T RSt K I E : Type} [DecidableEq I]
    (L : ℕ) (gMain : Bool) (tL : Option ℕ) (t0 : ℕ) (sid : Option I)
    (s : FSMultiBucketAuthState T RSt K I E) :
    Option ℕ × FSMultiBucketAuthState T RSt K I E :=
  match sid with
  | none => (none, s)
  | some ik =>
    let (idx, s') := regSessMultiBucket L gMain tL t0 ik s
    (some idx, s')

@[expose] def validGuessBucketParAuth (Δcka : ℕ) (tL : Option ℕ) (par : Bool) (t0 : ℕ) : Bool :=
  _root_.CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t0 &&
    (decide (Party.senderOf t0 == Party.A) == par)

@[expose] def rootFSMultiBucketAuth {KR RSt I K SS RS T M E : Type}
    [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I K) (Δcka qep : ℕ)
    (tL : Option ℕ) (par : Bool) (t0 : ℕ) (pl0 : Bool) (ik0 : I) (σ0 : RSt) :
    HM (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E) (RSt × K × Option I) := do
  let tH := healEpoch tL
  let pIk := prng.up σ0 ik0
  if pl0 || qep + 1 < t0 then
    return (pIk.1, pIk.2, none)
  else if validGuessBucketParAuth Δcka tL par t0 then
    if tL.isSome && (t0 == tH) then
      let ir ← StateT.lift (sampleT I)
      let kSample ← StateT.lift (sampleT K)
      return ((prng.up σ0 ir).1, kSample, some ir)
    else
      let kLookup ← lookupMultiBucketF t0 ik0
      return (pIk.1, kLookup, some ik0)
  else if tL.isSome && (t0 == tH) then
    let ir ← StateT.lift (sampleT I)
    let kSample ← StateT.lift (sampleT K)
    return ((prng.up σ0 ir).1, kSample, none)
  else if !(t0 < tH) then
    let kLookup ← lookupMultiBucketF t0 ik0
    return (pIk.1, kLookup, none)
  else
    return (pIk.1, pIk.2, none)

@[expose] def isHonestHdrMultiBucket {T RSt K I E : Type} [DecidableEq T]
    (h : FSMultiBucketAuthState T RSt K I E) (hdr : Header T) : Bool :=
  match h.cache hdr.1, hdr.2 with
  | some (Tc, _, _, _), some Tn => Tc == Tn
  | _, _ => false

@[expose] def hooksFSMultiBucketAuth {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins T I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I K)
    (fs : _root_.CryptoGames.FSAEADScheme K SS RS (Header T) M E)
    (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par la : Bool) :
    Hooks (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E)
      Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ) where
  startSend ctx _ t0 γ0 σ0 r0 := do
    let pl0 := postLeak tL ctx
    let coins ← (match r0 with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins))
    let cOut := cka.send γ0 coins
    let (σ', kVal, sid) ← rootFSMultiBucketAuth prng Δcka qep tL par t0 pl0 cOut.2.2 σ0
    let s1 ← get
    let (optIdx, s2) := regSessOptMultiBucket L gMain tL t0 sid s1
    set { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kVal, optIdx)) }
    let ssv : SS ⊕ ℕ := match optIdx with
      | none => .inl (fs.initSender kVal)
      | some sIdx => .inr sIdx
    return some (cOut.1, cOut.2.1, σ', ssv)
  startRecv ctx _ t0 γ0 σ0 tn0 := do
    let tH := healEpoch tL
    let pl0 := postLeak tL ctx
    let honest := match (← get).cache t0 with
      | some (tCached, σc, kVal, optIdx) => if tCached = tn0 then some (σc, kVal, optIdx) else none
      | none => none
    match honest with
    | some (σc, kVal, optIdx) =>
      let rsv : RS ⊕ ℕ := match optIdx with
        | none => .inl (fs.initReceiver kVal)
        | some sIdx => .inr sIdx
      return some (some ((cka.receive γ0 tn0).1, σc, rsv))
    | none =>
      if gMain then
        if !(qep + 1 < t0) && _root_.CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t0 &&
            (tL.isSome && (t0 == tH)) then
          return none
        else
          return some none
      else if !(qep + 1 < t0) && _root_.CryptoGames.SM.lastLeakGuessAdmissible (2 + Δcka) tL t0 then
        if tL.isSome && (t0 == tH) then
          return none
        else if pl0 then
          let kk := cka.receive γ0 tn0
          let p := prng.up σ0 kk.2
          return some (some (kk.1, p.1, .inl (fs.initReceiver p.2)))
        else if validGuessBucketParAuth Δcka tL par t0 then
          let kk := cka.receive γ0 tn0
          let _ ← lookupMultiBucketF t0 kk.2
          let s1 ← get
          let (sIdx, s2) := regSessMultiBucket L false tL t0 kk.2 s1
          set s2
          return some (some (kk.1, (prng.up σ0 kk.2).1, .inr sIdx))
        else if !(t0 < tH) then
          let kk := cka.receive γ0 tn0
          let k' ← lookupMultiBucketF t0 kk.2
          return some (some (kk.1, (prng.up σ0 kk.2).1, .inl (fs.initReceiver k')))
        else
          return some none
      else
        return some none
  fsSend ctx P _ ssv h m pair := do
    match ssv with
    | .inl ss =>
      let o := fs.send ss h m
      return some (.inl o.1, o.2)
    | .inr sIdx =>
      let s ← get
      let bk := (s.book sIdx).getD {}
      let ok ← (if !(ctx.safeCh (2 + Δcka) P) && !bk.sCorr then do
          match ← liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.corruptSenderQuery
              (ReceiverState := RS) (AssocData := Header T) (Message := M) (Ciphertext := E)) with
          | none => pure false
          | some _ =>
            modify fun s =>
              let b := (s.book sIdx).getD {}
              { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
            pure true
        else pure true)
      if !ok then return none
      let e? ← (match pair with
        | some (m₀, m₁) =>
          liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.challengeQuery
            (SenderState := SS) (ReceiverState := RS) h m₀ m₁)
        | none =>
          liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.transmitQuery
            (SenderState := SS) (ReceiverState := RS) h m))
      match e? with
      | none => return none
      | some e =>
        modify fun s =>
          let b := (s.book sIdx).getD {}
          let cnt' := b.fsCount + 1
          let b' : FSMultiBook T E := { b with fsCount := cnt', fsTrans := (cnt', h, e) :: b.fsTrans }
          { s with book := Function.update s.book sIdx (some b') }
        return some (.inr sIdx, e)
  fsRecv ctx _ t0 rsv h e rec := do
    match rsv with
    | .inl rs => return some ((fs.receive rs h e).map fun o => (.inl o.1, o.2.1, o.2.2))
    | .inr sIdx =>
      let s ← get
      let bk := (s.book sIdx).getD {}
      let matched := bk.fsTrans.find? (fun x => x.2 == (h, e))
      let ok ← (if matched.isNone && !(_root_.CryptoGames.SM.healedBy ctx.tL (2 + Δcka) t0) && !bk.sCorr then do
          match ← liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.corruptSenderQuery
              (ReceiverState := RS) (AssocData := Header T) (Message := M) (Ciphertext := E)) with
          | none => pure false
          | some _ =>
            modify fun s =>
              let b := (s.book sIdx).getD {}
              { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
            pure true
        else pure true)
      if !ok then return none
      let res ← (if matched.isSome then
          liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.deliverQuery
            (SenderState := SS) (ReceiverState := RS) h e)
        else
          liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.injectQuery
            (SenderState := SS) (ReceiverState := RS) h e))
      match res with
      | none => return none
      | some .rejected => return some none
      | some (.accepted i mo') =>
        let s1 ← get
        let bk1 := (s1.book sIdx).getD {}
        if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
          modify fun s => { s with lfWin := true }
          return none
        else
          let drop := (matched.map (·.1)).getD i
          modify fun s =>
            let b := (s.book sIdx).getD {}
            let b' : FSMultiBook T E := { b with fsTrans := b.fsTrans.filter (·.1 != drop) }
            { s with book := Function.update s.book sIdx (some b') }
          match mo', rec with
          | some m, _ => return some (some (.inr sIdx, i, m))
          | none, some r => return some (some (.inr sIdx, i, r.msg))
          | none, none => return none
  commit _ _ _ new := pure (some new)
  reveal ctx _ vp := do
    let tH := healEpoch tL
    if !gMain && (!(vp.tcur < tH) || !(max (ctx.epoch Party.A) (ctx.epoch Party.B) < tH)) then
      return none
    else
      let vS? : Option (Option SS) ← (match vp.vS with
        | none => pure (some none)
        | some (.inl ss) => pure (some (some ss))
        | some (.inr sIdx) => do
          match ← liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.corruptSenderQuery
              (ReceiverState := RS) (AssocData := Header T) (Message := M) (Ciphertext := E)) with
          | none => pure none
          | some ss =>
            modify fun s =>
              let b := (s.book sIdx).getD {}
              { s with book := Function.update s.book sIdx (some { b with sCorr := true }) }
            pure (some (some ss)))
      match vS? with
      | none => return none
      | some ssReal =>
        if (List.range L).any (fun t => match vp.vR t with | some (.inr _) => true | _ => false) then
          return none
        else
          let vR' : ℕ → Option RS := fun t =>
            if t < L then
              match vp.vR t with
              | some (.inl rs) => some rs
              | _ => none
            else none
          return some (realParty vp vp.γ vp.root ssReal vR')

@[expose] def initFSMultiBucketAuth {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq I] [SampleableType KR] [SampleableType KC]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins T I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I K)
    (fs : _root_.CryptoGames.FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep : ℕ) (gMain : Bool) (tL : Option ℕ) (par : Bool) :
    HM (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E)
      (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) × VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) := do
  let kr ← StateT.lift (sampleT KR)
  let kc ← StateT.lift (sampleT KC)
  let (σ, kVal, sid) ← rootFSMultiBucketAuth prng Δcka qep tL par 0 false lam (prng.init kr)
  let s1 ← get
  let (optIdx, s2) := if gMain then regSessOptMultiBucket L true tL 0 sid s1 else (none, s1)
  set s2
  let ssv0 : SS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initSender kVal)
    | some sIdx => .inr sIdx
  let rsv0 : RS ⊕ ℕ := match optIdx with
    | none => .inl (fs.initReceiver kVal)
    | some sIdx => .inr sIdx
  return mkParties (cka.initA kc) (cka.initB kc) σ ssv0 rsv0

abbrev FSMultiBucketAuthEState (Γ T RSt SS RS M E K I : Type) :=
  EState (VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ)) M (Header T × E) (FSMultiBucketAuthState T RSt K I E) ×
    Option ℕ

@[expose] def implFSMultiBucketAuth {Γ T RSt SS RS M E CCoins K I : Type}
    [DecidableEq T] [DecidableEq M] [DecidableEq E] [Inhabited E]
    (hk : Hooks (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E)
      Γ T RSt SS RS M E CCoins Γ RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (Δcka qep maxSkip : ℕ) (gMain : Bool) (tL : Option ℕ) :
    QueryImpl
      (unifSpec + _root_.CryptoGames.SM.spec (PartyState Γ T RSt SS RS) M CCoins (Header T × E))
      (StateT (FSMultiBucketAuthEState Γ T RSt SS RS M E K I)
        (OracleComp (unifSpec + FSMultiSpec SS RS T M E))) :=
  let cfg := bucketAuthCfg (M := M) Δcka tL
  let i₀ : QueryImpl unifSpec
      (StateT (FSMultiBucketAuthEState Γ T RSt SS RS M E K I)
        (OracleComp (unifSpec + FSMultiSpec SS RS T M E))) :=
    fun n => StateT.lift (query (spec := unifSpec + FSMultiSpec SS RS T M E) (.inl n))
  let i₁ : QueryImpl ((Party × M × Option CCoins) →ₒ Option (Header T × E))
      (StateT (FSMultiBucketAuthEState Γ T RSt SS RS M E K I)
        (OracleComp (unifSpec + FSMultiSpec SS RS T M E))) :=
    fun ⟨P, m, r⟩ => do
      let (es0, winEp0) ← get
      if es0.abort || es0.g.win then return none
      match es0.g.epMgmt (2 + Δcka) qep P r.isSome with
      | none => return none
      | some s₁ =>
        let (res, h') ← StateT.lift ((vSend hk s₁ P (s₁.st P) m none r).run es0.h)
        match res with
        | none =>
          set ({ es0 with h := h', abort := true }, winEp0)
          return none
        | some (st', ct) =>
          let recE : _root_.CryptoGames.SM.Record M (Header T × E) :=
            ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, ct⟩
          set ({ es0 with g := s₁.record (2 + Δcka) P st' recE false, h := h' }, winEp0)
          return some ct
  let i₂ : QueryImpl ((Party × M × M × Option CCoins) →ₒ Option (Header T × E))
      (StateT (FSMultiBucketAuthEState Γ T RSt SS RS M E K I)
        (OracleComp (unifSpec + FSMultiSpec SS RS T M E))) :=
    fun _ => pure none
  let i₃ : QueryImpl ((Party × (Header T × E)) →ₒ Option (_root_.CryptoGames.SM.RecvResult M))
      (StateT (FSMultiBucketAuthEState Γ T RSt SS RS M E K I)
        (OracleComp (unifSpec + FSMultiSpec SS RS T M E))) :=
    fun x => do
      let (es0, winEp0) ← get
      let (out, es') ← StateT.lift ((deliverE hk maxSkip cfg x).run es0)
      set (es', winEp0)
      return out
  let i₄ : QueryImpl ((Party × (Header T × E)) →ₒ Option (_root_.CryptoGames.SM.RecvResult M))
      (StateT (FSMultiBucketAuthEState Γ T RSt SS RS M E K I)
        (OracleComp (unifSpec + FSMultiSpec SS RS T M E))) :=
    fun x => do
      let (es0, winEp0) ← get
      let wasWin := es0.g.win
      let isNewForged :=
        decide (x.2.1.1 = (es0.g.st x.1).tcur + 1) && !isHonestHdrMultiBucket es0.h x.2.1
      let (out, es') ← StateT.lift ((injectE hk (2 + Δcka) qep cfg x).run es0)
      let winEp' :=
        if !wasWin && es'.g.win && (gMain || isNewForged) then some x.2.1.1 else winEp0
      set (es', winEp')
      return out
  let i₅ : QueryImpl (Party →ₒ Option (PartyState Γ T RSt SS RS))
      (StateT (FSMultiBucketAuthEState Γ T RSt SS RS M E K I)
        (OracleComp (unifSpec + FSMultiSpec SS RS T M E))) :=
    fun P => do
      let (es0, winEp0) ← get
      if es0.abort || es0.g.win || !(es0.g.corrAllowed P) then return none
      let s₁ := es0.g.afterCorr P
      let (res, h') ← StateT.lift ((hk.reveal es0.g P (es0.g.st P)).run es0.h)
      match res with
      | none =>
        set ({ es0 with h := h', abort := true }, winEp0)
        return none
      | some stOut =>
        set ({ es0 with g := s₁, h := h' }, winEp0)
        return some stOut
  HAdd.hAdd i₀ (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

@[expose] def redFSAuthMultiBucket {KC Γ CCoins T I KR RSt K SS RS M E : Type}
    [DecidableEq T] [DecidableEq I] [DecidableEq M] [DecidableEq E] [Inhabited E]
    [SampleableType KR] [SampleableType KC] [SampleableType CCoins]
    [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : _root_.CryptoGames.CKAScheme KC Γ CCoins T I)
    (prng : _root_.CryptoGames.PRFPRNG KR RSt I K)
    (fs : _root_.CryptoGames.FSAEADScheme K SS RS (Header T) M E)
    (lam : I) (Δcka qep : ℕ) (gMain la : Bool) (tL : Option ℕ) (par : Bool)
    (A : SchemeAdversary Γ T RSt SS RS M CCoins E) :
    OracleComp (unifSpec + FSMultiSpec SS RS T M E) Bool := do
  let ((vA, vB), h0) ← (initFSMultiBucketAuth L cka prng fs lam Δcka qep gMain tL par).run {}
  let g0 : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E :=
    { st := fun P => match P with | .A => vA | .B => vB, b := false }
  let hk := hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la
  let (_, es, winEp) ←
    (simulateQ (implFSMultiBucketAuth hk Δcka qep fs.maxSkip gMain tL) A).run
      ({ g := g0, h := h0, abort := false }, none)
  if la then
    return es.h.lfWin
  else
    match winEp with
    | none => return false
    | some tWin =>
      return (!es.abort && es.g.win &&
        _root_.CryptoGames.SM.authLosingConditionsAvoided (2 + Δcka) tL tWin es.g &&
        (decide (Party.senderOf tWin == Party.A) == par))

section BucketEvalBridge

variable {KC Γ CCoins T I KR RSt K SS RS M E : Type}

@[expose] def fsMultiBucketHsEnc (h : FSMultiBucketAuthState T RSt K I E) :
    (@fsMultiBucketHsTy KC Γ CCoins T I KR RSt K SS RS M E).denote :=
  (h.cache, h.fTable, h.sessions,
   (fun sIdx => (h.book sIdx).map fun b => (b.sCorr, b.fsCount, b.fsTrans)),
   h.lfWin)

@[expose] def FSMultiBucketHBounded (L : ℕ) (h : FSMultiBucketAuthState T RSt K I E) : Prop :=
  (∀ t, (h.fTable t).length ≤ L) ∧
  (∀ t, (h.sessions t).length ≤ L) ∧
  ∀ sIdx bk, h.book sIdx = some bk → bk.fsTrans.length ≤ L

@[expose] def FSMultiBucketHBoundedPost (L : ℕ) (h : FSMultiBucketAuthState T RSt K I E) : Prop :=
  ∀ sIdx bk, h.book sIdx = some bk → bk.fsTrans.length ≤ L

@[expose] def FSMultiBucketStepBounded (B_q q : ℕ)
    (h : FSMultiBucketAuthState T RSt K I E) : Prop :=
  (∀ t, (h.fTable t).length + q ≤ B_q + 1) ∧
  (∀ t, (h.sessions t).length + q ≤ B_q + 1) ∧
  ∀ sIdx bk, h.book sIdx = some bk → bk.fsTrans.length + q ≤ B_q

theorem FSMultiBucketStepBounded.mono {B_q m₁ m₂ : ℕ}
    {h : FSMultiBucketAuthState T RSt K I E} (hm : m₁ ≤ m₂)
    (hB : FSMultiBucketStepBounded B_q m₂ h) :
    FSMultiBucketStepBounded B_q m₁ h :=
  ⟨fun t => by have := hB.1 t; omega,
   fun t => by have := hB.2.1 t; omega,
   fun sIdx bk hbk => by have := hB.2.2 sIdx bk hbk; omega⟩

theorem FSMultiBucketStepBounded.toHBounded {L B_q q : ℕ}
    {h : FSMultiBucketAuthState T RSt K I E} (hB1 : B_q + 1 ≤ L)
    (hB : FSMultiBucketStepBounded B_q q h) :
    FSMultiBucketHBounded L h :=
  ⟨fun t => by have := hB.1 t; omega,
   fun t => by have := hB.2.1 t; omega,
   fun sIdx bk hbk => by have := hB.2.2 sIdx bk hbk; omega⟩

theorem validGuessBucketParAuthE_eval
    {O' : Ops (prngSig KC Γ CCoins T I KR RSt K SS RS M E)} (Δcka : ℕ)
    (tL : Option ℕ) (par : Bool) {Γ'} (tE : Expr O' Γ' .nat) (ρ : Env Γ') :
    (validGuessBucketParAuthE (KC := KC) (Γ := Γ) (CCoins := CCoins) (T := T) (I := I)
        (KR := KR) (RSt := RSt) (K := K) (SS := SS) (RS := RS) (M := M) (E := E)
        Δcka tL par tE).eval ρ =
      validGuessBucketParAuth Δcka tL par (tE.eval ρ) := by
  unfold validGuessBucketParAuthE validGuessBucketParAuth
  have htL : (optNatLit (O' := O') tL).eval ρ = tL := by cases tL <;> rfl
  simp only [Expr.eval, validGuessE_eval, senderOfE_eval, htL]
  congr 1
  cases par <;> cases Party.senderOf (tE.eval ρ) <;> rfl

theorem postLeakBucketE_eval {O' : Ops (prngSig KC Γ CCoins T I KR RSt K SS RS M E)}
    {vpT : Ty (prngSig KC Γ CCoins T I KR RSt K SS RS M E)} {VPt : Type}
    (vpEncFn : VPt → vpT.denote) (tL : Option ℕ) {Γ'}
    (ctxE : Expr O' Γ' (cGsTy vpT)) (ρ : Env Γ')
    (ctx : GameState VPt M (Header T × E))
    (hctx : ctxE.eval ρ = cGsEnc (vpT := vpT) vpEncFn ctx) :
    (postLeakBucketE tL ctxE).eval ρ = postLeak tL ctx := by
  unfold postLeakBucketE postLeak
  have hTL : (cGsTL ctxE).eval ρ = ctx.tL := by simp [cGsTL, cGsEnc, hctx, Expr.eval]
  rcases hcur : ctx.tL with _ | cur
  · simp [Expr.eval, hTL, hcur]
  · cases tL
    · simp [Expr.eval, Expr.v0, ltOptE, optNatLit, ltOpt, hTL, hcur]
    · simp only [Expr.eval, Expr.v0, Env.get_cons_zero, ltOptE, optNatLit, ltOpt, hTL, hcur]
      exact decide_eq_decide.mpr Iff.rfl

theorem bucketAuthCfgEC_agrees
    {ckaInitA : KC → Γ} {ckaInitB : KC → Γ}
    {ckaSend : Γ → CCoins → Γ × T × I} {ckaReceive : Γ → T → Γ × I}
    {prngInit : KR → RSt} {prngUp : RSt → I → RSt × K}
    {fsInitSender : K → SS} {fsInitReceiver : K → RS}
    {fsSend : SS → Header T → M → SS × E}
    {fsReceive : RS → Header T → E → Option (RS × ℕ × M)}
    {eqT : T → T → Bool} {eqI : I → I → Bool} {eqM : M → M → Bool} {eqE : E → E → Bool}
    {lam : I} {defaultE : E}
    (Δcka : ℕ) (tL : Option ℕ) :
    ConfigECAgrees (ckaInitA := ckaInitA) (ckaInitB := ckaInitB) (ckaSend := ckaSend)
      (ckaReceive := ckaReceive) (prngInit := prngInit) (prngUp := prngUp)
      (fsInitSender := fsInitSender) (fsInitReceiver := fsInitReceiver)
      (fsSend := fsSend) (fsReceive := fsReceive) (eqT := eqT) (eqI := eqI)
      (eqM := eqM) (eqE := eqE) (lam := lam) (defaultE := defaultE)
      (bucketAuthCfgEC Δcka tL) (bucketAuthCfg (M := M) Δcka tL) where
  deliverWin_eq := rfl
  injectFull_eq _ ρ := by
    have htL : (optNatLit (O' := prngOps ckaInitA ckaInitB ckaSend ckaReceive prngInit prngUp
      fsInitSender fsInitReceiver fsSend fsReceive eqT eqI eqM eqE lam defaultE) tL).eval ρ = tL := by
      cases tL <;> rfl
    simp [bucketAuthCfgEC, bucketAuthCfg, validGuessE_eval, htL]
  challOK_eq _ _ := rfl
  challMsg_eq _ _ _ _ _ := rfl

theorem lookupMultiBucketF_preserve [DecidableEq I] [SampleableType K]
    (t0 : ℕ) (ik : I) (h : FSMultiBucketAuthState T RSt K I E) :
    ∀ res ∈ support ((lookupMultiBucketF (SS := SS) (RS := RS) (M := M) t0 ik).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  unfold lookupMultiBucketF at hmem
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  rcases hlk : (h.fTable t0).lookup ik with _ | k
  · simp only [hlk] at hmem
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨kNew, h0⟩, hk, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hk
    obtain ⟨_, _, hEq1⟩ := hk; cases hEq1
    simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
      support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    refine ⟨fun τ => ?_, rfl, rfl⟩
    by_cases hτ : τ = t0 <;> simp [Function.update, hτ]
  · simp only [hlk, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    exact ⟨fun _ => Nat.le_add_right _ _, rfl, rfl⟩

theorem regSessMultiBucket_preserve [DecidableEq I]
    (L : ℕ) (gMain : Bool) (tL : Option ℕ) (t0 : ℕ) (ik : I)
    (h : FSMultiBucketAuthState T RSt K I E) :
    (regSessMultiBucket L gMain tL t0 ik h).2.fTable = h.fTable ∧
    (∀ τ, ((regSessMultiBucket L gMain tL t0 ik h).2.sessions τ).length ≤
      (h.sessions τ).length + 1) ∧
    (regSessMultiBucket L gMain tL t0 ik h).2.book = h.book := by
  dsimp only [regSessMultiBucket]
  by_cases hik : ik ∈ h.sessions t0
  · simp only [hik, ↓reduceIte]
    exact ⟨trivial, fun _ => Nat.le_add_right _ _, trivial⟩
  · simp only [hik, ↓reduceIte]
    refine ⟨trivial, fun τ => ?_, trivial⟩
    by_cases hτ : τ = t0 <;> simp [hτ]

theorem regSessOptMultiBucket_preserve [DecidableEq I]
    (L : ℕ) (gMain : Bool) (tL : Option ℕ) (t0 : ℕ) (sid : Option I)
    (h : FSMultiBucketAuthState T RSt K I E) :
    (regSessOptMultiBucket L gMain tL t0 sid h).2.fTable = h.fTable ∧
    (∀ τ, ((regSessOptMultiBucket L gMain tL t0 sid h).2.sessions τ).length ≤
      (h.sessions τ).length + 1) ∧
    (regSessOptMultiBucket L gMain tL t0 sid h).2.book = h.book := by
  rcases sid with _ | ik
  · exact ⟨rfl, fun _ => Nat.le_add_right _ _, rfl⟩
  · exact regSessMultiBucket_preserve L gMain tL t0 ik h

theorem rootFSMultiBucketAuth_preserve [DecidableEq I] [SampleableType I] [SampleableType K]
    (prng : PRFPRNG KR RSt I K) (Δcka qep : ℕ) (tL : Option ℕ) (par : Bool)
    (t0 : ℕ) (pl0 : Bool) (ik0 : I) (σ0 : RSt) (h : FSMultiBucketAuthState T RSt K I E) :
    ∀ res ∈ support ((rootFSMultiBucketAuth (SS := SS) (RS := RS) (M := M)
        prng Δcka qep tL par t0 pl0 ik0 σ0).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      res.2.sessions = h.sessions ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  dsimp only [rootFSMultiBucketAuth] at hmem
  split_ifs at hmem
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl, rfl⟩
  · rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ir, h0⟩, hIr, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hIr
    obtain ⟨_, _, hEq1⟩ := hIr; cases hEq1
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨kSample, h1⟩, hk, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hk
    obtain ⟨_, _, hEq2⟩ := hk; cases hEq2
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl, rfl⟩
  · rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨kLookup, h1⟩, hlk, hmem⟩ := hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    exact lookupMultiBucketF_preserve t0 ik0 h (kLookup, h') hlk
  · rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨ir, h0⟩, hIr, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hIr
    obtain ⟨_, _, hEq1⟩ := hIr; cases hEq1
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨kSample, h1⟩, hk, hmem⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hk
    obtain ⟨_, _, hEq2⟩ := hk; cases hEq2
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl, rfl⟩
  · rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨kLookup, h1⟩, hlk, hmem⟩ := hmem
    simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem
    exact lookupMultiBucketF_preserve t0 ik0 h (kLookup, h') hlk
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at hmem
    cases hmem; exact ⟨fun _ => Nat.le_add_right _ _, rfl, rfl⟩

theorem hooksFSMultiBucketAuth_startSend_preserve
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t0 : ℕ) (γ0 : Γ) (σ0 : RSt) (r0 : Option CCoins)
    (h : FSMultiBucketAuthState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).startSend
        ctx P t0 γ0 σ0 r0).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      (∀ τ, (res.2.sessions τ).length ≤ (h.sessions τ).length + 1) ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMultiBucketAuth at hmem
  dsimp only at hmem
  have hBody : ∀ coins,
      (out, h') ∈ support ((do
        let cOut := cka.send γ0 coins
        let (σ', kVal, sid) ← rootFSMultiBucketAuth (SS := SS) (RS := RS) (M := M) (E := E)
          prng Δcka qep tL par t0 (postLeak tL ctx) cOut.2.2 σ0
        let s1 ← (get : HM (FSMultiSpec SS RS T M E) (FSMultiBucketAuthState T RSt K I E) _)
        let (optIdx, s2) := regSessOptMultiBucket L gMain tL t0 sid s1
        set { s2 with cache := Function.update s2.cache t0 (some (cOut.2.1, σ', kVal, optIdx)) }
        let ssv : SS ⊕ ℕ := match optIdx with
          | none => .inl (fs.initSender kVal)
          | some sIdx => .inr sIdx
        return some (cOut.1, cOut.2.1, σ', ssv)).run h) →
      (∀ τ, (h'.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      (∀ τ, (h'.sessions τ).length ≤ (h.sessions τ).length + 1) ∧
      h'.book = h.book := by
    intro coins hm
    rw [StateT.run_bind, mem_support_bind_iff] at hm
    obtain ⟨⟨⟨σ', kVal, sid⟩, h1⟩, hrt, hm⟩ := hm
    have ⟨hT1, hS1, hB1⟩ := rootFSMultiBucketAuth_preserve prng Δcka qep tL par t0
      (postLeak tL ctx) (cka.send γ0 coins).2.2 σ0 h ((σ', kVal, sid), h1) hrt
    simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
      pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm
    rcases hm with ⟨_, rfl⟩
    have ⟨hT2, hS2, hB2⟩ := regSessOptMultiBucket_preserve L gMain tL t0 sid h1
    exact ⟨fun τ => by dsimp only; rw [hT2]; exact hT1 τ,
      fun τ => by dsimp only; have := hS2 τ; rw [hS1] at this; exact this,
      by dsimp only; rw [hB2, hB1]⟩
  rcases r0 with _ | c
  · rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨coins, h0⟩, hSamp, hm⟩ := hmem
    simp only [StateT.run_lift, mem_support_bind_iff, support_pure,
      Set.mem_singleton_iff] at hSamp
    obtain ⟨c', _, hEq⟩ := hSamp
    cases hEq
    exact hBody coins hm
  · simp only [StateT.run_bind, StateT.run_pure, pure_bind] at hmem
    exact hBody c hmem

theorem hooksFSMultiBucketAuth_startRecv_preserve
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (t0 : ℕ) (γ0 : Γ) (σ0 : RSt) (tn0 : T)
    (h : FSMultiBucketAuthState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).startRecv
        ctx P t0 γ0 σ0 tn0).run h),
      (∀ τ, (res.2.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      (∀ τ, (res.2.sessions τ).length ≤ (h.sessions τ).length + 1) ∧
      res.2.book = h.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMultiBucketAuth at hmem
  dsimp only at hmem
  rw [StateT.run_bind, StateT.run_get, pure_bind] at hmem
  have hDone : h' = h →
      (∀ τ, (h'.fTable τ).length ≤ (h.fTable τ).length + 1) ∧
      (∀ τ, (h'.sessions τ).length ≤ (h.sessions τ).length + 1) ∧
      h'.book = h.book := fun heq => by
    subst heq
    exact ⟨fun _ => Nat.le_add_right _ _, fun _ => Nat.le_add_right _ _, rfl⟩
  rcases hHon : (match h.cache t0 with
    | some (tCached, σc, kVal, optIdx) => if tCached = tn0 then some (σc, kVal, optIdx) else none
    | none => none) with _ | ⟨σc, kVal, optIdx⟩ <;> simp only [hHon] at hmem
  · split_ifs at hmem
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hDone hmem.2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hDone hmem.2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hDone hmem.2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hDone hmem.2
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨k1, h1⟩, hlk, hmem⟩ := hmem
      have ⟨hT1, hS1, hB1⟩ := lookupMultiBucketF_preserve t0 (cka.receive γ0 tn0).2 h (k1, h1) hlk
      simp only [StateT.run_bind, StateT.run_get, StateT.run_set, StateT.run_pure,
        pure_bind, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      have ⟨hT2, hS2, hB2⟩ := regSessMultiBucket_preserve L false tL t0 (cka.receive γ0 tn0).2 h1
      exact ⟨fun τ => by dsimp only; rw [hT2]; exact hT1 τ,
        fun τ => by dsimp only; have := hS2 τ; rw [hS1] at this; exact this,
        by dsimp only; rw [hB2, hB1]⟩
    · rw [StateT.run_bind, mem_support_bind_iff] at hmem
      obtain ⟨⟨k1, h1⟩, hlk, hmem⟩ := hmem
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      rcases hmem with ⟨_, rfl⟩
      have ⟨hT1, hS1, hB1⟩ := lookupMultiBucketF_preserve t0 (cka.receive γ0 tn0).2 h (k1, h') hlk
      exact ⟨hT1, fun τ => by rw [hS1]; exact Nat.le_add_right _ _, hB1⟩
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hDone hmem.2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      exact hDone hmem.2
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    exact hDone hmem.2

@[expose] def fsBookStep (k : ℕ) (b0 b1 : ℕ → Option (FSMultiBook T E)) : Prop :=
  ∀ idx bk', b1 idx = some bk' →
    (∃ bk₀, b0 idx = some bk₀ ∧ bk'.fsTrans.length ≤ bk₀.fsTrans.length + k) ∨
      bk'.fsTrans.length ≤ k

theorem fsBookStep_refl (k : ℕ) {b0 b1 : ℕ → Option (FSMultiBook T E)} (hEq : b1 = b0) :
    fsBookStep k b0 b1 := by
  intro idx bk' hbk'
  exact Or.inl ⟨bk', by rw [← hEq]; exact hbk', Nat.le_add_right _ _⟩

theorem fsBookStep_mono {k1 k2 : ℕ} (hk : k1 ≤ k2)
    {b0 b1 : ℕ → Option (FSMultiBook T E)} (h : fsBookStep k1 b0 b1) :
    fsBookStep k2 b0 b1 := by
  intro idx bk' hbk'
  rcases h idx bk' hbk' with ⟨bk₀, hbk₀, hle⟩ | hle
  · exact Or.inl ⟨bk₀, hbk₀, by omega⟩
  · exact Or.inr (by omega)

theorem fsBookStep_trans {k1 k2 : ℕ}
    {b0 b1 b2 : ℕ → Option (FSMultiBook T E)}
    (h01 : fsBookStep k1 b0 b1) (h12 : fsBookStep k2 b1 b2) :
    fsBookStep (k1 + k2) b0 b2 := by
  intro idx bk₂ hbk₂
  rcases h12 idx bk₂ hbk₂ with ⟨bk₁, hbk₁, hle₁⟩ | hle₂
  · rcases h01 idx bk₁ hbk₁ with ⟨bk₀, hbk₀, hle₀⟩ | hle₁'
    · exact Or.inl ⟨bk₀, hbk₀, by omega⟩
    · exact Or.inr (by omega)
  · exact Or.inr (by omega)

theorem fsBookStep_update_sCorr (b : ℕ → Option (FSMultiBook T E)) (sIdx : ℕ) :
    fsBookStep 0 b (Function.update b sIdx (some { (b sIdx).getD {} with sCorr := true })) := by
  intro idx bk' hbk'
  by_cases hEq : idx = sIdx
  · subst hEq
    rw [Function.update_self, Option.some.injEq] at hbk'
    subst hbk'
    rcases hb : b idx with _ | bk₀
    · exact Or.inr (by simp)
    · exact Or.inl ⟨bk₀, rfl, by simp⟩
  · rw [Function.update_of_ne hEq] at hbk'
    exact Or.inl ⟨bk', hbk', le_rfl⟩

theorem fsBookStep_update_cons (b : ℕ → Option (FSMultiBook T E)) (sIdx : ℕ)
    (hdr : Header T) (e : E) :
    fsBookStep 1 b (Function.update b sIdx
      (some { (b sIdx).getD {} with
        fsCount := ((b sIdx).getD {}).fsCount + 1
        fsTrans := (((b sIdx).getD {}).fsCount + 1, hdr, e) :: ((b sIdx).getD {}).fsTrans })) := by
  intro idx bk' hbk'
  by_cases hEq : idx = sIdx
  · subst hEq
    rw [Function.update_self, Option.some.injEq] at hbk'
    subst hbk'
    rcases hb : b idx with _ | bk₀
    · exact Or.inr (by simp)
    · exact Or.inl ⟨bk₀, rfl, by simp⟩
  · rw [Function.update_of_ne hEq] at hbk'
    exact Or.inl ⟨bk', hbk', Nat.le_add_right _ _⟩

theorem fsBookStep_update_filter (b : ℕ → Option (FSMultiBook T E)) (sIdx : ℕ)
    (p : (ℕ × Header T × E) → Bool) :
    fsBookStep 0 b (Function.update b sIdx
      (some { (b sIdx).getD {} with fsTrans := ((b sIdx).getD {}).fsTrans.filter p })) := by
  intro idx bk' hbk'
  by_cases hEq : idx = sIdx
  · subst hEq
    rw [Function.update_self, Option.some.injEq] at hbk'
    subst hbk'
    rcases hb : b idx with _ | bk₀
    · exact Or.inr (by simp)
    · exact Or.inl ⟨bk₀, rfl, by simpa using List.length_filter_le p bk₀.fsTrans⟩
  · rw [Function.update_of_ne hEq] at hbk'
    exact Or.inl ⟨bk', hbk', le_rfl⟩

theorem fsBookStep_apply {B q : ℕ} {b0 b1 : ℕ → Option (FSMultiBook T E)}
    (hq1 : q + 1 ≤ B)
    (hInv : ∀ idx bk, b0 idx = some bk → bk.fsTrans.length + (q + 1) ≤ B)
    (hStep : fsBookStep 1 b0 b1) :
    ∀ idx bk', b1 idx = some bk' → bk'.fsTrans.length + q ≤ B := by
  intro idx bk' hbk'
  rcases hStep idx bk' hbk' with ⟨bk₀, hbk₀, hle⟩ | hle
  · have := hInv idx bk₀ hbk₀; omega
  · omega

theorem hooksFSMultiBucketAuth_fsSend_preserve
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t0 : ℕ)
    (ssv : SS ⊕ ℕ) (hdr : Header T) (m : M) (pair : Option (M × M))
    (h : FSMultiBucketAuthState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).fsSend
        ctx P t0 ssv hdr m pair).run h),
      res.2.fTable = h.fTable ∧ res.2.sessions = h.sessions ∧ fsBookStep 1 h.book res.2.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMultiBucketAuth at hmem
  dsimp only at hmem
  rcases ssv with ss | sIdx
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩
    exact ⟨rfl, rfl, fsBookStep_refl 1 rfl⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    have hTail : ∀ (ok : Bool) (h1 : FSMultiBucketAuthState T RSt K I E),
        (h1.fTable = h.fTable ∧ h1.sessions = h.sessions ∧ fsBookStep 0 h.book h1.book) →
        (out, h') ∈ support ((do
          if !ok then return none
          let e? ← (match pair with
            | some (m₀, m₁) =>
              liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.challengeQuery
                (SenderState := SS) (ReceiverState := RS) hdr m₀ m₁)
            | none =>
              liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.transmitQuery
                (SenderState := SS) (ReceiverState := RS) hdr m))
          match e? with
          | none => return none
          | some e =>
            modify fun (s : FSMultiBucketAuthState T RSt K I E) =>
              let b := (s.book sIdx).getD {}
              let cnt' := b.fsCount + 1
              let b' : FSMultiBook T E :=
                { b with fsCount := cnt', fsTrans := (cnt', hdr, e) :: b.fsTrans }
              { s with book := Function.update s.book sIdx (some b') }
            return some ((.inr sIdx : SS ⊕ ℕ), e)).run h1) →
        h'.fTable = h.fTable ∧ h'.sessions = h.sessions ∧ fsBookStep 1 h.book h'.book := by
      intro ok h1 hStep1 hm2
      cases ok
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hm2
        rcases hm2 with ⟨_, hh'⟩
        rw [hh']
        exact ⟨hStep1.1, hStep1.2.1, fsBookStep_mono (Nat.zero_le 1) hStep1.2.2⟩
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          mem_support_bind_iff] at hm2
        obtain ⟨⟨e?, h2⟩, hmQ, hm2⟩ := hm2
        have hh2 : h2 = h1 := by
          rcases pair with _ | ⟨m₀, m₁⟩ <;>
            (simp only [liftFSMultiBucket, StateT.run_lift, mem_support_bind_iff,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmQ;
             rcases hmQ with ⟨_, _, _, hEq⟩; exact hEq)
        dsimp only at hm2
        rw [hh2] at hm2
        rcases e? with _ | e
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm2
          rcases hm2 with ⟨_, hh'⟩
          rw [hh']
          exact ⟨hStep1.1, hStep1.2.1, fsBookStep_mono (Nat.zero_le 1) hStep1.2.2⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm2
          rcases hm2 with ⟨_, hh'⟩
          rw [hh']
          exact ⟨hStep1.1, hStep1.2.1,
            by simpa using fsBookStep_trans hStep1.2.2 (fsBookStep_update_cons h1.book sIdx hdr e)⟩
    rw [mem_support_bind_iff] at hmem
    obtain ⟨⟨ok, h1⟩, hm1, hm2⟩ := hmem
    dsimp only at hm2
    split_ifs at hm1
    · simp only [liftFSMultiBucket, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
        mem_support_bind_iff] at hm1
      obtain ⟨cs?, _, hm1⟩ := hm1
      rcases cs? with _ | ss'
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm1
        rcases hm1 with ⟨hok, hh1⟩
        rw [hok, hh1] at hm2
        exact hTail false h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hm2
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm1
        rcases hm1 with ⟨hok, hh1⟩
        rw [hok, hh1] at hm2
        exact hTail true
          { h with book := Function.update h.book sIdx (some { (h.book sIdx).getD {} with sCorr := true }) }
          ⟨rfl, rfl, fsBookStep_update_sCorr h.book sIdx⟩ hm2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm1
      rcases hm1 with ⟨hok, hh1⟩
      rw [hok, hh1] at hm2
      exact hTail true h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hm2

theorem hooksFSMultiBucketAuth_fsRecv_preserve
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party) (t0 : ℕ)
    (rsv : RS ⊕ ℕ) (hdr : Header T) (e : E) (rec_ : Option (Record M (Header T × E)))
    (h : FSMultiBucketAuthState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).fsRecv
        ctx P t0 rsv hdr e rec_).run h),
      res.2.fTable = h.fTable ∧ res.2.sessions = h.sessions ∧ fsBookStep 0 h.book res.2.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMultiBucketAuth at hmem
  dsimp only at hmem
  rcases rsv with rs | sIdx
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, rfl⟩
    exact ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩
  · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hmem
    set matched : Option (ℕ × Header T × E) :=
      ((h.book sIdx).getD {}).fsTrans.find? (fun x => x.2 == (hdr, e))
    have hTail : ∀ (ok : Bool) (h1 : FSMultiBucketAuthState T RSt K I E),
        (h1.fTable = h.fTable ∧ h1.sessions = h.sessions ∧ fsBookStep 0 h.book h1.book) →
        (out, h') ∈ support ((do
          if !ok then return none
          let res ← (if matched.isSome then
              liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.deliverQuery
                (SenderState := SS) (ReceiverState := RS) hdr e)
            else
              liftFSMultiBucket sIdx (_root_.CryptoGames.FSAEAD.injectQuery
                (SenderState := SS) (ReceiverState := RS) hdr e))
          match res with
          | none => return none
          | some .rejected => return some none
          | some (.accepted i mo') =>
            let s1 ← get
            let bk1 := (s1.book sIdx).getD {}
            if la && matched.isNone && (!bk1.sCorr) && bk1.fsCount < i then
              modify fun (s : FSMultiBucketAuthState T RSt K I E) => { s with lfWin := true }
              return none
            else
              let drop := (matched.map fun (x : ℕ × Header T × E) => x.1).getD i
              modify fun (s : FSMultiBucketAuthState T RSt K I E) =>
                let b : FSMultiBook T E := (s.book sIdx).getD {}
                let b' : FSMultiBook T E :=
                  { b with fsTrans := b.fsTrans.filter fun (x : ℕ × Header T × E) => x.1 != drop }
                { s with book := Function.update s.book sIdx (some b') }
              match mo', rec_ with
              | some m, _ => return some (some ((.inr sIdx : RS ⊕ ℕ), i, m))
              | none, some r => return some (some ((.inr sIdx : RS ⊕ ℕ), i, r.msg))
              | none, none => return none).run h1) →
        h'.fTable = h.fTable ∧ h'.sessions = h.sessions ∧ fsBookStep 0 h.book h'.book := by
      intro ok h1 hStep1 hm2
      cases ok
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq] at hm2
        rcases hm2 with ⟨_, hh'⟩
        rw [hh']; exact hStep1
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          mem_support_bind_iff] at hm2
        obtain ⟨⟨resQ, h2⟩, hmQ, hm2⟩ := hm2
        have hh2 : h2 = h1 := by
          split_ifs at hmQ <;>
            (simp only [liftFSMultiBucket, StateT.run_lift, mem_support_bind_iff,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmQ;
             rcases hmQ with ⟨_, _, _, hEq⟩; exact hEq)
        dsimp only at hm2
        rw [hh2] at hm2
        rcases resQ with _ | (_ | ⟨i, mo'⟩)
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm2
          rcases hm2 with ⟨_, hh'⟩; rw [hh']; exact hStep1
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm2
          rcases hm2 with ⟨_, hh'⟩; rw [hh']; exact hStep1
        · simp only [StateT.run_bind, StateT.run_get, pure_bind] at hm2
          split_ifs at hm2
          · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
              support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm2
            rcases hm2 with ⟨_, hh'⟩; rw [hh']; exact hStep1
          · simp only [StateT.run_bind, StateT.run_modify, pure_bind] at hm2
            rcases mo' with _ | m
            · rcases rec_ with _ | r <;>
                (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm2;
                 rcases hm2 with ⟨_, hh'⟩; rw [hh'];
                 exact ⟨hStep1.1, hStep1.2.1,
                   by simpa using fsBookStep_trans hStep1.2.2 (fsBookStep_update_filter h1.book sIdx _)⟩)
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm2
              rcases hm2 with ⟨_, hh'⟩; rw [hh']
              exact ⟨hStep1.1, hStep1.2.1,
                by simpa using fsBookStep_trans hStep1.2.2 (fsBookStep_update_filter h1.book sIdx _)⟩
    rw [mem_support_bind_iff] at hmem
    obtain ⟨⟨ok, h1⟩, hm1, hm2⟩ := hmem
    dsimp only at hm2
    split_ifs at hm1
    · simp only [liftFSMultiBucket, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
        mem_support_bind_iff] at hm1
      obtain ⟨cs?, _, hm1⟩ := hm1
      rcases cs? with _ | ss'
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm1
        rcases hm1 with ⟨hok, hh1⟩
        rw [hok, hh1] at hm2
        exact hTail false h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hm2
      · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm1
        rcases hm1 with ⟨hok, hh1⟩
        rw [hok, hh1] at hm2
        exact hTail true
          { h with book := Function.update h.book sIdx (some { (h.book sIdx).getD {} with sCorr := true }) }
          ⟨rfl, rfl, fsBookStep_update_sCorr h.book sIdx⟩ hm2
    · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm1
      rcases hm1 with ⟨hok, hh1⟩
      rw [hok, hh1] at hm2
      exact hTail true h ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩ hm2

theorem hooksFSMultiBucketAuth_reveal_preserve
    [DecidableEq T] [DecidableEq I] [DecidableEq E]
    [SampleableType CCoins] [SampleableType I] [SampleableType K]
    (L : ℕ) (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR RSt I K)
    (fs : FSAEADScheme K SS RS (Header T) M E) (Δcka qep : ℕ) (gMain : Bool)
    (tL : Option ℕ) (par la : Bool)
    (ctx : Ctx Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ) M E) (P : Party)
    (vp : VP Γ T RSt (SS ⊕ ℕ) (RS ⊕ ℕ))
    (h : FSMultiBucketAuthState T RSt K I E) :
    ∀ res ∈ support (((hooksFSMultiBucketAuth L cka prng fs Δcka qep gMain tL par la).reveal
        ctx P vp).run h),
      res.2.fTable = h.fTable ∧ res.2.sessions = h.sessions ∧ fsBookStep 0 h.book res.2.book := by
  intro ⟨out, h'⟩ hmem
  unfold hooksFSMultiBucketAuth at hmem
  dsimp only at hmem
  by_cases hEarly : (!gMain && (!(vp.tcur < healEpoch tL) ||
      !(max (ctx.epoch Party.A) (ctx.epoch Party.B) < healEpoch tL))) = true
  · simp only [hEarly, ↓reduceIte, StateT.run_pure, support_pure,
      Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨_, hh'⟩; rw [hh']; exact ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩
  · simp only [Bool.not_eq_true] at hEarly
    simp only [hEarly, Bool.false_eq_true, ↓reduceIte] at hmem
    rw [StateT.run_bind, mem_support_bind_iff] at hmem
    obtain ⟨⟨vS?, h1⟩, hm1, hm2⟩ := hmem
    have hStep1 : h1.fTable = h.fTable ∧ h1.sessions = h.sessions ∧ fsBookStep 0 h.book h1.book := by
      rcases hvS : vp.vS with _ | (ss | sIdx) <;> simp only [hvS] at hm1
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm1
        rcases hm1 with ⟨_, hh1⟩; rw [hh1]; exact ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm1
        rcases hm1 with ⟨_, hh1⟩; rw [hh1]; exact ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩
      · simp only [liftFSMultiBucket, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
          mem_support_bind_iff] at hm1
        obtain ⟨cs?, _, hm1⟩ := hm1
        rcases cs? with _ | ss'
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm1
          rcases hm1 with ⟨_, hh1⟩; rw [hh1]; exact ⟨rfl, rfl, fsBookStep_refl 0 rfl⟩
        · simp only [StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind,
            support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm1
          rcases hm1 with ⟨_, hh1⟩; rw [hh1]
          exact ⟨rfl, rfl, fsBookStep_update_sCorr h.book sIdx⟩
    dsimp only at hm2
    rcases vS? with _ | ssReal
    · dsimp only at hm2
      simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm2
      rcases hm2 with ⟨_, hh'⟩; rw [hh']; exact hStep1
    · dsimp only at hm2
      split_ifs at hm2 <;>
        (simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hm2;
         rcases hm2 with ⟨_, hh'⟩; rw [hh']; exact hStep1)

end BucketEvalBridge

end

end Computational.Proofs.SessionCostedFig8.BucketFSAuthShallowBase
