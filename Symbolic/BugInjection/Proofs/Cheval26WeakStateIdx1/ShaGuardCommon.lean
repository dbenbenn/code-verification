/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.ElfBinding
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard
public import Symbolic.Proofs.Refinement.Composed.Cli.Model
public import Symbolic.Proofs.Refinement.Composed.Cli.SDet.Defs

/-!
# Shared Helpers for `Cheval26WeakStateIdx1.ShaGuard`

Shared structural definitions and equality-reflection lemmas used across the split
`ShaGuard*` witness modules for `Cheval26WeakStateIdx1Cli`.
-/

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuardCommon

open Arm64 (FsPath normalizePath)
open CryptoGames.HKDF (bytesToKey32)
open CryptoGames.LibsignalSession (SessionState SignalMessage initializeRecipientSession)
open CryptoVerification.E2E (
  LocalIdentity PEParams PreKeyMessageFields ResponderPreKeySecrets acceptInput djbKey
  keyPairOf ofU8 pqxdhSpqrSession
)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.SignalSession (
  PqParty bundleDir coinsFile filesOf markKyberUsed preKeysNamedBy
)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed.Refinement (parsePreKey)
open DY.Libsignal.Composed.Refinement.Cli (InputsEquiv)
open DY.Libsignal.Composed.Refinement.Cli.ElfGuard (preKeyOfBody?)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace (
  FileList c3In c6In coins6 evalFileList filesOf_eq_evalFileList foldStep isCliFilePath
  sameEvalFileList validFileList wsBob0 wsBob3 wsBundle wsMsg3
)
open Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard (
  checkRecvPrekeyEqAt dummyX modelPrimsFast optEqBool pqxdhSessionParamsFast prodEqBool
  recvPrekeyCoreFast sessionStateEqBool
)

@[expose] public section

set_option autoImplicit false

theorem foldStep_eq_none_of_not_match {l : FileList} {np : FsPath}
    (h : ∀ x ∈ l, (np == normalizePath x.1) = false) : l.foldl (foldStep np) none = none := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    rw [List.foldl_cons]; unfold foldStep; rw [h x (List.mem_cons_self ..)]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem evalFileList_eq_of_sameEvalFileList {l1 l2 : FileList}
    (hsame : sameEvalFileList l1 l2 = true) (p : String) :
    evalFileList l1 p = evalFileList l2 p := by
  unfold sameEvalFileList at hsame
  obtain ⟨ha1, ha2⟩ := (Bool.and_eq_true _ _).mp hsame
  by_cases hm1 : ∃ x ∈ l1, normalizePath x.1 = normalizePath p
  · obtain ⟨x, hx, hnx⟩ := hm1
    have hev := beq_iff_eq.mp (List.all_eq_true.mp ha1 x hx)
    unfold evalFileList at hev ⊢
    rwa [← hnx]
  · by_cases hm2 : ∃ x ∈ l2, normalizePath x.1 = normalizePath p
    · obtain ⟨x, hx, hnx⟩ := hm2
      have hev := beq_iff_eq.mp (List.all_eq_true.mp ha2 x hx)
      unfold evalFileList at hev ⊢
      rwa [← hnx]
    · unfold evalFileList
      rw [foldStep_eq_none_of_not_match (fun x hx => beq_eq_false_iff_ne.mpr fun h => hm1 ⟨x, hx, h.symm⟩),
          foldStep_eq_none_of_not_match (fun x hx => beq_eq_false_iff_ne.mpr fun h => hm2 ⟨x, hx, h.symm⟩)]

theorem filesOf_append_eq_of_sameEvalFileList {l1 l2 extra : FileList}
    (hl1 : l1.all (fun x => isCliFilePath x.1) = true)
    (hl2 : l2.all (fun x => isCliFilePath x.1) = true)
    (hex : extra.all (fun x => isCliFilePath x.1) = true)
    (hsame : sameEvalFileList l1 l2 = true) (p : String) :
    filesOf (l1 ++ extra) p = filesOf (l2 ++ extra) p := by
  have hl1' : (l1 ++ extra).all (fun x => isCliFilePath x.1) = true := by
    rw [List.all_append, hl1, hex]; rfl
  have hl2' : (l2 ++ extra).all (fun x => isCliFilePath x.1) = true := by
    rw [List.all_append, hl2, hex]; rfl
  rw [filesOf_eq_evalFileList hl1', filesOf_eq_evalFileList hl2']
  unfold evalFileList
  rw [List.foldl_append, List.foldl_append]
  exact congrArg (fun v => extra.foldl _ v) (evalFileList_eq_of_sameEvalFileList hsame p)

theorem validFileList_paths {l : FileList} (h : validFileList l = true) :
    l.all (fun x => isCliFilePath x.1) = true :=
  List.all_eq_true.mpr fun x hx => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h x hx)).1

theorem validFileList_filter {l : FileList} (pred : (String × HwBytes) → Bool)
    (h : validFileList l = true) : validFileList (l.filter pred) = true :=
  List.all_eq_true.mpr fun x hx => List.all_eq_true.mp h x (List.mem_of_mem_filter hx)

theorem coinsExtra_paths (c : HwBytes) :
    ([(coinsFile, c)] : FileList).all (fun x => isCliFilePath x.1) = true := by
  have h : isCliFilePath coinsFile = true := by decide +kernel
  simp [h]

theorem bundleCoinsExtra_paths (c : HwBytes) :
    (wsBundle.files bundleDir ++ [(coinsFile, c)]).all (fun x => isCliFilePath x.1) = true := by
  have hb : (wsBundle.files bundleDir).all (fun x => isCliFilePath x.1) = true := by decide +kernel
  rw [List.all_append, hb, coinsExtra_paths c]; rfl

theorem inputsEquiv_of_eq {i j j' : CryptoVerification.SignalSession.Inputs}
    (hj : j = j') (h : InputsEquiv i j') : InputsEquiv i j :=
  ⟨h.1.trans (congrArg CryptoVerification.SignalSession.Inputs.argv hj.symm),
   h.2.1.trans (congrArg CryptoVerification.SignalSession.Inputs.dirs hj.symm),
   h.2.2.1.trans (congrArg CryptoVerification.SignalSession.Inputs.stdin hj.symm),
   fun p => (h.2.2.2 p).trans
     (congrArg (fun x => filesOf x.files p) hj.symm)⟩

theorem encodeDirFast_eq_ws (W : CryptoVerification.E2E.PEParams)
    (st : CryptoVerification.SignalSession.PqParty) :
    Symbolic.BugInjection.Proofs.CliExec.CompHooks0Guard.encodeDirFast W st =
      Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace.encodeDirFast W st :=
  rfl

def drKeyEqBool (a b : SignalPqxdh.DRKey) : Bool :=
  (a.rootKey == b.rootKey) && (a.chainKey == b.chainKey) && (a.pqrKey == b.pqrKey)

theorem eq_of_drKeyOptEq {o1 o2 : Option SignalPqxdh.DRKey}
    (h : optEqBool drKeyEqBool o1 o2 = true) : o1 = o2 := by
  cases o1 <;> cases o2 <;> try cases h
  · rfl
  · rename_i a b; cases a; cases b
    dsimp only [optEqBool, drKeyEqBool] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, h.1.2, h.2]

def recvDkAt (W : PEParams) (st₀ : PqParty) (m : PreKeyMessageFields) :
    Option SignalPqxdh.DRKey :=
  match preKeysNamedBy st₀ m, SignalMessage.tryFrom protoSignalCodec m.inner with
  | some k, .ok _ =>
    if (m.spkId != k.spkId) || (m.kpkId != k.kpkId) then none
    else SignalPqxdh.Model.acceptKeys (modelPrimsFast dummyX W) (acceptInput W st₀.me k m)
  | _, _ => none

def recvWithDkAt (W : PEParams) (st₀ : PqParty) (m : PreKeyMessageFields)
    (rc : BitVec 256) (dkOpt : Option SignalPqxdh.DRKey) :
    Option (Option (Option (HwBytes × SessionState HwBytes))) :=
  (preKeysNamedBy st₀ m).map fun k =>
    match SignalMessage.tryFrom protoSignalCodec m.inner with
    | .error _ => some none
    | .ok inner =>
      if (m.spkId != k.spkId) || (m.kpkId != k.kpkId) then some none
      else match dkOpt with
        | none => some none
        | some dk =>
          let st0 : SessionState HwBytes := initializeRecipientSession (pqxdhSpqrSession W)
            ⟨(keyPairOf W.C st₀.me.idPriv).publicKey⟩ ⟨⟨m.idPub⟩⟩ (keyPairOf W.C k.spkPriv)
            (bytesToKey32 (ofU8 dk.rootKey)) (bytesToKey32 (ofU8 dk.chainKey))
            (bytesToKey32 (ofU8 dk.pqrKey))
          match SessionState.tryDecryptFromRecord W.C (pqxdhSpqrSession W)
              ((pqxdhSessionParamsFast W).expectedAddrs st₀.party) inner .preKey rc st0 with
          | (.ok pt, st) => some (some (pt, st)) | (.error .panic, _) => none
          | (.error _, _) => some none

theorem recvMap_eq_recvWithDkAt (W : PEParams) (st₀ : PqParty)
    (m : PreKeyMessageFields) (rc : BitVec 256) :
    ((preKeysNamedBy st₀ m).map fun k => recvPrekeyCoreFast dummyX W st₀.party st₀.me k m rc) =
      recvWithDkAt W st₀ m rc (recvDkAt W st₀ m) := by
  unfold recvWithDkAt recvDkAt recvPrekeyCoreFast
  cases preKeysNamedBy st₀ m with
  | none => rfl
  | some k =>
    dsimp only [Option.map]
    cases SignalMessage.tryFrom protoSignalCodec m.inner with
    | error _ => rfl
    | ok _ =>
      dsimp only
      cases (m.spkId != k.spkId) || (m.kpkId != k.kpkId) <;> rfl

theorem checkRecvPrekeyEqAt_of_split {W₁ W₂ : PEParams} {st₀ : PqParty}
    {m : PreKeyMessageFields} {rc : BitVec 256}
    (hdk : optEqBool drKeyEqBool (recvDkAt W₁ st₀ m) (recvDkAt W₂ st₀ m) = true)
    (htail :
      let dkOpt := recvDkAt W₁ st₀ m
      optEqBool (optEqBool (optEqBool (prodEqBool (fun x y => x == y) sessionStateEqBool)))
        (recvWithDkAt W₁ st₀ m rc dkOpt)
        (recvWithDkAt W₂ st₀ m rc dkOpt) = true) :
    checkRecvPrekeyEqAt W₁ W₂ st₀ m rc = true := by
  unfold checkRecvPrekeyEqAt
  rw [recvMap_eq_recvWithDkAt W₁, recvMap_eq_recvWithDkAt W₂, ← eq_of_drKeyOptEq hdk]
  exact htail

def localIdEqBool (a b : LocalIdentity) : Bool :=
  (a.idPriv.toList == b.idPriv.toList) && (a.regId == b.regId)

theorem eq_of_localIdEqBool {a b : LocalIdentity} (h : localIdEqBool a b = true) : a = b := by
  cases a; cases b
  dsimp only [localIdEqBool] at h; simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact congrArg₂ LocalIdentity.mk (List.Vector.eq _ _ h.1) h.2

def respSecretsEqBool (a b : ResponderPreKeySecrets) : Bool :=
  (a.spkId == b.spkId) && (a.spkPriv.toList == b.spkPriv.toList) &&
  (a.kpkId == b.kpkId) && (a.kpkPub.toList == b.kpkPub.toList) &&
  (a.kpkSec.toList == b.kpkSec.toList) &&
  optEqBool (prodEqBool (· == ·) (fun x y => x.toList == y.toList)) a.opk b.opk

theorem eq_of_respSecretsOptEq {o1 o2 : Option ResponderPreKeySecrets}
    (h : optEqBool respSecretsEqBool o1 o2 = true) : o1 = o2 := by
  cases o1 <;> cases o2 <;> try cases h
  · rfl
  · rename_i a b; cases a with | mk s1 sp1 k1 kp1 ks1 op1 => cases b with | mk s2 sp2 k2 kp2 ks2 op2 =>
    dsimp only [optEqBool, respSecretsEqBool] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    have hop : op1 = op2 := by
      cases op1 <;> cases op2 <;> try cases h6
      · rfl
      · rename_i p1 p2; cases p1; cases p2
        dsimp only [optEqBool, prodEqBool] at h6
        simp only [Bool.and_eq_true, beq_iff_eq] at h6
        exact congrArg Option.some (congrArg₂ Prod.mk h6.1 (List.Vector.eq _ _ h6.2))
    rw [h1, List.Vector.eq _ _ h2, h3, List.Vector.eq _ _ h4, List.Vector.eq _ _ h5, hop]

theorem checkRecvPrekeyEqAt_congr_st {W₁ W₂ : PEParams} {st₁ st₂ : PqParty}
    {m : PreKeyMessageFields} {rc : BitVec 256}
    (h : ((st₁.party == st₂.party) && localIdEqBool st₁.me st₂.me &&
          optEqBool respSecretsEqBool (preKeysNamedBy st₁ m) (preKeysNamedBy st₂ m)) = true) :
    checkRecvPrekeyEqAt W₁ W₂ st₁ m rc = checkRecvPrekeyEqAt W₁ W₂ st₂ m rc := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  unfold checkRecvPrekeyEqAt
  rw [h.1.1, eq_of_localIdEqBool h.1.2, eq_of_respSecretsOptEq h.2]

def wsBody3 : HwBytes := c3In.drop 1
def wsBody6 : HwBytes := c6In.drop 1
def wsRc6 : BitVec 256 := bytesToKey32 coins6
def wsMsg6 : PreKeyMessageFields := (preKeyOfBody? wsBody6).getD wsMsg3

def wsBob3NoSess : PqParty :=
  { (markKyberUsed wsBob0 wsMsg3).getD wsBob0 with
    peerId := some ⟨⟨wsMsg3.idPub⟩⟩, session := none }

def checkWs6NonMatch : Bool :=
  match wsBob3.session, parsePreKey wsBody6 with
  | some (x₀, _), some q₀ =>
      (x₀.aliceBaseKey != djbKey wsMsg6.baseKey) &&
      (x₀.aliceBaseKey != q₀.baseKey.take 33)
  | _, _ => false

theorem of_checkWs6NonMatch (h : checkWs6NonMatch = true) :
    ∃ x₀ g₀ q₀, wsBob3.session = some (x₀, g₀) ∧ parsePreKey wsBody6 = some q₀ ∧
      x₀.aliceBaseKey ≠ djbKey wsMsg6.baseKey ∧ x₀.aliceBaseKey ≠ q₀.baseKey.take 33 := by
  unfold checkWs6NonMatch at h
  cases hs : wsBob3.session with
  | none => rw [hs] at h; cases h
  | some xg =>
    rcases xg with ⟨x₀, g₀⟩
    cases hq : parsePreKey wsBody6 with
    | none => rw [hs, hq] at h; cases h
    | some q₀ =>
      rw [hs, hq] at h; simp only [Bool.and_eq_true, bne_iff_ne] at h
      exact ⟨x₀, g₀, q₀, rfl, rfl, h.1, h.2⟩

end

end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ShaGuardCommon
