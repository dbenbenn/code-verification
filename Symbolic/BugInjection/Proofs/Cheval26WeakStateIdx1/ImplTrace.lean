/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv35
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtPrefixInv38
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.Wire80
import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.CompRSchedBSeedPins

/-!
# 7-Call Weak-State CLI Implementation Trace Helpers

Provides precompiled wire/input constants, filesystem snapshot normalization (`filesOf_eq_evalFileList`,
`ValidStepFiles`), concrete 7-call inputs/outputs (`wsInp0`..`wsInp6`, `wsOut0`..`wsOut6`), and
`preKeyNoMatch_call6_of_files3` for `ImplTracePlaced` and the `WeakState` implementation disproof.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.ImplTrace

open Arm64 (FsPath FsEntry FsState normalizePath)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY (Participant)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup EligibleForSessionPromotion ecKey kyberKey clamp parsePreKeyWire
   recordBytes bytesField msgField u32Field chainBytes)
open DY.Libsignal.Refinement (encodeField paddedVarint)
open DY.Libsignal.Composed.Refinement.Cli
  (CliCall CliTurn DirectorySnapshot PreKeyNoMatch InvertsGuarded aliceUuid bobUuid
   peerOf peerNameOf sessionPathOf)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open CryptoVerification.RecordCodecs (IdentityKeyPairStructure SignedPreKeyRecordStructure)
open CryptoVerification.SignalSession
  (Inputs Outcome PublicBundle Address filesOf fsView stdioPaths partyDirs bundleDir coinsFile
   addressFile identityKeyPairFile registrationIdFile identityFile sessionFile le32)
open Symbolic.BugInjection (PQXDHSpqrSetup hexBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compLookupPub)

abbrev FileList := List (String × HwBytes)

abbrev wsSetup : PQXDHSpqrSetup := Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.setup
abbrev wsTrace : List CliEvent := Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1Cli.trace

def rawRunAt (k : Nat) : RunEvent := match wsTrace[k]? with
  | some (.run ev) => ev | _ => { party := "", cmd := .send ⟨"", 0⟩, input := [], coins := [], exit := none }
def rawExitOutAt (k : Nat) : HwBytes := match (rawRunAt k).exit with | some (_, out) => out | none => []
private theorem rawExitOutAt_of_some {k : Nat} {c : Nat} {out : HwBytes}
    (h : (rawRunAt k).exit = some (c, out)) : rawExitOutAt k = out := by
  unfold rawExitOutAt; rw [h]

def hexBytesChars (cs : List Char) : HwBytes :=
  Symbolic.BugInjection.hexBytes.go
    (fun c => if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10) cs
theorem hexBytes_eq_hexBytesChars (s : String) : hexBytes s = hexBytesChars s.toList := rfl

attribute [local irreducible] Symbolic.BugInjection.hexBytes

private theorem hexBytes_of_ofList (s : String) (cs : List Char) (bs : HwBytes)
    (hs : s = String.ofList cs) (hb : hexBytesChars cs = bs) : hexBytes s = bs := by
  rw [hexBytes_eq_hexBytesChars, hs, String.toList_ofList, hb]

section FastHex
open Lean Meta Elab Command

private meta def hexDigitVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

private meta def parseHexStr (s : String) : List UInt8 :=
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (16 * hexDigitVal a + hexDigitVal b) :: go rest | _ => []
  go s.toList

private meta def buildByteListExpr (s : String) : Expr := Id.run do
  let bv8Ty := mkApp (mkConst ``BitVec) (mkNatLit 8)
  let mut bsExpr := mkApp (mkConst ``List.nil [0]) bv8Ty
  for b in (parseHexStr s).reverse do
    bsExpr := mkApp3 (mkConst ``List.cons [0]) bv8Ty
      (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit b.toNat)) bsExpr
  return bsExpr

private meta def precompiledStrEqs : List Name :=
  [ ``PtPrefixInv35.bundle0Str_eq, ``PtPrefixInv38.wire37Str_eq, ``SpecTop.recv40Str_eq,
    ``SpecTop.recv81Str_eq, ``Wire80.wire80Str_eq, ``CompRSchedBSeedPins.schedBCall1SendStr_eq,
    ``CompRSchedBSeedPins.schedBCall2SendStr_eq, ``CompRSchedBSeedPins.schedBCall5SendStr_eq,
    ``CompRSchedBSeedPins.schedBCall6RecvStr_eq ]

private meta def findPrecompiledStrEq (s : String) : MetaM (Option (Expr × Expr)) := do
  for nm in precompiledStrEqs do
    let ty := (← getConstInfo nm).type
    if ty.isAppOfArity ``Eq 3 then
      if let .lit (.strVal candS) := ty.getAppArgs[1]! then
        let rhs := ty.getAppArgs[2]!
        if candS == s && rhs.isAppOfArity ``String.ofList 1 then
          return some (rhs.getAppArgs[0]!, mkConst nm)
  return none

private meta def buildFastHexProof (s : String) (defConst : Expr) : MetaM Expr := do
  let charTy := mkConst ``Char; let strTy := mkConst ``String
  let listBv8Ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``BitVec) (mkNatLit 8))
  let sLit := mkStrLit s; let hbPrf := mkApp2 (mkConst ``Eq.refl [1]) listBv8Ty defConst
  if let some (csConst, hsPrf) ← findPrecompiledStrEq s then
    return mkApp5 (mkConst ``hexBytes_of_ofList) sLit csConst defConst hsPrf hbPrf
  if s.length > 512 then throwError "no precompiled Str_eq matches string of length {s.length}"
  let mut csExpr := mkApp (mkConst ``List.nil [0]) charTy
  for c in s.toList.reverse do csExpr := mkApp3 (mkConst ``List.cons [0]) charTy (toExpr c) csExpr
  let hsPrf := mkApp2 (mkConst ``Eq.refl [1]) strTy sLit
  return mkApp5 (mkConst ``hexBytes_of_ofList) sLit csExpr defConst hsPrf hbPrf

local elab "fast_hex_bytes " rhs:term : term => do
  let listBv8Ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``BitVec) (mkNatLit 8))
  let rhsExpr ← instantiateMVars (← Term.elabTermEnsuringType rhs listBv8Ty)
  let .lit (.strVal s) ← whnf (← whnf rhsExpr).getAppArgs[0]! | throwError "expected hex string literal"
  return buildByteListExpr s

local elab "def_fast_hex_eq " thmId:ident " : " rhs:term " := " defId:ident : command => do
  liftTermElabM do
    let listBv8Ty := mkApp (mkConst ``List [0]) (mkApp (mkConst ``BitVec) (mkNatLit 8))
    let rhsExpr ← instantiateMVars (← Term.elabTermEnsuringType rhs listBv8Ty)
    let defConst := mkConst (← realizeGlobalConstNoOverloadWithInfo defId)
    let .lit (.strVal s) ← whnf (← whnf rhsExpr).getAppArgs[0]! | throwError "expected hex string literal"
    let hexStrExpr := mkApp (mkConst ``Symbolic.BugInjection.hexBytes) (mkStrLit s)
    let eqEv ← if rhsExpr.isAppOfArity ``rawExitOutAt 1 then
        let kExpr := rhsExpr.getAppArgs[0]!
        let hExit ← mkEqRefl (mkProj ``RunEvent 4 (mkApp (mkConst ``rawRunAt) kExpr))
        pure <| mkApp4 (mkConst ``rawExitOutAt_of_some) kExpr (mkNatLit 0) hexStrExpr hExit
      else pure <| mkApp2 (mkConst ``Eq.refl [1]) listBv8Ty rhsExpr
    let eqHexGo ← buildFastHexProof s defConst
    let fullPrf := mkAppN (mkConst ``Eq.trans [1]) #[listBv8Ty, rhsExpr, hexStrExpr, defConst, eqEv, eqHexGo]
    let declName := (← getCurrNamespace) ++ thmId.getId
    let fullTy := mkApp3 (mkConst ``Eq [1]) listBv8Ty rhsExpr defConst
    addDecl <| .thmDecl { name := declName, levelParams := [], type := fullTy, value := fullPrf }

def c0InFast : HwBytes := fast_hex_bytes (rawRunAt 0).input
def coins0 : HwBytes := fast_hex_bytes (rawRunAt 0).coins
def pt1 : HwBytes := fast_hex_bytes (rawRunAt 1).input
def coins1 : HwBytes := fast_hex_bytes (rawRunAt 1).coins
def c1Out : HwBytes := fast_hex_bytes (rawExitOutAt 1)
def pt2 : HwBytes := fast_hex_bytes (rawRunAt 2).input
def coins2 : HwBytes := fast_hex_bytes (rawRunAt 2).coins
def c2Out : HwBytes := fast_hex_bytes (rawExitOutAt 2)
def c3In : HwBytes := fast_hex_bytes (rawRunAt 3).input
def coins3 : HwBytes := fast_hex_bytes (rawRunAt 3).coins
def pt3Out : HwBytes := fast_hex_bytes (rawExitOutAt 3)
def c4InFast : HwBytes := fast_hex_bytes (rawRunAt 4).input
def coins4 : HwBytes := fast_hex_bytes (rawRunAt 4).coins
def pt5 : HwBytes := fast_hex_bytes (rawRunAt 5).input
def coins5 : HwBytes := fast_hex_bytes (rawRunAt 5).coins
def c5Out : HwBytes := fast_hex_bytes (rawExitOutAt 5)
def c6In : HwBytes := fast_hex_bytes (rawRunAt 6).input
def coins6 : HwBytes := fast_hex_bytes (rawRunAt 6).coins
def pt6Out : HwBytes := fast_hex_bytes (rawExitOutAt 6)
def nilBytes : HwBytes := []
set_option maxRecDepth 20000
def_fast_hex_eq rawRun0_in_eq : (rawRunAt 0).input := c0InFast
def_fast_hex_eq rawRun0_coins_eq : (rawRunAt 0).coins := coins0
def_fast_hex_eq rawRun0_out_eq : rawExitOutAt 0 := nilBytes
def_fast_hex_eq rawRun1_in_eq : (rawRunAt 1).input := pt1
def_fast_hex_eq rawRun1_coins_eq : (rawRunAt 1).coins := coins1
def_fast_hex_eq rawRun1_out_eq : rawExitOutAt 1 := c1Out
def_fast_hex_eq rawRun2_in_eq : (rawRunAt 2).input := pt2
def_fast_hex_eq rawRun2_coins_eq : (rawRunAt 2).coins := coins2
def_fast_hex_eq rawRun2_out_eq : rawExitOutAt 2 := c2Out
def_fast_hex_eq rawRun3_in_eq : (rawRunAt 3).input := c3In
def_fast_hex_eq rawRun3_coins_eq : (rawRunAt 3).coins := coins3
def_fast_hex_eq rawRun3_out_eq : rawExitOutAt 3 := pt3Out
def_fast_hex_eq rawRun4_in_eq : (rawRunAt 4).input := c4InFast
def_fast_hex_eq rawRun4_coins_eq : (rawRunAt 4).coins := coins4
def_fast_hex_eq rawRun4_out_eq : rawExitOutAt 4 := nilBytes
def_fast_hex_eq rawRun5_in_eq : (rawRunAt 5).input := pt5
def_fast_hex_eq rawRun5_coins_eq : (rawRunAt 5).coins := coins5
def_fast_hex_eq rawRun5_out_eq : rawExitOutAt 5 := c5Out
def_fast_hex_eq rawRun6_in_eq : (rawRunAt 6).input := c6In
def_fast_hex_eq rawRun6_coins_eq : (rawRunAt 6).coins := coins6
def_fast_hex_eq rawRun6_out_eq : rawExitOutAt 6 := pt6Out
end FastHex

def noInvertEvent : CliEvent → Bool | .env (.invertDH ..) | .env (.invertKEM ..) => false | _ => true

theorem invertsGuarded_of_noInverts {interp : ExternInterpretation} {r : ProtocolSetup}
    {evs : List CliEvent} (h : evs.all noInvertEvent = true) : InvertsGuarded interp r evs := by
  intro pre post e heq
  have hok := List.all_eq_true.mp h (.env e) (by rw [heq]; simp)
  cases e <;> simp [noInvertEvent] at hok ⊢

theorem wsTrace_invertsGuarded (r : ProtocolSetup) : InvertsGuarded compI0 r wsTrace :=
  invertsGuarded_of_noInverts (by decide +kernel)

def cliDirPaths : List FsPath := partyDirs.map normalizePath ++ [[bundleDir]]

def isCliFilePath (p : String) : Bool :=
  let np := normalizePath p
  !np.isEmpty && !(stdioPaths.map normalizePath).contains np && !cliDirPaths.contains np &&
    ((FsPath.nonEmptyPrefixes np).dropLast).all (fun pref => cliDirPaths.contains pref) &&
    !Arm64.hasLeadingSlash p && !Arm64.hasDotDot p

def validFileList (l : FileList) : Bool := l.all (fun x => isCliFilePath x.1 && decide (x.2.length < 2 ^ 31))
def foldStep (np : FsPath) (acc : Option HwBytes) (x : String × HwBytes) : Option HwBytes :=
  if np == normalizePath x.1 then some x.2 else acc
def evalFileList (l : FileList) (p : String) : Option HwBytes := l.foldl (foldStep (normalizePath p)) none

private def entryFileBytes : Option FsEntry → Option HwBytes | some (.file bs) => some bs | _ => none
private def fsStepFile (fs : FsState) (x : String × HwBytes) : FsState :=
  (((FsPath.nonEmptyPrefixes (normalizePath x.1)).dropLast).foldl
    (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile x.1 (some (.file x.2))

private theorem setDir_foldl_nonFile {ancs : List FsPath} {np : FsPath} (fs : FsState)
    (h0 : entryFileBytes (fs.entries np) = none) :
    entryFileBytes ((ancs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries np) = none := by
  induction ancs generalizing fs with
  | nil => exact h0
  | cons a rest ih => apply ih; unfold FsState.setEntry; dsimp only; split <;> [rfl; exact h0]

private theorem setDir_foldl_outside {ancs : List FsPath} {np : FsPath} (fs : FsState)
    (hancs : ∀ pref ∈ ancs, pref ∈ cliDirPaths) (hnp : np ∉ cliDirPaths) :
    (ancs.foldl (fun acc pref => acc.setEntry pref (some .dir)) fs).entries np = fs.entries np := by
  induction ancs generalizing fs with
  | nil => rfl
  | cons a rest ih =>
    have ha : a ∈ cliDirPaths := hancs a (List.mem_cons_self ..)
    have hne : (np == a) = false := beq_eq_false_iff_ne.mpr (fun h => hnp (h ▸ ha))
    have hstep : (fs.setEntry a (some .dir)).entries np = fs.entries np := by
      unfold FsState.setEntry; dsimp only; rw [hne]; rfl
    rw [List.foldl_cons, ih _ (fun p hp => hancs p (List.mem_cons_of_mem a hp)), hstep]

private theorem isCliFilePath_props {p : String} (h : isCliFilePath p = true) :
    normalizePath p ≠ [] ∧ normalizePath p ∉ stdioPaths.map normalizePath ∧
    normalizePath p ∉ cliDirPaths ∧
    (∀ pref ∈ (FsPath.nonEmptyPrefixes (normalizePath p)).dropLast, pref ∈ cliDirPaths) ∧
    Arm64.hasLeadingSlash p = false ∧ Arm64.hasDotDot p = false := by
  unfold isCliFilePath at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
    decide_eq_true_eq, List.all_eq_true] at h
  exact ⟨(fun hemp => by rw [hemp] at h; cases h.1.1.1.1.1), h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

private theorem foldl_fsStepFile_nonFile {l : FileList} {np : FsPath} (fs : FsState)
    (hl : ∀ x ∈ l, isCliFilePath x.1 = true) (hnp : np = [] ∨ np ∈ cliDirPaths)
    (h0 : entryFileBytes (fs.entries np) = none) :
    entryFileBytes ((l.foldl fsStepFile fs).entries np) = none := by
  induction l generalizing fs with
  | nil => exact h0
  | cons x rest ih =>
    obtain ⟨hne_nil, _, hnot_dir, _⟩ := isCliFilePath_props (hl x (List.mem_cons_self ..))
    have hne : (np == normalizePath x.1) = false := beq_eq_false_iff_ne.mpr fun heq =>
      hnp.elim (fun h => hne_nil (heq.symm.trans h)) (fun hdir => hnot_dir (heq ▸ hdir))
    apply ih _ (fun y hy => hl y (List.mem_cons_of_mem x hy))
    unfold fsStepFile FsState.setFile; rw [FsState.setEntry]; dsimp only; rw [hne]
    exact setDir_foldl_nonFile fs h0

private theorem foldl_fsStepFile_file {l : FileList} {np : FsPath} (fs : FsState) (acc : Option HwBytes)
    (hl : ∀ x ∈ l, isCliFilePath x.1 = true) (hnot_dir : np ∉ cliDirPaths)
    (h0 : entryFileBytes (fs.entries np) = acc) :
    entryFileBytes ((l.foldl fsStepFile fs).entries np) = l.foldl (foldStep np) acc := by
  induction l generalizing fs acc with
  | nil => exact h0
  | cons x rest ih =>
    have hanc_eq := setDir_foldl_outside fs (isCliFilePath_props (hl x (List.mem_cons_self ..))).2.2.2.1 hnot_dir
    have hstep : entryFileBytes ((fsStepFile fs x).entries np) = foldStep np acc x := by
      unfold fsStepFile FsState.setFile; rw [FsState.setEntry]; dsimp only; unfold foldStep
      split <;> [rfl; rw [hanc_eq, h0]]
    exact ih (fsStepFile fs x) _ (fun y hy => hl y (List.mem_cons_of_mem x hy)) hstep

private theorem foldStep_eq_none_of_not_match {l : FileList} {np : FsPath}
    (h : ∀ x ∈ l, (np == normalizePath x.1) = false) : l.foldl (foldStep np) none = none := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
    rw [List.foldl_cons]; unfold foldStep; rw [h x (List.mem_cons_self ..)]
    exact ih (fun y hy => h y (List.mem_cons_of_mem x hy))

theorem filesOf_eq_evalFileList {l : FileList}
    (hl : l.all (fun x => isCliFilePath x.1) = true) (p : String) : filesOf l p = evalFileList l p := by
  have hall : ∀ x ∈ l, isCliFilePath x.1 = true := fun x hx => List.all_eq_true.mp hl x hx
  unfold filesOf fsView Arm64.Process.initFsState evalFileList
  dsimp only [FsState.files, FsState.getEntry, FsState.setFd]
  by_cases hstd : normalizePath p ∈ stdioPaths.map normalizePath
  · simp only [hstd, ↓reduceIte]; exact (foldStep_eq_none_of_not_match fun x hx =>
      beq_eq_false_iff_ne.mpr fun heq => (isCliFilePath_props (hall x hx)).2.1 (heq ▸ hstd)).symm
  · simp only [hstd, ↓reduceIte]; by_cases hemp : (normalizePath p).isEmpty = true
    · simp only [hemp, ↓reduceIte]; have hnil : normalizePath p = [] := List.isEmpty_iff.mp hemp
      exact (foldStep_eq_none_of_not_match fun x hx =>
        beq_eq_false_iff_ne.mpr fun heq => (isCliFilePath_props (hall x hx)).1 (heq.symm.trans hnil)).symm
    · simp only [hemp, Bool.false_eq_true, ↓reduceIte]
      have hempty_init : entryFileBytes (({} : FsState).entries (normalizePath p)) = none := by
        show entryFileBytes (if (normalizePath p).isEmpty then some .dir else none) = none
        simp [hemp, entryFileBytes]
      by_cases hdir : normalizePath p ∈ cliDirPaths
      · have lhs_none := foldl_fsStepFile_nonFile ({} : FsState) hall (Or.inr hdir) hempty_init
        have rhs_none := foldStep_eq_none_of_not_match fun x hx =>
          beq_eq_false_iff_ne.mpr fun heq => (isCliFilePath_props (hall x hx)).2.2.1 (heq ▸ hdir)
        change entryFileBytes ((l.foldl fsStepFile ({} : FsState)).entries (normalizePath p)) = _
        rw [lhs_none, rhs_none]
      · change entryFileBytes ((l.foldl fsStepFile ({} : FsState)).entries (normalizePath p)) = _
        exact foldl_fsStepFile_file ({} : FsState) none hall hdir hempty_init

private theorem validFileList_paths {l : FileList} (h : validFileList l = true) :
    l.all (fun x => isCliFilePath x.1) = true :=
  List.all_eq_true.mpr fun x hx => ((Bool.and_eq_true _ _).mp (List.all_eq_true.mp h x hx)).1

private theorem validFileList_filter {l : FileList} (pred : (String × HwBytes) → Bool)
    (h : validFileList l = true) : validFileList (l.filter pred) = true :=
  List.all_eq_true.mpr fun x hx => List.all_eq_true.mp h x (List.mem_of_mem_filter hx)

def scrubPred (np : FsPath) : Bool := (np == normalizePath coinsFile) || (np.head? == some bundleDir)
def scrubList (l : FileList) : FileList := l.filter (fun x => !scrubPred (normalizePath x.1))
def clearSessionList (sessPath : String) (l : FileList) : FileList :=
  l.filter (fun x => !(normalizePath x.1 == normalizePath sessPath))

private theorem scrubList_valid {l : FileList} (h : validFileList l = true) :
    validFileList (scrubList l) = true := validFileList_filter (fun x => !scrubPred (normalizePath x.1)) h

def mkInpArgv (argv : List String) (c : CliCall) (base : FileList) : Inputs :=
  { argv, dirs := partyDirs ++ (match c.cmd with | .init _ dir => [dir] | _ => []),
    files := base ++ c.extra, stdin := c.stdin }

def wsAliceSessPath : String := "sessions/5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"
def wsBobSessPath : String := "sessions/8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"
def wsPub (sk : HwBytes) : HwBytes := compLookupPub (clamp sk)
def textBytesFast (s : String) : HwBytes :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem nat_repr_one : Nat.repr 1 = "1" := by
  rw [Nat.repr_of_lt (by omega), Nat.digitChar_eq_one.mpr rfl]; rfl

def wsBundle : PublicBundle :=
  { identityKey := ecKey (wsPub wsSetup.bobId), registrationId := wsSetup.regIdB
    signedId := wsSetup.spkId, signedKey := ecKey (wsPub wsSetup.spk), signedSig := wsSetup.spkSig
    kyberId := wsSetup.kpkId, kyberKey := kyberKey wsSetup.kyberPk, kyberSig := wsSetup.kyberPkSig, oneTime := none }
def wsAliceBaseList : FileList :=
  [(addressFile, textBytesFast "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"),
   (identityKeyPairFile, IdentityKeyPairStructure.encode ⟨ecKey (wsPub wsSetup.aliceId), wsSetup.aliceId⟩),
   (registrationIdFile, le32 wsSetup.regIdA), (identityFile bobUuid, ecKey (wsPub wsSetup.bobId))]
def wsBobBaseList : FileList :=
  [(addressFile, textBytesFast "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"),
   (identityKeyPairFile, IdentityKeyPairStructure.encode ⟨ecKey (wsPub wsSetup.bobId), wsSetup.bobId⟩),
   (registrationIdFile, le32 wsSetup.regIdB), (identityFile aliceUuid, ecKey (wsPub wsSetup.aliceId)),
   ("signed-pre-keys/7", SignedPreKeyRecordStructure.encode
     ⟨wsSetup.spkId, ecKey (wsPub wsSetup.spk), wsSetup.spk, wsSetup.spkSig, 0⟩),
   ("last-resort-kyber-pre-keys/9", SignedPreKeyRecordStructure.encode
     ⟨wsSetup.kpkId, kyberKey wsSetup.kyberPk, kyberKey (wsSetup.kyberSec.drop 1), wsSetup.kyberPkSig, 0⟩),
   ("last-resort-kyber-pre-keys/9.base-keys", [])]

def s1 : HwBytes := ((parsePreKeyWire c1Out).map (·.message)).getD []
def s2 : HwBytes := ((parsePreKeyWire c2Out).map (·.message)).getD []
def s5 : HwBytes := ((parsePreKeyWire c5Out).map (·.message)).getD []
def c6BaseKey : HwBytes := ((parsePreKeyWire c6In).map (fun q => q.baseKey.take 33)).getD []

private theorem c6In_head_ne_whisper : c6In.head? ≠ some wireWhisperTag := by decide +kernel
private theorem c6In_parsed_ok : ((parsePreKeyWire c6In).map (fun q =>
    decide (q.message ∈ [s1, s2, s5]) && decide (q.message.length + 2048 < 2 ^ 32) &&
    (q.baseKey.take 33 == c6BaseKey))) = some true := by decide +kernel

def startsWith : HwBytes → HwBytes → Bool
  | [], _ => true | _ :: _, [] => false | a :: as, b :: bs => (a == b) && startsWith as bs
def hasSublist (pat : HwBytes) : HwBytes → Bool
  | [] => pat.isEmpty | x :: xs => startsWith pat (x :: xs) || hasSublist pat xs
private theorem startsWith_append (pat rest : HwBytes) : startsWith pat (pat ++ rest) = true := by
  induction pat with | nil => rfl | cons a as ih => simp [startsWith, ih]
private theorem hasSublist_append (pre pat post : HwBytes) : hasSublist pat (pre ++ pat ++ post) = true := by
  induction pre with
  | nil =>
    cases pat with
    | nil => cases post <;> rfl
    | cons a as =>
      simp only [List.nil_append, List.cons_append, hasSublist]
      exact Bool.or_eq_true _ _ |>.mpr (Or.inl (startsWith_append (a :: as) post))
  | cons x xs ih => simp only [List.cons_append, hasSublist, ih, Bool.or_true]
private theorem bytesField13_sublist_recordBytes (rr : DY.Libsignal.Rust.RecordRec) :
    hasSublist (bytesField 13 rr.current.aliceBaseKey) (recordBytes rr) = true := by
  let s := rr.current
  let innerPre := u32Field 1 s.sessionVersion ++ bytesField 2 s.localIdentityPublic ++
    bytesField 3 s.remoteIdentityPublic ++ bytesField 4 s.rootKey ++
    u32Field 5 s.previousCounter ++ ((s.senderChain.map (msgField 6 ∘ chainBytes)).getD []) ++
    s.receiverChains.flatMap (msgField 7 ∘ chainBytes) ++
    ((s.pendingPreKey.map fun p => msgField 9 (p.1 ++ p.2)).getD []) ++
    u32Field 10 s.remoteRegistrationId ++ u32Field 11 s.localRegistrationId
  let innerPost := ((s.pendingKyberPreKey.map fun p => msgField 14 (p.1 ++ p.2)).getD []) ++ bytesField 15 s.pqRatchetState
  let inner := innerPre ++ bytesField 13 s.aliceBaseKey ++ innerPost
  have hrec : recordBytes rr = (paddedVarint (1 * 8 + 2) 0 ++ paddedVarint inner.length 0 ++ innerPre) ++
      bytesField 13 s.aliceBaseKey ++ (innerPost ++ rr.previous.flatMap (msgField 2)) := by
    dsimp only [inner, innerPre, innerPost, s]; unfold recordBytes msgField encodeField; simp only [List.append_assoc]
  rw [hrec]; exact hasSublist_append _ _ _

/-- Rules out `EligibleForSessionPromotion` when `rec_` omits the protobuf field-13 tag of `c6BaseKey`. -/
theorem not_eligibleForSessionPromotion_of_no_sublist {rec_ : HwBytes}
    (hno : hasSublist (bytesField 13 c6BaseKey) rec_ = false) : ¬ EligibleForSessionPromotion rec_ c6In := by
  rintro ⟨rr, p, hrec, _, hp, hbk⟩
  have hok := c6In_parsed_ok; rw [hp, Option.map_some, Option.some.injEq] at hok
  have hbk_eq : p.baseKey.take 33 = c6BaseKey := beq_iff_eq.mp ((Bool.and_eq_true _ _).mp hok).2
  have hsub := bytesField13_sublist_recordBytes rr; rw [← hrec, hbk, hbk_eq, hno] at hsub; cases hsub

def wsCall0 : CliCall := { party := "alice", cmd := .init ⟨bobUuid, 1⟩ bundleDir, bundle := wsBundle.files bundleDir, stdin := [], coins := coins0 }
def wsCall1 : CliCall := { party := "alice", cmd := .send ⟨bobUuid, 1⟩, bundle := [], stdin := pt1, coins := coins1 }
def wsCall2 : CliCall := { party := "alice", cmd := .send ⟨bobUuid, 1⟩, bundle := [], stdin := pt2, coins := coins2 }
def wsCall3 : CliCall := { party := "bob", cmd := .recv ⟨aliceUuid, 1⟩, bundle := [], stdin := c3In, coins := coins3 }
def wsCall4 : CliCall := { party := "alice", cmd := .init ⟨bobUuid, 1⟩ bundleDir, bundle := wsBundle.files bundleDir, stdin := [], coins := coins4 }
def wsCall5 : CliCall := { party := "alice", cmd := .send ⟨bobUuid, 1⟩, bundle := [], stdin := pt5, coins := coins5 }
def wsCall6 : CliCall := { party := "bob", cmd := .recv ⟨aliceUuid, 1⟩, bundle := [], stdin := c6In, coins := coins6 }

def wsInp0 : Inputs := mkInpArgv ["init", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1", bundleDir] wsCall0 wsAliceBaseList
def wsInp1 (files0 : FileList) : Inputs := mkInpArgv ["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"] wsCall1 (scrubList files0)
def wsInp2 (files1 : FileList) : Inputs := mkInpArgv ["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"] wsCall2 (scrubList files1)
def wsInp3 : Inputs := mkInpArgv ["recv", "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"] wsCall3 wsBobBaseList
def wsInp4 (files2 : FileList) : Inputs := mkInpArgv ["init", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1", bundleDir] wsCall4 (clearSessionList wsAliceSessPath (scrubList files2))
def wsInp5 (files4 : FileList) : Inputs := mkInpArgv ["send", "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"] wsCall5 (scrubList files4)
def wsInp6 (files3 : FileList) : Inputs := mkInpArgv ["recv", "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"] wsCall6 (scrubList files3)

def wsOut0 (files0 : FileList) : Outcome := .exited 0 [] (filesOf files0)
def wsOut1 (files1 : FileList) : Outcome := .exited 0 c1Out (filesOf files1)
def wsOut2 (files2 : FileList) : Outcome := .exited 0 c2Out (filesOf files2)
def wsOut3 (files3 : FileList) : Outcome := .exited 0 pt3Out (filesOf files3)
def wsOut4 (files4 : FileList) : Outcome := .exited 0 [] (filesOf files4)
def wsOut5 (files5 : FileList) : Outcome := .exited 0 c5Out (filesOf files5)
def wsOut6 (files6 : FileList) : Outcome := .exited 0 pt6Out (filesOf files6)

def hasNonEmptySession (l : FileList) (sessPath : String) : Bool :=
  match evalFileList l sessPath with | some b => !b.isEmpty | none => false

def hasNoMatchBobSession (l : FileList) : Bool :=
  match evalFileList l wsBobSessPath with
  | some rec_ => !rec_.isEmpty && !hasSublist (bytesField 13 c6BaseKey) rec_ | none => false

def wsCompP0 : CryptoVerification.E2E.PEParams :=
  ⟨Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed.compHooks0.C,
   Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed.compHooks0.Q⟩
def wsPubVec (sk : HwBytes) : List.Vector (BitVec 8) 32 :=
  CryptoVerification.E2E.fitVec 32 (Symbolic.BugInjection.Proofs.CliExec.CompHooks0Placed.Interp0.compLookupPub (clamp sk))
def wsBundleFields : CryptoVerification.E2E.PreKeyBundleFields :=
  { regId := wsSetup.regIdB, opk := none, spkId := wsSetup.spkId, spkPub := wsPubVec wsSetup.spk,
    spkSig := CryptoVerification.E2E.fitVec 64 wsSetup.spkSig, kpkId := wsSetup.kpkId,
    kpkPub := CryptoVerification.E2E.fitVec 1568 wsSetup.kyberPk,
    kpkSig := CryptoVerification.E2E.fitVec 64 wsSetup.kyberPkSig, idPub := wsPubVec wsSetup.bobId }
def wsAlice0 : CryptoVerification.SignalSession.PqParty :=
  { party := .A, me := { idPriv := CryptoVerification.E2E.fitVec 32 wsSetup.aliceId, regId := wsSetup.regIdA },
    peerId := some ⟨⟨wsPubVec wsSetup.bobId⟩⟩, session := none,
    signed := [], oneTime := [], kyberOneTime := [], kyberLastResort := [] }
def wsBob0 : CryptoVerification.SignalSession.PqParty :=
  { party := .B, me := { idPriv := CryptoVerification.E2E.fitVec 32 wsSetup.bobId, regId := wsSetup.regIdB },
    peerId := some ⟨⟨wsPubVec wsSetup.aliceId⟩⟩, session := none,
    signed := [(wsSetup.spkId, ⟨CryptoVerification.E2E.fitVec 32 wsSetup.spk,
      CryptoVerification.E2E.fitVec 64 wsSetup.spkSig, 0#64⟩)],
    oneTime := [], kyberOneTime := [],
    kyberLastResort := [(wsSetup.kpkId, ⟨CryptoVerification.E2E.fitVec 1568 wsSetup.kyberPk,
      CryptoVerification.E2E.fitVec 3168 (wsSetup.kyberSec.drop 1),
      CryptoVerification.E2E.fitVec 64 wsSetup.kyberPkSig, 0#64⟩, [])] }
def wsTape0 : List.Vector (BitVec 8) CryptoVerification.E2E.initiateTapeLen :=
  CryptoVerification.E2E.fitVec CryptoVerification.E2E.initiateTapeLen coins0
def wsDummyX : CryptoVerification.E2E.UnreachedPqxdhPrimitives :=
  { sigPkGen := fun _ => [], sigSign := fun _ _ _ => [], scalarMul := fun _ _ => [],
    scalarAdd := fun _ _ => [], kemKeyGen := fun _ => ([], []), pow8 := fun _ => [],
    isValidDhTriple := fun _ _ _ => false }
def u8StrFast (s : String) : SignalPqxdh.Bytes := s.toList.flatMap String.utf8EncodeChar
def modelPrimsFast (X : CryptoVerification.E2E.UnreachedPqxdhPrimitives)
    (W : CryptoVerification.E2E.PEParams) : SignalPqxdh.Primitives :=
  let B := CryptoVerification.E2E.blockLevelPrims X W
  let B1 : SignalPqxdh.Primitives := { B with sha512 := SignalPqxdh.sha512Ref B }
  { B1 with
    sigVerify := SignalPqxdh.xeddsaVerifyRef B1, isCanonical := SignalPqxdh.isCanonicalRef B1,
    hkdfDerive96 := fun sec => SignalPqxdh.hkdfExpand96Ref B1
      (SignalPqxdh.hkdfExtractRef B1 none sec) (u8StrFast "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"),
    rootCreateChain := SignalPqxdh.rootCreateChainRef B1, chainKdfSeed := SignalPqxdh.chainKdfSeedRef B1,
    chainKdfNext := SignalPqxdh.chainKdfNextRef B1, deriveMsgKeys := SignalPqxdh.deriveMsgKeysRef B1,
    aeadEnc := SignalPqxdh.aes256CbcHmacEncRef B1, aeadDec := SignalPqxdh.aes256CbcHmacDecRef B1 }
def serviceIdParseFast (input : HwBytes) : Option (Bool × List.Vector (BitVec 8) 16) :=
  let pni : HwBytes := [0x50#8, 0x4e#8, 0x49#8, 0x3a#8]
  if pni.isPrefixOf input then
    (CryptoVerification.LibsignalTripleRatchetRepr.tryParseHyphenated
      CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse (input.drop pni.length)).map (true, ·)
  else (CryptoVerification.LibsignalTripleRatchetRepr.tryParseHyphenated
    CryptoVerification.LibsignalTripleRatchetRepr.uuidTryParse input).map (false, ·)
def serializedPartyAddressesFast (sender recipient : CryptoGames.Party) : Option HwBytes := do
  let s ← serviceIdParseFast (textBytesFast (CryptoVerification.E2E.partyAddressName sender))
  let r ← serviceIdParseFast (textBytesFast (CryptoVerification.E2E.partyAddressName recipient))
  return CryptoVerification.LibsignalTripleRatchetRepr.addrBytes s CryptoVerification.E2E.partyDeviceId ++
    CryptoVerification.LibsignalTripleRatchetRepr.addrBytes r CryptoVerification.E2E.partyDeviceId
def mkAliceInit (t : List.Vector (BitVec 8) CryptoVerification.E2E.initiateTapeLen) :
    CryptoVerification.SignalSession.PqParty :=
  match SignalPqxdh.Model.initiateKeys (modelPrimsFast wsDummyX wsCompP0)
      (CryptoVerification.E2E.initiateInput wsCompP0 wsAlice0.me wsBundleFields t) with
  | some (dk, hdr) =>
    let idA := CryptoVerification.E2E.keyPairOf wsCompP0.C wsAlice0.me.idPriv
    match CryptoGames.LibsignalSession.initializeInitiatorSession wsCompP0.C
        (CryptoVerification.E2E.pqxdhSpqrSession wsCompP0) ⟨idA.publicKey⟩ ⟨⟨wsBundleFields.idPub⟩⟩
        ⟨wsBundleFields.spkPub⟩ (CryptoGames.HKDF.bytesToKey32 (CryptoVerification.E2E.ofU8 dk.rootKey))
        (CryptoGames.HKDF.bytesToKey32 (CryptoVerification.E2E.ofU8 dk.chainKey))
        (CryptoGames.HKDF.bytesToKey32 (CryptoVerification.E2E.ofU8 dk.pqrKey))
        (CryptoGames.HKDF.bytesToKey32 ((t.toList.drop 160).take 32)) with
    | .ok s =>
      { wsAlice0 with
        peerId := some ⟨⟨wsBundleFields.idPub⟩⟩,
        session := some (CryptoVerification.E2E.initiatorRecordExtras wsAlice0.me wsBundleFields
          ⟨CryptoVerification.E2E.u8Vec 32 hdr.ekAPk⟩ (CryptoVerification.E2E.u8Vec 1568 hdr.kemCt),
          ⟨.A, s.setUnacknowledgedPreKeyMessage, 0, [0]⟩) }
    | .error _ => wsAlice0
  | none => wsAlice0
def wsAlice1 : CryptoVerification.SignalSession.PqParty := mkAliceInit wsTape0
def wsAlice2 : CryptoVerification.SignalSession.PqParty :=
  match wsAlice1.session with
  | some (x, g) =>
    match CryptoGames.LibsignalSession.SessionState.messageEncrypt wsCompP0.C
        CryptoVerification.LibsignalProtoCodec.protoSignalCodec
        (CryptoVerification.E2E.pqxdhSpqrSession wsCompP0)
        (serializedPartyAddressesFast .A .B) pt1 coins1 g.session with
    | (.ok _, s) => { wsAlice1 with session := some (x, { g with session := s }) }
    | _ => wsAlice1
  | none => wsAlice1
def wsDummyMsg : CryptoVerification.E2E.PreKeyMessageFields :=
  { regId := 0, opkId := none, spkId := 0, kpkId := 0, kyberCt := List.Vector.replicate 1568 0#8,
    baseKey := List.Vector.replicate 32 0#8, idPub := List.Vector.replicate 32 0#8, inner := [] }
def wsMsg3 : CryptoVerification.E2E.PreKeyMessageFields :=
  (DY.Libsignal.Composed.Refinement.Cli.ElfGuard.preKeyOfBody? (c3In.drop 1)).getD wsDummyMsg
def wsRc3 : BitVec 256 := CryptoGames.HKDF.bytesToKey32 coins3
def wsBob3 : CryptoVerification.SignalSession.PqParty :=
  match CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec wsMsg3.inner,
      CryptoVerification.SignalSession.preKeysNamedBy wsBob0 wsMsg3 with
  | .ok inner, some k =>
    match SignalPqxdh.Model.acceptKeys (modelPrimsFast wsDummyX wsCompP0)
        (CryptoVerification.E2E.acceptInput wsCompP0 wsBob0.me k wsMsg3),
        CryptoVerification.SignalSession.markKyberUsed wsBob0 wsMsg3 with
    | some dk, some st1 =>
      let st0 := CryptoGames.LibsignalSession.initializeRecipientSession
        (CryptoVerification.E2E.pqxdhSpqrSession wsCompP0)
        ⟨(CryptoVerification.E2E.keyPairOf wsCompP0.C wsBob0.me.idPriv).publicKey⟩
        ⟨⟨wsMsg3.idPub⟩⟩ (CryptoVerification.E2E.keyPairOf wsCompP0.C k.spkPriv)
        (CryptoGames.HKDF.bytesToKey32 (CryptoVerification.E2E.ofU8 dk.rootKey))
        (CryptoGames.HKDF.bytesToKey32 (CryptoVerification.E2E.ofU8 dk.chainKey))
        (CryptoGames.HKDF.bytesToKey32 (CryptoVerification.E2E.ofU8 dk.pqrKey))
      match CryptoGames.LibsignalSession.SessionState.tryDecryptFromRecord wsCompP0.C
          (CryptoVerification.E2E.pqxdhSpqrSession wsCompP0)
          (serializedPartyAddressesFast .A .B) inner .preKey wsRc3 st0 with
      | (.ok _, s) =>
        { CryptoVerification.SignalSession.removeOpk st1 wsMsg3 with
          peerId := some ⟨⟨wsMsg3.idPub⟩⟩,
          session := some (CryptoVerification.E2E.responderRecordExtras wsBob0.me wsMsg3, ⟨.B, s, 1, [1]⟩) }
      | _ => wsBob0
    | _, _ => wsBob0
  | _, _ => wsBob0
def wsTape4 : List.Vector (BitVec 8) CryptoVerification.E2E.initiateTapeLen :=
  CryptoVerification.E2E.fitVec CryptoVerification.E2E.initiateTapeLen coins4
def wsAlice5 : CryptoVerification.SignalSession.PqParty := mkAliceInit wsTape4
def idStrFast (i : BitVec 32) : String :=
  if i = 7#32 then "7" else if i = 9#32 then "9" else toString i.toNat
def partyTextFast : CryptoGames.Party → String
  | .A => "8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b.1"
  | .B => "5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6.1"
def encodeDirFast (W : CryptoVerification.E2E.PEParams)
    (st : CryptoVerification.SignalSession.PqParty) : FileList :=
  [(addressFile, textBytesFast (partyTextFast st.party)),
   (identityKeyPairFile, IdentityKeyPairStructure.encode
      ⟨CryptoVerification.E2E.djbKey (CryptoVerification.E2E.keyPairOf W.C st.me.idPriv).publicKey.bytes,
       st.me.idPriv.toList⟩), (registrationIdFile, le32 st.me.regId)] ++
  (match st.peerId with
   | some k => [(identityFile (CryptoVerification.E2E.partyAddressName st.party.other), k.serialize)]
   | none => []) ++
  (match st.session with
   | some (x, g) => [("sessions/" ++ partyTextFast st.party.other,
       CryptoVerification.E2E.encodeRecordUnderExtras (fun _ => x) g)]
   | none => []) ++
  st.signed.map (fun (i, k) => ("signed-pre-keys/" ++ idStrFast i,
    CryptoVerification.SignalSession.signedRecordBytes W.C i k)) ++
  st.oneTime.map (fun (i, k) => ("one-time-pre-keys/" ++ idStrFast i,
    match k with | some sk => CryptoVerification.SignalSession.oneTimeRecordBytes W.C i sk | none => [])) ++
  st.kyberOneTime.map (fun (i, k) => ("one-time-kyber-pre-keys/" ++ idStrFast i,
    match k with | some k => CryptoVerification.SignalSession.kyberRecordBytes i k | none => [])) ++
  (st.kyberLastResort.map fun (i, k, seen) =>
    [("last-resort-kyber-pre-keys/" ++ idStrFast i, CryptoVerification.SignalSession.kyberRecordBytes i k),
     ("last-resort-kyber-pre-keys/" ++ idStrFast i ++ ".base-keys",
      CryptoVerification.SignalSession.baseKeysBytes seen)]).flatten
def wsAlice0Files : FileList := encodeDirFast wsCompP0 wsAlice0
def wsAlice1Files : FileList := encodeDirFast wsCompP0 wsAlice1
def wsAlice2Files : FileList := encodeDirFast wsCompP0 wsAlice2
def wsBob3Files : FileList := encodeDirFast wsCompP0 wsBob3
def wsAlice5Files : FileList := encodeDirFast wsCompP0 wsAlice5

def sameEvalFileList (l1 l2 : FileList) : Bool :=
  l1.all (fun x => evalFileList l1 x.1 == evalFileList l2 x.1) &&
  l2.all (fun x => evalFileList l1 x.1 == evalFileList l2 x.1)

def sameStepDirs (f0 f1 f2 f3 f4 : FileList) : Bool :=
  sameEvalFileList (scrubList f0) wsAlice1Files &&
  sameEvalFileList (scrubList f1) wsAlice2Files &&
  sameEvalFileList (clearSessionList wsAliceSessPath (scrubList f2)) wsAlice0Files &&
  sameEvalFileList (scrubList f3) wsBob3Files &&
  sameEvalFileList (scrubList f4) wsAlice5Files

/-- Decidable side-condition on post-call file lists `f0`..`f6`: valid bounded paths, non-empty
Alice sessions after calls 0, 1, and 4, a non-matching Bob session after call 3, and directory
extensionality on the honest prefix states. -/
def ValidStepFiles (f0 f1 f2 f3 f4 f5 f6 : FileList) : Bool :=
  validFileList f0 && validFileList f1 && validFileList f2 && validFileList f3 &&
  validFileList f4 && validFileList f5 && validFileList f6 &&
  hasNonEmptySession (scrubList f0) wsAliceSessPath && hasNonEmptySession (scrubList f1) wsAliceSessPath &&
  hasNoMatchBobSession (scrubList f3) &&
  (hasNonEmptySession (scrubList f4) wsAliceSessPath && sameStepDirs f0 f1 f2 f3 f4)

private theorem validStepFiles_smoke :
    ValidStepFiles wsAlice1Files wsAlice2Files wsAlice2Files wsBob3Files wsAlice5Files [] [] = true := by
  decide +kernel

theorem ValidStepFiles.sameDirs {f0 f1 f2 f3 f4 f5 f6 : FileList}
    (h : ValidStepFiles f0 f1 f2 f3 f4 f5 f6 = true) :
    sameStepDirs f0 f1 f2 f3 f4 = true := by
  unfold ValidStepFiles at h; simp only [Bool.and_eq_true] at h
  exact h.2.2

def mkTurn (aDir bDir : DirectorySnapshot) (sent : List HwBytes) (bobOff : Bool) : CliTurn :=
  { dirs := fun q => if q = "alice" then aDir else if q = "bob" then bDir else fun _ => none, sent, bobOff }

private theorem sessPath_bob_eq {r : ProtocolSetup} (ha : r.alice = "alice") :
    sessionPathOf r "bob" = wsBobSessPath := by
  simp [sessionPathOf, peerOf, peerNameOf, ha, (by decide : ("bob" : String) ≠ "alice"),
    sessionFile, Address.text, aliceUuid, wsBobSessPath, nat_repr_one]

theorem preKeyNoMatch_call6_of_files3 {r : ProtocolSetup} (ha : r.alice = "alice") (hb : r.bob = "bob")
    {files3 : FileList} (hv3 : validFileList files3 = true)
    (hnm3 : hasNoMatchBobSession (scrubList files3) = true)
    (aDir : DirectorySnapshot) (sent : List HwBytes) (off : Bool) :
    PreKeyNoMatch r (mkTurn aDir (filesOf (scrubList files3)) sent off) wsCall6 := by
  have hba : ("bob" : String) ≠ "alice" := by decide
  have hv3s := scrubList_valid hv3; unfold hasNoMatchBobSession at hnm3
  cases hev : evalFileList (scrubList files3) wsBobSessPath <;> rw [hev] at hnm3
  · cases hnm3
  · rename_i rec_; obtain ⟨hne_bool, hnosub_bool⟩ := (Bool.and_eq_true _ _).mp hnm3
    have hrec_ne : rec_ ≠ [] := fun h => by rw [h] at hne_bool; cases hne_bool
    refine ⟨hb.symm, ⟨_, rfl⟩, c6In_head_ne_whisper, rec_, ?_,
      not_eligibleForSessionPromotion_of_no_sublist ((Bool.not_eq_true' _).mp hnosub_bool)⟩
    simp [CliTurn.records, mkTurn, hb, hba, sessPath_bob_eq ha,
      filesOf_eq_evalFileList (validFileList_paths hv3s), hev, hrec_ne]
