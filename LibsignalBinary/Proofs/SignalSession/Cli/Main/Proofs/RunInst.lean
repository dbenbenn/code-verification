/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.RunInst.ScopeAndCommit -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Hops -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooks
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Domains
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.StackBudget
import LibsignalBinary.Proofs.SignalSession.Cli.ProcessBridge
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.RunRel
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.S0Proofs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Spec
import LibsignalBinary.Proofs.SignalSession.Cli.Run.ReadFileHook
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Bounds
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Sem
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.Oblig.EncSessionInj
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.Placed.BudgetVmSteps

/-!
# Instantiation of `signal_session::run` into `main` and Domain Refinement Bridges

Wires `RunCompose.run_ok'` and `runRel_dom` at `cliRunSem` into `main_ok_a1`, combining `mainSpec` /
`mainSpecTight` with `RunRefine`, `RunBounds`, `RunFilesOk`, `RunEncOk`, `RunHsOk`, and `CommitOk`
to establish SM-domain (`main_ok_cli_sm`, `cliBinaryCorrect_of_slots`) and 5-clause PQXDH-domain
(`main_ok_cli_pq`) correctness, together with `(P, A, ext)` generalizations.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs

/-- Default unreached `UnreachedPqxdhPrimitives` witness (used when instantiating `RunSem` for the SM domain,
which never invokes `initiate` or `decrypt_prekey`). -/
@[expose] def defaultModelExtras : UnreachedPqxdhPrimitives where
  sigPkGen _ := []
  sigSign _ _ _ := []
  scalarMul _ _ := []
  scalarAdd _ _ := []
  kemKeyGen _ := ([], [])
  pow8 _ := []
  isValidDhTriple _ _ _ := false

/-- Concrete `RunSem` (`S₀`) at `Slots.scopeIn` for `encDef`, `decSigDef`, `initDef` (`InitOk₀`),
`filesOk₀`, and `encOk₀`, parameterized over `decPk`, `decPkOk`, and `pksmParse`. -/
@[expose] noncomputable def cliRunSem (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) : RunSem where
  encrypt := encDef ⟨W.C, W.Q⟩ Slots.scopeIn
  decryptSignal := decSigDef ⟨W.C, W.Q⟩ Slots.scopeIn
  initiate := initDef X ⟨W.C, W.Q⟩
  decryptPrekey := decPk
  pksmParse := pksmParse
  filesOk := Slots.filesOk₀ Slots.scopeIn (fun _ => True)
  encOk := Slots.encOk₀ Slots.scopeIn
  initOk := InitOk₀ ⟨W.C, W.Q⟩
  decPkOk := decPkOk

/-- `cliRunSem` parameterized over `P : PEParams` instead of `W : CliHooks` (`W.bcmp` and
`W.utf8Err` are unused in `cliRunSem`). -/
@[expose] noncomputable def cliRunSemExt (X : UnreachedPqxdhPrimitives) (P : PEParams)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) : RunSem where
  encrypt := encDef P Slots.scopeIn
  decryptSignal := decSigDef P Slots.scopeIn
  initiate := initDef X P
  decryptPrekey := decPk
  pksmParse := pksmParse
  filesOk := Slots.filesOk₀ Slots.scopeIn (fun _ => True)
  encOk := Slots.encOk₀ Slots.scopeIn
  initOk := InitOk₀ P
  decPkOk := decPkOk

theorem cliRunSem_eq_ext (X : UnreachedPqxdhPrimitives) (W : CliHooks)
    (decPk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → List (BitVec 8) →
      SlotAns (List (BitVec 8)))
    (decPkOk : FsFiles → AddrVal → AddrVal → PreKeySignalMessage → Prop)
    (pksmParse : List (BitVec 8) → Option PreKeySignalMessage) :
    cliRunSem X W decPk decPkOk pksmParse = cliRunSemExt X ⟨W.C, W.Q⟩ decPk decPkOk pksmParse :=
  rfl

end CryptoVerification.SignalSession.Cli.MainHops

namespace CryptoVerification.SignalSession

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunRefine
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.LibsignalPublicApi.StoreKit

private theorem varint_length_le_5 {n : Nat} (hn : n < 2 ^ 32) :
    (Prost.varint n).length ≤ 5 := by
  unfold Prost.varint; split
  · simp
  · dsimp only [List.length_cons]; unfold Prost.varint; split
    · simp
    · dsimp only [List.length_cons]; unfold Prost.varint; split
      · simp
      · dsimp only [List.length_cons]; unfold Prost.varint; split
        · simp
        · dsimp only [List.length_cons]; unfold Prost.varint
          have h5 : n / 128 / 128 / 128 / 128 < 128 := by omega
          simp [h5]

private theorem key_length_le_5 {tag wt : Nat} (h : 8 * tag + wt < 2 ^ 32) :
    (Prost.key tag wt).length ≤ 5 :=
  varint_length_le_5 h

private theorem uint32Field_length_le_10 {tag : Nat} (ht : 8 * tag < 2 ^ 32)
    (ov : Option (BitVec 32)) :
    (Prost.uint32Field tag ov).length ≤ 10 := by
  cases ov with
  | none => simp [Prost.uint32Field]
  | some v =>
    simp only [Prost.uint32Field, List.length_append]
    have h1 := key_length_le_5 (wt := 0) (by omega)
    have h2 := varint_length_le_5 v.isLt
    omega

private theorem bytesField_some_length_le {tag : Nat} {bs : List (BitVec 8)}
    (ht : 8 * tag + 2 < 2 ^ 32) (hbs : bs.length < 2 ^ 32) :
    (Prost.bytesField tag (some bs)).length ≤ bs.length + 10 := by
  simp only [Prost.bytesField, List.length_append]
  have h1 := key_length_le_5 ht
  have h2 := varint_length_le_5 hbs
  omega

theorem preKeyMsgE_bytes_lt_2_32 {m : PreKeyMessageFields} (hm : m.inner.length + 2048 < 2 ^ 32) :
    m.bytes.length < 2 ^ 32 := by
  simp only [PreKeyMessageFields.bytes, ProtoPreKeySignalMessage.encode, List.length_cons,
    List.length_append]
  have h1 := uint32Field_length_le_10 (tag := 1) (by decide) m.opkId
  have h2 := bytesField_some_length_le (tag := 2) (bs := djbKey m.baseKey) (by decide)
    (by simp [djbKey])
  have h3 := bytesField_some_length_le (tag := 3) (bs := djbKey m.idPub) (by decide)
    (by simp [djbKey])
  have h4 := bytesField_some_length_le (tag := 4) (bs := m.inner) (by decide) (by omega)
  have h5 := uint32Field_length_le_10 (tag := 5) (by decide) (some m.regId)
  have h6 := uint32Field_length_le_10 (tag := 6) (by decide) (some m.spkId)
  have h7 := uint32Field_length_le_10 (tag := 7) (by decide) (some m.kpkId)
  have h8 := bytesField_some_length_le (tag := 8) (bs := kyberKey m.kyberCt) (by decide)
    (by simp [kyberKey])
  have hdjb1 : (djbKey m.baseKey).length = 33 := by simp [djbKey]
  have hdjb2 : (djbKey m.idPub).length = 33 := by simp [djbKey]
  have hkyb : (kyberKey m.kyberCt).length = 1569 := by simp [kyberKey]
  omega

end CryptoVerification.SignalSession
