/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.AEAD.Aes256
public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import Symbolic.Specifications.Refinement.Statement

/-!
# ELF Binding for CLI Refinement

Instantiates `CompRefinesCli` with the ARM64 ELF run relation (`elfRel`) using symbol addresses
resolved from the ELF's `.symtab` (`resolveCliElfAddrs`), together with hook-to-symbol and
FIPS 197 AES-256 agreement (`HooksMatchPlaced`), per-call primitive agreement with the executed
ELF primitives (`RealHooksAgreeOnInput`, `realCliHooks`), and the progress guarantee up to
`SampleNTT` seed divergence (`CliElfProgress`, DEV-CLI22).
-/

@[expose] public section

set_option autoImplicit false

namespace DY.Libsignal.Composed.Refinement.Cli

open Arm64 Arm64.Process
open CryptoProofLib.Refinement (ByteString ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Refinement (sha256CompressFunction sha256CompressSymbol x25519AgreementSymbol
  x25519PublicKeySymbol aesCbcEncryptSymbol aesCbcDecryptSymbol)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol)
open CryptoGames.LibsignalSession (GhostState IdentityKey SessionState)
open CryptoVerification.E2E (PEParams PreKeyBundleFields PreKeyMessageFields RecordExtras
  UnreachedPqxdhPrimitives initiateTapeLen pqxdhSessionParams pqxdhSpqrSession wirePrekey
  wireWhisper)
open CryptoVerification.SignalSession (CliElfAddrs CliHooks CliReachesSampleNttStuckElf Inputs
  Outcome PqParty PqSessionMatches PqxdhPartyInSpecDomain bundleDir cliRunElf encodeDir filesOf
  partyAddress pqInitInputs pqInitModel pqInputs pqRecvInputs pqRecvPrekeyModel pqRecvWhisperModel
  pqSendInputs pqSendModel publicBundleOf realCrypto realPqxdhPrims resolveCliElfAddrs)

/-- Agreement between `CliHooks` `W` and `ExternInterpretation` `interp` on SHA-256 compression,
AES-256-CBC, X25519, and Kyber-1024. -/
def HooksMatchInterpretation (interp : ExternInterpretation) (W : CliHooks) : Prop :=
  W.C.F = sha256CompressFunction interp ∧
  (∀ p k iv : ByteString, k.length = 32 → iv.length = 16 →
    interp aesCbcEncryptSymbol [p, k, iv] =
      some (CryptoGames.LibsignalSession.aesCbcEncrypt W.C.E (CryptoGames.HKDF.bytesToKey32 k)
        (CryptoGames.CBC.bytesToBlock iv) p)) ∧
  (∀ c k iv : ByteString, k.length = 32 → iv.length = 16 →
    interp aesCbcDecryptSymbol [c, k, iv] =
      CryptoGames.LibsignalSession.aesCbcDecrypt W.C.D (CryptoGames.HKDF.bytesToKey32 k)
        (CryptoGames.CBC.bytesToBlock iv) c) ∧
  (∀ a b : List.Vector (BitVec 8) 32,
    interp x25519AgreementSymbol [a.toList, b.toList] = some (W.C.X a b).toList) ∧
  (∀ a : List.Vector (BitVec 8) 32,
    interp x25519PublicKeySymbol [a.toList] = some (W.C.pubKey a).toList) ∧
  (∀ (pk : List.Vector (BitVec 8) 1568) (rand : List.Vector (BitVec 8) 32),
    interp kyberEncapsSymbol [pk.toList, rand.toList] =
      some ((W.Q.encaps pk rand).1.toList ++ (W.Q.encaps pk rand).2.toList)) ∧
  (∀ (sk : List.Vector (BitVec 8) 3168) (ct : List.Vector (BitVec 8) 1568),
    interp kyberDecapsSymbol [sk.toList, ct.toList] = some (W.Q.decaps sk ct).toList)

namespace ElfGuard

/-- Zero-pads or truncates `b` to 32 bytes. -/
def vec32 (b : HwBytes) : List.Vector (BitVec 8) 32 := ⟨(b ++ List.replicate 32 0).take 32, by simp⟩

/-- Equivalence of CLI `Inputs` up to directory-snapshot extensionality under `filesOf`. -/
def InputsEquiv (i i' : Inputs) : Prop :=
  i.argv = i'.argv ∧ i.dirs = i'.dirs ∧ i.stdin = i'.stdin ∧
    ∀ p, filesOf i.files p = filesOf i'.files p

/-- Extracts `PreKeyMessageFields` from a pre-key message body when `parsePreKey` succeeds at
version 4 with a 1568-byte Kyber ciphertext prefixed by `0x08`. -/
def preKeyOfBody? (body : HwBytes) : Option PreKeyMessageFields :=
  match parsePreKey body, decodePreKey (body.drop 1) with
  | some q, some raw =>
    if q.version = 4 then
      match q.kyberPreKeyId, q.kyberCiphertext with
      | some kid, some (t :: ct) =>
        if h : t = 0x08#8 ∧ ct.length = 1568 then
          some { regId := raw.registrationId.getD 0, opkId := q.preKeyId, spkId := q.signedPreKeyId,
                 kpkId := kid, kyberCt := ⟨ct, h.2⟩, baseKey := vec32 (q.baseKey.drop 1),
                 idPub := vec32 (q.identityKey.drop 1), inner := q.message }
        else none
      | _, _ => none
    else none
  | _, _ => none

/-- Checks whether an existing session `(x, g)` matches parsed pre-key fields `q` on
`aliceBaseKey` and `sessionVersion`. -/
def PqFieldsMatch (x : RecordExtras) (g : GhostState HwBytes) (q : PreKeyFields) : Prop :=
  x.aliceBaseKey = q.baseKey.take 33 ∧ g.session.sessionVersion.toNat = q.version

/-- Model transition for decrypting a parsed pre-key message `q` against a matching existing
session `(x, g)`. -/
def pqRecvMatchingFieldsModel (P : PEParams) (st : PqParty) (x : RecordExtras)
    (g : GhostState HwBytes) (q : PreKeyFields) (rc : BitVec 256) :
    Option (Option (PqParty × HwBytes)) :=
  let idA : IdentityKey := ⟨⟨vec32 (q.identityKey.drop 1)⟩⟩
  if !st.trusts idA then some none
  else if g.session.remoteIdentity ≠ some idA then some none
  else
    match SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
        ((pqxdhSessionParams P).expectedAddrs g.party) q.inner .preKey rc g.session with
    | (.ok pt, s) =>
      some (some ({ st with peerId := some idA, session := some (x, { g with session := s }) }, pt))
    | (.error .panic, _) => none
    | (.error _, _) => some none

/-- CLI `init` inputs for party `st` over an arbitrary bundle file list `files` and 192-byte
randomness tape `t`. -/
def pqInitInputsF (P : PEParams) (st : PqParty) (files : List (String × HwBytes))
    (t : List.Vector (BitVec 8) initiateTapeLen) : Inputs :=
  pqInputs P st (.init (partyAddress st.party.other) bundleDir) files t.toList []

/-- Per-call party-directory and spec-domain agreement guard between primitive parameters `P`
and `P₀` on input `i`: on every `P`-spec-domain party state `st` and admissible extra-file list
`extra` whose `pqInputs` matches `i`, `encodeDir P st = encodeDir P₀ st` (the stored X25519
public-key files match `P₀`) and `st` also lies in `PqxdhPartyInSpecDomain P₀` (trivially `True`
when `P = P₀`). Restricting `extra` to flat `bundleDir` files on `init` and `[]` otherwise
(matching `ValidCall`) prevents `extra` from shadowing `encodeDir P st` entries under last-wins
`filesOf`. -/
abbrev DirsAgreeOnInput (P P₀ : PEParams) (i : Inputs) : Prop :=
  ∀ st cmd extra coins stdin, PqxdhPartyInSpecDomain P st →
    (match cmd with | .init _ d => d = bundleDir ∧ BundleFilesFlat extra | _ => extra = []) →
    InputsEquiv i (pqInputs P st cmd extra coins stdin) →
    encodeDir P st = encodeDir P₀ st ∧ PqxdhPartyInSpecDomain P₀ st

/-- Per-call model-agreement guard between primitive parameters `P` and `P₀` on input `i`: on
every spec-domain CLI transition matching `i`, the protocol model at `P` produces the same
transition as at `P₀`. Shared across the linked, closed cryptographic primitives (trivially `True`
when `P = P₀`). -/
abbrev ModelAgreesOnInput (P P₀ : PEParams) (i : Inputs) : Prop :=
  (∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (files : List (String × HwBytes))
      (b : PreKeyBundleFields) (t : List.Vector (BitVec 8) initiateTapeLen),
    PqxdhPartyInSpecDomain P st → st.session = none →
    (files = (publicBundleOf b).files bundleDir ∨
      (BundleFilesFlat files ∧ parseBundleFiles (filesOf files) = some (publicBundleOf b))) →
    InputsEquiv i (pqInitInputsF P st files t) →
    pqInitModel X P st b t = pqInitModel X P₀ st b t) ∧
  (∀ (st : PqParty) (m : HwBytes) (coins : List.Vector (BitVec 8) 64),
    PqxdhPartyInSpecDomain P st → m.length < 2 ^ 32 →
    InputsEquiv i (pqSendInputs P st m coins) →
    pqSendModel P st m coins.toList = pqSendModel P₀ st m coins.toList) ∧
  (∀ (st : PqParty) (body : HwBytes) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → body.length < 2 ^ 32 →
    InputsEquiv i (pqRecvInputs P st (wireWhisper :: body) rc) →
    pqRecvWhisperModel P st body rc = pqRecvWhisperModel P₀ st body rc) ∧
  (∀ (X : UnreachedPqxdhPrimitives) (st : PqParty) (body : HwBytes) (m : PreKeyMessageFields)
      (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → m.inner.length + 2048 < 2 ^ 32 →
    (body = m.bytes ∨ (body.length < 2 ^ 32 ∧ preKeyOfBody? body = some m)) →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    ((∀ x g, st.session = some (x, g) → PqSessionMatches x g m) →
      pqRecvPrekeyModel X P st m rc = pqRecvPrekeyModel X P₀ st m rc) ∧
    (∀ x g, st.session = some (x, g) → ¬ PqSessionMatches x g m →
      pqRecvPrekeyModel X P { st with session := none } m rc =
        pqRecvPrekeyModel X P₀ { st with session := none } m rc)) ∧
  (∀ (st : PqParty) (x : RecordExtras) (g : GhostState HwBytes) (body : HwBytes)
      (q : PreKeyFields) (rc : BitVec 256),
    PqxdhPartyInSpecDomain P st → st.session = some (x, g) → body.length < 2 ^ 32 →
    parsePreKey body = some q → PqFieldsMatch x g q →
    InputsEquiv i (pqRecvInputs P st (wirePrekey :: body) rc) →
    pqRecvMatchingFieldsModel P st x g q rc =
      pqRecvMatchingFieldsModel P₀ st x g q rc)

end ElfGuard

/-- The closed CLI primitives executed by the linked ELF code (`realCrypto` and `realPqxdhPrims`
from `CliBinaryPq.lean`). -/
noncomputable def realCliHooks : CliHooks := ⟨realCrypto, realPqxdhPrims⟩

/-- Per-call domain guard: on every spec-domain transition matching `i`, the calling party's
encoded key files and spec-domain membership (`ElfGuard.DirsAgreeOnInput`) and the protocol model
transition (`ElfGuard.ModelAgreesOnInput`) at `W` agree with `realCliHooks`.

* **Real-binary instantiation**: at `W = realCliHooks`, `RealHooksAgreeOnInput W i` holds on
  every input, so `elfRel` reduces to `runFnToRelation (cliRunElf elf addrs)` (no
  `RealHooksAgreeOnInput` filter). Admissibility of `realCliHooks` (`RealPrimsAdmissible`:
  `∃ interp, ExternContractsHoldCli interp ∧ RealPrimsMatch interp`) is proved by
  `Proven.Refinement.real_prims_admissible`, and `CompRefinesCliBinaryReal` (below) and
  `SignalSessionSecureReal` (`Symbolic/Specifications/Security/Binary.lean`) fix the primitives to
  `realCliHooks` via `RealPrimsMatch` over `elfRelReal` (dropping the `RealHooksAgreeOnInput`
  filter while retaining the `CliTraces` step guards and `InvertsGuarded` / `CoinsFresh` premises).
* **Non-vacuity and witness interpretations**: agreement is required only on reachable trace
  inputs, so witness interpretations keep real X25519 public keys on the setup secrets while
  preserving collision-free / synthetic SHA-256 and X25519 laws and lookup-table Kyber / ML-KEM
  off-trace. -/
abbrev RealHooksAgreeOnInput (W : CliHooks) (i : Inputs) : Prop :=
  ElfGuard.DirsAgreeOnInput ⟨W.C, W.Q⟩ ⟨realCliHooks.C, realCliHooks.Q⟩ i ∧
    ElfGuard.ModelAgreesOnInput ⟨W.C, W.Q⟩ ⟨realCliHooks.C, realCliHooks.Q⟩ i

/-- Binary primitive agreement: `HooksMatchInterpretation interp W` with `W.C.E` and `W.C.D`
fixed to the closed FIPS 197 AES-256 block cipher (`CryptoGames.AES256.aes256Enc`,
`CryptoGames.AES256.aes256Dec`) executed by the linked ELF code. -/
def HooksMatchPlaced (interp : ExternInterpretation) (W : CliHooks) : Prop :=
  HooksMatchInterpretation interp W ∧
  W.C.E = CryptoGames.AES256.aes256Enc ∧ W.C.D = CryptoGames.AES256.aes256Dec

/-- ARM64 process run relation of `elf` at `.symtab`-resolved addresses `addrs` under hooks `W`,
guarded by per-call agreement with the executed primitives (`RealHooksAgreeOnInput W i`). -/
def elfRel (elf : ElfImage) (addrs : CliElfAddrs)
    (_interp : ExternInterpretation) (W : CliHooks) :
    Inputs → Option Outcome → Prop :=
  fun i o => runFnToRelation (cliRunElf elf addrs) i o ∧ RealHooksAgreeOnInput W i

/-- Progress (no CPU fault, trap, or non-termination unless the run reaches a non-terminating
`SampleNTT` entry, `CliReachesSampleNttStuckElf`, DEV-CLI22) on every guarded `CliCall`
(`RealHooksAgreeOnInput W i`) at any turn reachable from `initDirs` under `elfRel elf addrs`:
either `cliRunElf elf addrs i` produces a process outcome, or the run reaches one of the 5
`libcrux_ml_kem` `SampleNTT` entry points with a SHAKE-128 matrix seed that never terminates
(`CliReachesSampleNttStuckElf elf addrs i`, DEV-CLI22). -/
def CliElfProgress (elf : ElfImage) (addrs : CliElfAddrs) : Prop :=
  ∀ interp : ExternInterpretation, ExternContractsHoldCli interp →
  ∀ W : CliHooks, HooksMatchPlaced interp W →
  ∀ r : ProtocolSetup, ProtocolSetupWF r →
  ∀ t : CliTurn,
    CliReachable (elfRel elf addrs interp W) interp r
      (CliTurn.init (initDirs interp r)) t →
  ∀ (c : CliCall) (i : CryptoVerification.SignalSession.Inputs),
    ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
    RealHooksAgreeOnInput W i →
    cliRunElf elf addrs i ≠ none ∨ CliReachesSampleNttStuckElf elf addrs i

/-- Whole-protocol refinement and progress guarantee for ELF image `bytes`: parses `bytes`,
resolves the 18 panic and 5 `SampleNTT` addresses from `.symtab` (`resolveCliElfAddrs`), and
asserts `CliElfProgress elf addrs` and `CompRefinesCli HooksMatchPlaced (elfRel elf addrs)`. -/
def CompRefinesCliBinary (bytes : List (BitVec 8)) : Prop :=
  ∃ (elf : ElfImage) (addrs : CliElfAddrs),
    ElfImage.parse bytes = .ok elf ∧
    resolveCliElfAddrs bytes elf = .ok addrs ∧
    CliElfProgress elf addrs ∧
    CompRefinesCli HooksMatchPlaced (elfRel elf addrs)

/-! ## Real-primitive statements

The statements below fix the CLI primitives to the closed primitives executed by the linked ELF
(`realCliHooks`) instead of quantifying over all agreeing `W : CliHooks`. The run relation
`elfRelReal` therefore drops the `RealHooksAgreeOnInput` filter, so `CompRefinesCliBinaryReal` and
`SignalSessionSecureReal` cover every guarded execution trace of `cliRunElf` from `initDirs`
(`CliTraces` still requires `ValidCall`, `InputsFor`, and `LeaksFrom` on every step, and
`InvertsGuarded` and `CoinsFresh` remain premises). The remaining universal quantifier is over
extern interpretations `interp` that satisfy the symbolic laws (`ExternContractsHoldCli`) and agree
with the real primitives (`RealPrimsMatch`); `RealPrimsAdmissible` asserts that such an `interp`
exists, i.e. that the real primitives obey the laws assumed by the symbolic model. -/

/-- Extern interpretation `interp` agrees with the closed primitives executed by the linked ELF
(`HooksMatchPlaced interp realCliHooks`). -/
def RealPrimsMatch (interp : ExternInterpretation) : Prop :=
  HooksMatchPlaced interp realCliHooks

/-- The real primitives obey the symbolic laws: some extern interpretation satisfies
`ExternContractsHoldCli` and agrees with `realCliHooks`. -/
def RealPrimsAdmissible : Prop :=
  ∃ interp : ExternInterpretation, ExternContractsHoldCli interp ∧ RealPrimsMatch interp

/-- ARM64 process run relation of `elf` at `.symtab`-resolved addresses `addrs` (starting from
plain `ElfImage.loadState`), without the `RealHooksAgreeOnInput` filter. The primitive parameter is
`Unit`: the ELF executes its own linked primitives (`realCliHooks`). -/
def elfRelReal (elf : ElfImage) (addrs : CliElfAddrs)
    (_interp : ExternInterpretation) (_ : Unit) :
    Inputs → Option Outcome → Prop :=
  runFnToRelation (cliRunElf elf addrs)

/-- Progress (no CPU fault, trap, or non-termination unless the run reaches a non-terminating
`SampleNTT` entry, `CliReachesSampleNttStuckElf elf addrs i`, DEV-CLI22) on every guarded `CliCall`
(`ValidCall` / `InputsFor`) at any turn reachable from `initDirs` under `elfRelReal elf addrs` (no
`RealHooksAgreeOnInput` filter), for every extern interpretation satisfying the symbolic laws and
agreeing with the real primitives. -/
def CliElfProgressReal (elf : ElfImage) (addrs : CliElfAddrs) : Prop :=
  ∀ interp : ExternInterpretation, ExternContractsHoldCli interp → RealPrimsMatch interp →
  ∀ r : ProtocolSetup, ProtocolSetupWF r →
  ∀ t : CliTurn,
    CliReachable (elfRelReal elf addrs interp ()) interp r
      (CliTurn.init (initDirs interp r)) t →
  ∀ (c : CliCall) (i : CryptoVerification.SignalSession.Inputs),
    ValidCall interp r t c → InputsFor c (t.dirs c.party) i →
    cliRunElf elf addrs i ≠ none ∨ CliReachesSampleNttStuckElf elf addrs i

/-- Whole-protocol refinement and progress for ELF image `bytes` at the real primitives: the real
primitives obey the symbolic laws (`RealPrimsAdmissible`); `bytes` parses and its 18 panic and 5
`SampleNTT` addresses resolve from `.symtab` (`resolveCliElfAddrs`); progress holds
(`CliElfProgressReal`); and every guarded execution trace of `cliRunElf` from `initDirs`
(`CliTraces` with `ValidCall` / `InputsFor` / `LeaksFrom`, and `InvertsGuarded`; no
`RealHooksAgreeOnInput` filter under `elfRelReal elf addrs`) is explained by the composed model or
hits a cryptographic collision after an explained prefix. -/
def CompRefinesCliBinaryReal (bytes : List (BitVec 8)) : Prop :=
  RealPrimsAdmissible ∧
  ∃ (elf : ElfImage) (addrs : CliElfAddrs),
    ElfImage.parse bytes = .ok elf ∧
    resolveCliElfAddrs bytes elf = .ok addrs ∧
    CliElfProgressReal elf addrs ∧
    CompRefinesCli (fun interp (_ : Unit) => RealPrimsMatch interp) (elfRelReal elf addrs)

end DY.Libsignal.Composed.Refinement.Cli
