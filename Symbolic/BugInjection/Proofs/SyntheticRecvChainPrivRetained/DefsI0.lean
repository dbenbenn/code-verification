/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0Rows
public import Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
public import Symbolic.BugInjection.Synthetic.Witnesses.RecvChainPrivRetainedCli

/-!
# Concrete Witness Interpretation `rcprI0`, Double-Leak Trace `rcprTrace`, and `rcprCompFitsPinned`

Defines the table-driven `ExternInterpretation` `rcprI0`, matching CLI hooks `rcprHooks0`,
setup records `rcprRecordsI0`, concrete opaque semantics `rcprSem0`, proof-layer pinned
predicate `rcprCompFitsPinned`, and the 8-event double-leak trace `rcprTrace` for
`RecvChainPrivRetainedCli`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0

open CryptoProofLib.Refinement (ExternInterpretation ByteString)
open DY.X25519 (isLowOrderKey uCoord)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (RunEvent EnvEvent CliEvent)
open DY.Libsignal.Refinement
  (StubSymbol x25519PublicKeySymbol x25519AgreementSymbol x25519TorsionSymbol
   aesCbcEncryptSymbol aesCbcDecryptSymbol sha256CompressSymbol sha256CompressFunction)
open DY.Libsignal.PQXDH.Refinement
  (kyberEncapsSymbol kyberDecapsSymbol
   libcruxHmacSymbol X25519TorsionShiftsRejected)
open DY.Libsignal.Composed.Refinement (ProtocolSetup OpaqueSymbolSemantics gamma leBytes secretBytes)
open DY.Libsignal.Composed.Refinement.Cli (ExternContractsHoldCli HooksMatchInterpretation)
open CryptoVerification.SignalSession (CliHooks)
open Symbolic.BugInjection (PQXDHSpqrSetup TorsionShiftsRecorded SetupMatches cliCompShape fillFresh hexBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
  (bytesToNat compTag4 compDefaultPub compDefaultDh compDefaultSha256 compDefaultHmac
   compDefaultKyberCt compDefaultKyberSs compKyberEncaps compKyberDecaps
   compHmac compOtherExtern compMlkem768FromSeed compSha512)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable (bytesToSha512StateLE)
open Symbolic.BugInjection.Proofs.Common443.CompI0Laws
  (compMlKem0 compKyberEncaps_length compKyberDecaps_length)
open Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0Rows
  (rcprSha256Bucket rcprSha256Rows rcprSha256 rcprSpqrState1 rcprSpqrState1_length)
open Symbolic.Swarm.CREF (compSemOf)

export Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0Rows
  (rcprSha256Bucket rcprSha256Rows rcprSha256 rcprSpqrState1 rcprSpqrState1_length)

/-- Witness setup `(setup_seed = 23209, rng_seed = 43, withOpk = false)`. -/
abbrev rcprSetup : PQXDHSpqrSetup :=
  Symbolic.BugInjection.Synthetic.Witnesses.RecvChainPrivRetainedCli.setup

/-- Alice's rotated-out `dhs_A0` private key (`32` bytes) retained in `receiverChains[1]`. -/
def rcprLeakKey1 : HwBytes :=
  hexBytes "202906877bd8902b3e109ef6a906769994a821adacd827f6f247ecc436154652"

theorem rcprLeakKey1_length : rcprLeakKey1.length = 32 := by decide

/-- Trailing rejected `bob recv` run event (`Call 5`, `stdin = []`, `exit = some (1, [])`). -/
def rcprStopEv : RunEvent where
  party := "bob"
  cmd := .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩
  input := []
  coins := List.replicate 32 0#8
  exit := some (1, [])

/-- The 8-event double-leak trace (`Calls 0..4`, two Alice leaks, and trailing `rcprStopEv`). -/
def rcprTrace : List CliEvent :=
  Symbolic.BugInjection.Synthetic.Witnesses.RecvChainPrivRetainedCli.trace.take 5 ++
    [ .env (.leak "alice" rcprLeakKey1),
      .env (.leak "alice" rcprSpqrState1),
      .run rcprStopEv ]

/-- The 7 recorded X25519 public keys indexed by `Fin 7`. -/
def rcprPubOfIdx (i : Fin 7) : HwBytes :=
  match i.val with
  | 0 => leBytes 32 0x3c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a
  | 1 => leBytes 32 0x627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7
  | 2 => leBytes 32 0x1814e39f6c4912ea4cff03837272d451a1ac17771cbf3a0572c2e6bc9688b8b6
  | 3 => leBytes 32 0x3876d0f225aa2d85682498e61e2fe97bc189e4815c96aee21e8218cf997b078f
  | 4 => leBytes 32 0x4ae020f0133ecd4a8abe6ff58f162cef8c18ef9d7411918dad639572eb5d1627
  | 5 => leBytes 32 0x5d3a7106880dc94921a70cd5a2b93338c35651a8a0df9a8b4166397336db25d
  | _ => leBytes 32 0x191933f5352eccec96182dee25cb6fc49f24128081a4b0215fcc626dfb5fa897

/-- Public key for an optional secret index (`compDefaultPub` on `none`). -/
def rcprPubOfOpt : Option (Fin 7) → HwBytes
  | some idx => rcprPubOfIdx idx
  | none => compDefaultPub

/-- Normalize a 32-byte clamped secret `s` to its `Fin 7` table index. -/
def rcprSecretIdx (s : HwBytes) : Option (Fin 7) :=
  if s.length == 32 then
    let n := bytesToNat s
    if n == 0x65385b1d0d73750ca8125bca3c7e3bf70682a12a5e17055929b1566240215318 then some ⟨0, by decide⟩
    else if n == 0x5e9c4282ed6763a8c28ebb7233e51d1950937b3041d5d4ac13ac2650f5f8df00 then some ⟨1, by decide⟩
    else if n == 0x6385622579df091d9039fcd19c5dd34f7a2af4f99132c5932ff0a06b4bd52080 then some ⟨2, by decide⟩
    else if n == 0x549ffe504bfdab7f6ec624aa856858679cde98852e60034bba69ec90eb4fef88 then some ⟨3, by decide⟩
    else if n == 0x52461536c4ec47f2f627d8acad21a894997606a9f69e103e2b90d87b87062920 then some ⟨4, by decide⟩
    else if n == 0x6bc2db31b837085ac90af993ad2b2fbc7357b25cdbbcecb5fc2f976ba2f56960 then some ⟨5, by decide⟩
    else if n == 0x7f62e60296fdfd995c0ef0e79e17027f62ee6dbfe35320b65c29f2075b719610 then some ⟨6, by decide⟩
    else none
  else none

/-- Map a 255-bit Montgomery `uCoord` to its `Fin 7` key index. -/
def rcprPointIdxOfU (u : Nat) : Option (Fin 7) :=
  if u == 0x3c01432d659f6956d79efdb84cf363bd3effef89cb39f4513184d598b479f75a then some ⟨0, by decide⟩
  else if u == 0x627fac8bff0348b0c032b515e585e882aa28244c58ceadfb6f2c8876f3506df7 then some ⟨1, by decide⟩
  else if u == 0x1814e39f6c4912ea4cff03837272d451a1ac17771cbf3a0572c2e6bc9688b8b6 then some ⟨2, by decide⟩
  else if u == 0x3876d0f225aa2d85682498e61e2fe97bc189e4815c96aee21e8218cf997b078f then some ⟨3, by decide⟩
  else if u == 0x4ae020f0133ecd4a8abe6ff58f162cef8c18ef9d7411918dad639572eb5d1627 then some ⟨4, by decide⟩
  else if u == 0x5d3a7106880dc94921a70cd5a2b93338c35651a8a0df9a8b4166397336db25d then some ⟨5, by decide⟩
  else if u == 0x191933f5352eccec96182dee25cb6fc49f24128081a4b0215fcc626dfb5fa897 then some ⟨6, by decide⟩
  else none

/-- Normalize a 32-byte public key point `p` to its `Fin 7` index via `uCoord`. -/
def rcprPointIdx (p : HwBytes) : Option (Fin 7) :=
  if p.length == 32 then rcprPointIdxOfU (uCoord (p.map BitVec.toNat))
  else none

/-- Full symmetric `7 × 7` X25519 agreement table on `Fin 7 × Fin 7`. -/
def rcprDhByIdx (i j : Fin 7) : HwBytes :=
  let lo := min i.val j.val
  let hi := max i.val j.val
  if lo == 0 && hi == 0 then leBytes 32 0x2fe753093abbba07396525f99f58cd936d5db206d7bf3223ffddd46f0a69fa53
  else if lo == 0 && hi == 1 then leBytes 32 0x779f82c33f39708c76a962a0dcfc700c91c3057d2fed34477380f3893ecc313e
  else if lo == 0 && hi == 2 then leBytes 32 0x2b1507edf1e8d4f38a3da9d3571b67ea7ee5b0606ab27e0c41dfd01e683e373b
  else if lo == 0 && hi == 3 then leBytes 32 0x4c2c505d344bb042bad835663e29442810149d51f4b51193f1ddd1a8bea60cb2
  else if lo == 0 && hi == 4 then leBytes 32 0x1ee9fcdc4891f0619f10d8f86500db039bed68405eddfad4e00cb2de44385136
  else if lo == 0 && hi == 5 then leBytes 32 0x7067862a01052972c242dafd83446dcd96b737d34e56e10cb29800117bf04cd5
  else if lo == 0 && hi == 6 then leBytes 32 0x67e4dcf527bb45fe8dc85ebdad0af026c3fc06cb6fd41d585c910e4c388df5ec
  else if lo == 1 && hi == 1 then leBytes 32 0x6a0303bda19674683bd79ce2858616bfb68d3431cdf3c6538fdc04e4a66e2b7
  else if lo == 1 && hi == 2 then leBytes 32 0x342ba6526f2f9e195f66f8334c73a3eeb8ea30b0824c73999e7a1aa9368fef40
  else if lo == 1 && hi == 3 then leBytes 32 0xa2243eb8bcdb7e8ea5b789c1e176f460f7589421241238bef591bd268baa0d8
  else if lo == 1 && hi == 4 then leBytes 32 0x430413f3a6c8ba1073e74ba5216d2d33fdd6f05b508f105e638926a7bbe2efe4
  else if lo == 1 && hi == 5 then leBytes 32 0x54532fc9a0177217411cb5cb120a7bcde70918cb218065c19b3809ff5255247
  else if lo == 1 && hi == 6 then leBytes 32 0x32cd5b7e65b83b22788fc146ea032ea99a2d368cf12ef60abe24a50e429e4553
  else if lo == 2 && hi == 2 then leBytes 32 0x1e67f74327f22d67ca1a097d8f69e058a6dd6c4968b909d4815b3ec2747034d6
  else if lo == 2 && hi == 3 then leBytes 32 0x7707b1a8208d0492fce5307d23fe5b81e8943766928eb6d041f35cad4df47188
  else if lo == 2 && hi == 4 then leBytes 32 0x5188500b822d529fe65cfbc87e52c5607f92b09f3dc64254c47aed0d73c65ebc
  else if lo == 2 && hi == 5 then leBytes 32 0x747941a83c4d11aec22e059392a4bb73cd84630cc437176ad2b3aafc2b5ec18e
  else if lo == 2 && hi == 6 then leBytes 32 0xd09069e4d2b6c6b8d7b7bb54701ce5b5394e941e2b5ee55f4e1aa70a3ccabc1
  else if lo == 3 && hi == 3 then leBytes 32 0x6df50b819f864c3c41ee7ef523be6dfb7a3775436e244a6222dff127bac167
  else if lo == 3 && hi == 4 then leBytes 32 0x3746e8e94f919ddeb18a41103c74a75e9ee51d2e3a6f83d29e0488fdf8694171
  else if lo == 3 && hi == 5 then leBytes 32 0x300864702f99e4d0287fb13f416d560252d2bfc301da4275af2db98569ce124d
  else if lo == 3 && hi == 6 then leBytes 32 0x528b604b9e428c60b688b1e51774abcf2490a51d8fdb9b94104f87e429dfce7a
  else if lo == 4 && hi == 4 then leBytes 32 0x6dd9b120da893f870bbee78568dc957e666f73da1384225243b971277bc83745
  else if lo == 4 && hi == 5 then leBytes 32 0x254ee5869a8a1c42dc8b4e38989885324dbdeb3d27b1f638b9b51878c60f811f
  else if lo == 4 && hi == 6 then leBytes 32 0x1c205f1757ab999e9118cdcb240a7eaa60ad4a08c1a2c861daf5f28646496463
  else if lo == 5 && hi == 5 then leBytes 32 0x73a92458b7cd70ae920dbe2314259c37a0ce9f71d1ac9f62a6188a978ddcd10b
  else if lo == 5 && hi == 6 then leBytes 32 0x1224271048156d3d4e65055d6fcb79cb90b18bcbff5888afc739328ada7f5f2a
  else if lo == 6 && hi == 6 then leBytes 32 0x241712b149e0f3071bd45d1cc53d193454d5c46b77dec1601f47faef46e398de
  else compTag4 ++ [BitVec.ofNat 8 lo, BitVec.ofNat 8 hi] ++ List.replicate 26 0x42#8

def rcprLookupPub (s : HwBytes) : HwBytes :=
  rcprPubOfOpt (rcprSecretIdx s)

def rcprLookupDh (s p : HwBytes) : HwBytes :=
  if isLowOrderKey (p.map BitVec.toNat) then
    List.replicate 32 0#8
  else
    match rcprSecretIdx s, rcprPointIdx p with
    | some i, some j => rcprDhByIdx i j
    | _, _ => compDefaultDh

def rcprAesPt0 : HwBytes := leBytes 2 0x306d
def rcprAesK0 : HwBytes := leBytes 32 0xe69af03427530a580cc1538c3b3109974a21cbfb15fbee9290dd8ed3972a021a
def rcprAesIv0 : HwBytes := leBytes 16 0x8dcedd678ff7bac2d9aa71ff7de710a6
def rcprAesCt0 : HwBytes := leBytes 16 0x2c7fc49019bb039c3639ab4942d023e6
def rcprAesA0 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨rcprAesPt0, by decide⟩ : List.Vector (BitVec 8) 2)) ^^^ CryptoGames.CBC.bytesToBlock rcprAesIv0
def rcprAesB0 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock rcprAesCt0
def rcprAesPt1 : HwBytes := leBytes 2 0x316d
def rcprAesK1 : HwBytes := leBytes 32 0x8759cbef1f2da8ffdbb7b7773b2fc89de931969fbacc107eff8398a6d7a32686
def rcprAesIv1 : HwBytes := leBytes 16 0x5081405e577b156ddea751312cda7305
def rcprAesCt1 : HwBytes := leBytes 16 0xa357eda0f7f69c6f99ba49117cef150f
def rcprAesA1 : CryptoGames.CBC.Block := ByteSpecs.bytesToBlock (ByteSpecs.pkcs7Bytes (⟨rcprAesPt1, by decide⟩ : List.Vector (BitVec 8) 2)) ^^^ CryptoGames.CBC.bytesToBlock rcprAesIv1
def rcprAesB1 : CryptoGames.CBC.Block := CryptoGames.CBC.bytesToBlock rcprAesCt1

/-- Involutive AES-256 block cipher swapping `(rcprAesA_m, rcprAesB_m)` on `rcprAesK_m`. -/
def rcprAesBlock (k : CryptoGames.CBC.AesKey) (b : CryptoGames.CBC.Block) : CryptoGames.CBC.Block :=
  if k == CryptoGames.HKDF.bytesToKey32 rcprAesK0 then
    if b == rcprAesA0 then rcprAesB0 else if b == rcprAesB0 then rcprAesA0 else b
  else if k == CryptoGames.HKDF.bytesToKey32 rcprAesK1 then
    if b == rcprAesA1 then rcprAesB1 else if b == rcprAesB1 then rcprAesA1 else b
  else b

def rcprAesPerm (k iv text : HwBytes) : HwBytes :=
  CryptoGames.LibsignalSession.aesCbcEncrypt rcprAesBlock (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) text

def rcprAesDec (k iv ct : HwBytes) : Option HwBytes :=
  CryptoGames.LibsignalSession.aesCbcDecrypt rcprAesBlock (CryptoGames.HKDF.bytesToKey32 k) (CryptoGames.CBC.bytesToBlock iv) ct

abbrev rcprKyberEncaps : HwBytes → HwBytes := compKyberEncaps
abbrev rcprKyberDecaps : HwBytes → HwBytes := compKyberDecaps
abbrev rcprHmac : HwBytes → HwBytes → HwBytes := compHmac
abbrev rcprMlkem768FromSeed : HwBytes → HwBytes := compMlkem768FromSeed

theorem rcprKyberEncaps_length (e : HwBytes) : (rcprKyberEncaps e).length = 1600 :=
  compKyberEncaps_length e
theorem rcprKyberDecaps_length (ct : HwBytes) : (rcprKyberDecaps ct).length = 32 :=
  compKyberDecaps_length ct

/-- Witness `ExternInterpretation` for `RecvChainPrivRetainedCli`. -/
def rcprI0 : ExternInterpretation :=
  fun s args =>
    if s = x25519PublicKeySymbol then
      match args with | [sk] => some (rcprLookupPub sk) | _ => none
    else if s = x25519AgreementSymbol then
      match args with | [sk, pk] => some (rcprLookupDh sk pk) | _ => none
    else if s = x25519TorsionSymbol then
      none
    else if s = aesCbcEncryptSymbol then
      match args with | [text, k, iv] => some (rcprAesPerm k iv text) | _ => none
    else if s = aesCbcDecryptSymbol then
      match args with | [ct, k, iv] => rcprAesDec k iv ct | _ => none
    else if s = kyberEncapsSymbol then
      match args with | [_, rand] => some (compKyberEncaps rand) | _ => some (compDefaultKyberCt ++ compDefaultKyberSs)
    else if s = kyberDecapsSymbol then
      match args with | [_, ct] => some (compKyberDecaps ct) | _ => some compDefaultKyberSs
    else if s = libcruxHmacSymbol then
      match args with | [k, d] => some (compHmac k d) | _ => some (compDefaultHmac [] [])
    else if s = sha256CompressSymbol then
      match args with | [st, blk] => some (rcprSha256 st blk) | _ => some (compDefaultSha256 [] [])
    else
      compOtherExtern s args

theorem rcprPubOfIdx_length (i : Fin 7) : (rcprPubOfIdx i).length = 32 := by
  revert i; decide

theorem rcprLookupPub_length (s : HwBytes) : (rcprLookupPub s).length = 32 := by
  unfold rcprLookupPub rcprPubOfOpt
  cases rcprSecretIdx s with
  | none => decide
  | some idx => exact rcprPubOfIdx_length idx

theorem rcprDhByIdx_length (i j : Fin 7) : (rcprDhByIdx i j).length = 32 := by
  revert i j; decide

theorem rcprLookupDh_length (s p : HwBytes) : (rcprLookupDh s p).length = 32 := by
  unfold rcprLookupDh
  split
  · rfl
  · cases rcprSecretIdx s <;> cases rcprPointIdx p <;> dsimp only <;>
      first | exact rcprDhByIdx_length _ _ | decide

/-- Recorded ML-KEM-768 primitives for `rcprHooks0`. -/
def rcprExecMlKem0 : CryptoVerification.LibsignalSpqrV1.MlKem :=
  { compMlKem0 with
    keyPair := fun seed => CryptoVerification.E2E.fitVec 2400 (compMlkem768FromSeed seed.toList) }

/-- Concrete CLI hooks agreeing with `rcprI0`. -/
def rcprHooks0 : CliHooks where
  C :=
    { F := sha256CompressFunction rcprI0
      E := rcprAesBlock
      D := rcprAesBlock
      X := fun a b => ⟨rcprLookupDh a.toList b.toList, rcprLookupDh_length a.toList b.toList⟩
      pubKey := fun a => ⟨rcprLookupPub a.toList, rcprLookupPub_length a.toList⟩ }
  Q :=
    { F512 := fun st blk =>
        bytesToSha512StateLE (compSha512 (CryptoVerification.E2E.sha512StateBytesLE st) blk)
      encaps := fun _ rand =>
        (⟨(compKyberEncaps rand.toList).take 1568, by
            rw [List.length_take, compKyberEncaps_length]; rfl⟩,
         ⟨(compKyberEncaps rand.toList).drop 1568, by
            rw [List.length_drop, compKyberEncaps_length]⟩)
      decaps := fun _ ct => ⟨compKyberDecaps ct.toList, compKyberDecaps_length ct.toList⟩
      K := rcprExecMlKem0 }

/-- Concrete `ProtocolSetup` of a witness setup `w` evaluated under `rcprI0`. -/
def rcprRecordsI0 (w : PQXDHSpqrSetup) : ProtocolSetup :=
  { alice := "alice", bob := "bob", withOpk := false, regIdA := w.regIdA, regIdB := w.regIdB,
    spkId := w.spkId, kpkId := w.kpkId, opkId := 0, kyberSecB := w.kyberSec, fresh := w.fresh,
    opaqueBytes := gamma rcprI0 w.compSem w.compGhost }

/-- Concrete `OpaqueSymbolSemantics` for `RecvChainPrivRetainedCli` under `rcprI0`. -/
def rcprSem0 : OpaqueSymbolSemantics :=
  compSemOf rcprI0 (rcprRecordsI0 rcprSetup)

/-- Pinned `fits` predicate for `RecvChainPrivRetainedCli` (proof layer). -/
def rcprCompFitsPinned (iw : cliCompShape.Interp) (r : ProtocolSetup) : Prop :=
  (SetupMatches rcprSetup iw.1 r ∧
    iw.1 = rcprI0 ∧
    (secretBytes r 3 = fillFresh 11 64 ∧ secretBytes r 4 = fillFresh 16 64 ∧
      secretBytes r 5 = fillFresh 17 64) ∧
    (r.alice = "alice" ∧ r.bob = "bob") ∧
    X25519TorsionShiftsRejected iw.1 ∧
    TorsionShiftsRecorded iw.1 rcprSetup.torsionShifts) ∧
  ExternContractsHoldCli iw.1 ∧
  HooksMatchInterpretation iw.1 iw.2

end Symbolic.BugInjection.Proofs.SyntheticRecvChainPrivRetained.DefsI0
