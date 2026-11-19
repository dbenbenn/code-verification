/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge

/-!
# Shared Definitions and Prefix Bridges for `SyntheticAddrKeyLeak`

Defines:
- `akSetup`, `akSetup_eq_hb`, `akSetup_eq_hbComp`, and `CliSetupMatchesPinned` / satisfiability bridges
  (`cliCompFitsPinned_ak_of_hb`, `cliCompFitsPinned_satisfiable_ak`, `compFitsPinned_hbComp_of_ak`,
  `compFitsPinned_hbCli_of_ak`) to `Cheval26SmallSubgroupHighBitCli.setup` (`(23209, 41)`).
- Fast WHNF concrete byte lists (`bunBytes`, `coins0`, `pt1`, `coins1`, `sentWire1`,
  `carrierSentWire1` / `c1Out`) avoiding slow kernel `hexBytes` string reduction.
- Both the recorded witness trace `akTrace` (`AddrKeyLeakCli.trace`) and the `(compI0, compHooks0)`
  carrier trace `akCarrierTrace` (definitionally `rfl`-equal to `ImplTrace.akCarrierTrace`),
  together with `evInit`, parameterized `evSendWithExit` / `evSendOf (out1 : HwBytes)` /
  `akEvents (out1 : HwBytes)`, `evSend`, `evSendCarrier`, `cliEvents`, `cliEventsCarrier`,
  `cliEvents_eq : cliEvents = akTrace`, and `akEvents_carrier_eq : akEvents carrierSentWire1 = akCarrierTrace`.
- `BreakFree`, `SchedFits`, `list_eq_two_splits`, and `runWrapped` lemmas for 1-call and 2-call prefixes.
- Call 0 `initiateDrawsOfCoins` / `init_exit0_cut_eq` and 14-byte RNG length bounds for
  `NoSendCollision` and `NoFullExplains`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.Defs

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.Defs (callsOf SchedFits flatEvents)
open Symbolic.Proofs.Swarm.UA.ClassicalBridge (BreakFree breakFree_nil)
open Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0)
open Symbolic.BugInjection.Proofs.Common.CompFitsSatisfiable
  (CliSetupMatchesPinned cliSetupMatchesPinned_satisfiable_hb)
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Common443.CliCoinSplitClose
  (cliCoins0 cliCoins0_length initiateDrawsOfCoins_cliCoins0_eq init_draws_cliCoins0_eq_hb)
open Symbolic.BugInjection.Proofs.Common443.CliEventBridge (breakFree_cons_run)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443
  (bundleBytes call0RngEvents trace_take_35_eq rngEkBytes rngDhsBytes
   call0RngEvents_take_1_eq call0RngEvents_drop_33_eq rngEkBytes_length rngDhsBytes_length)
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge (nil_eq_hexBytes)
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED

/-! ## 1. Witness Aliases & `CliSetupMatchesPinned` Bridges to `(23209, 41)` -/

/-- Setup of `synthetic-addr-key-leak-cli`. -/
abbrev akSetup : PQXDHSpqrSetup :=
  Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli.setup

/-- Recorded structured CLI event trace of `synthetic-addr-key-leak-cli`. -/
abbrev akTrace : List CliEvent :=
  Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli.trace

/-- Schedule participant list (`["alice", "alice", "bob"]`) covering the 2-call trace. -/
abbrev akWho : List Participant :=
  Witnesses.Cheval26SmallSubgroupHighBitComp.who

/-- Schedule success predicate (`fun _ => true`) covering the 2-call trace. -/
abbrev akOk : Nat → Bool :=
  Witnesses.Cheval26SmallSubgroupHighBitComp.ok

/-- `akSetup` is identical to `Cheval26SmallSubgroupHighBitCli.setup` except `kyberCts = []`
(Bob never runs `recv` in the 2-call `addr-key-leak` trace). -/
theorem akSetup_eq_hb :
    akSetup = { Witnesses.Cheval26SmallSubgroupHighBitCli.setup with kyberCts := [] } := rfl

/-- `akSetup` is also identical to `Cheval26SmallSubgroupHighBitComp.setup` except `kyberCts = []`. -/
theorem akSetup_eq_hbComp :
    akSetup = { Witnesses.Cheval26SmallSubgroupHighBitComp.setup with kyberCts := [] } := rfl

/-- Any `(i, r)` fitting `Cheval26SmallSubgroupHighBitCli.setup` fits `akSetup` (`kyberCts = []`). -/
theorem compFits_ak_of_hb {i : ExternInterpretation} {r : ProtocolSetup}
    (h : SetupMatches Witnesses.Cheval26SmallSubgroupHighBitCli.setup i r) :
    SetupMatches akSetup i r := by
  rw [akSetup_eq_hb]
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, fun _ hmem => nomatch hmem⟩

/-- Any `(i, r)` satisfying `compFitsPinned` on `Cheval26SmallSubgroupHighBitCli.setup` satisfies it
on `akSetup`. -/
theorem compFitsPinned_ak_of_hb {i : ExternInterpretation} {r : ProtocolSetup}
    (h : compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitCli.setup i r) :
    compFitsPinned akSetup i r :=
  ⟨compFits_ak_of_hb h.1, h.2⟩

/-- Any `(iw, r)` satisfying `CliSetupMatchesPinned` on `Cheval26SmallSubgroupHighBitCli.setup`
satisfies it on `akSetup`. -/
theorem cliCompFitsPinned_ak_of_hb
    {iw : cliCompShape.Interp} {r : ProtocolSetup}
    (h : CliSetupMatchesPinned Witnesses.Cheval26SmallSubgroupHighBitCli.setup iw r) :
    CliSetupMatchesPinned akSetup iw r :=
  ⟨compFitsPinned_ak_of_hb h.1, h.2⟩

/-- Non-vacuity of `CliSetupMatchesPinned akSetup`, bridged directly from
`cliSetupMatchesPinned_satisfiable_hb`. -/
theorem cliCompFitsPinned_satisfiable_ak :
    ∃ iw r, CliSetupMatchesPinned akSetup iw r :=
  let ⟨iw, r, h⟩ := cliSetupMatchesPinned_satisfiable_hb
  ⟨iw, r, cliCompFitsPinned_ak_of_hb h⟩

/-- Under `compI0`, `SetupMatches akSetup compI0 r` upgrades to `Cheval26SmallSubgroupHighBitComp.setup`
via `CompI0Laws.compI0_kyberCorrectOn`. -/
theorem compFits_hbComp_of_ak {r : ProtocolSetup}
    (h : SetupMatches akSetup compI0 r) :
    SetupMatches Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    CompI0Laws.compI0_kyberCorrectOn r Witnesses.Cheval26SmallSubgroupHighBitComp.setup.kyberCts⟩

/-- Under `compI0`, `compFitsPinned akSetup compI0 r` upgrades to
`Cheval26SmallSubgroupHighBitComp.setup`. -/
theorem compFitsPinned_hbComp_of_ak {r : ProtocolSetup}
    (h : compFitsPinned akSetup compI0 r) :
    compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r :=
  ⟨compFits_hbComp_of_ak h.1, h.2⟩

/-- Under `compI0`, `compFitsPinned akSetup compI0 r` also upgrades to
`Cheval26SmallSubgroupHighBitCli.setup`. -/
theorem compFitsPinned_hbCli_of_ak {r : ProtocolSetup}
    (h : compFitsPinned akSetup compI0 r) :
    compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitCli.setup compI0 r := by
  have hcomp := compFitsPinned_hbComp_of_ak h
  exact ⟨⟨hcomp.1.1, hcomp.1.2.1, hcomp.1.2.2.1, hcomp.1.2.2.2.1, hcomp.1.2.2.2.2.1,
    hcomp.1.2.2.2.2.2.1, hcomp.1.2.2.2.2.2.2.1, hcomp.1.2.2.2.2.2.2.2.1,
    hcomp.1.2.2.2.2.2.2.2.2.1, hcomp.1.2.2.2.2.2.2.2.2.2.1,
    hcomp.1.2.2.2.2.2.2.2.2.2.2.1, hcomp.1.2.2.2.2.2.2.2.2.2.2.2.1,
    hcomp.1.2.2.2.2.2.2.2.2.2.2.2.2.1, hcomp.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hcomp.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    CompI0Laws.compI0_kyberCorrectOn r Witnesses.Cheval26SmallSubgroupHighBitCli.setup.kyberCts⟩,
    hcomp.2⟩

/-! ## 2. Fast Concrete Byte Definitions & `hexBytes` Equalities -/

private def hexBytesChars (cs : List Char) : HwBytes :=
  Symbolic.BugInjection.hexBytes.go
    (fun c => if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10) cs

private theorem hexBytes_eq_hexBytesChars (s : String) : hexBytes s = hexBytesChars s.toList := rfl

attribute [local irreducible] Symbolic.BugInjection.hexBytes

private theorem hexBytes_of_ofList (s : String) (cs : List Char) (bs : HwBytes)
    (hs : s = String.ofList cs) (hb : hexBytesChars cs = bs) : hexBytes s = bs := by
  rw [hexBytes_eq_hexBytesChars, hs, String.toList_ofList, hb]

/-- Call 0 bundle input bytes (1813 bytes, shared with `Cheval26SmallSubgroupHighBitCli`). -/
abbrev bunBytes : HwBytes := CompRX0SS38.bunBytes

/-- Call 0 RNG coins (192 bytes, shared with `Cheval26SmallSubgroupHighBitCli`). -/
abbrev coins0 : HwBytes := cliCoins0

theorem bunBytes_eq_bundleBytes : bunBytes = bundleBytes :=
  CompRX0SS38.bunBytes_eq_hex.trans
    Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.bundleBytes_eq_hex.symm

theorem bunBytes_eq_fast : bunBytes = CompRX0SS38.bunFast := CompRX0SS38.bunBytes_eq

theorem bunBytes_getElem4_ne_one : bunBytes[4]? ≠ some 1#8 := CompRX0SS38.bunBytes_getElem4_ne

theorem coins0_length : coins0.length = 192 := cliCoins0_length

/-- Helper indexing `AddrKeyLeakCli.trace` identically to `ImplTrace.rawRunAt`. -/
def rawRunAt (k : Nat) : RunEvent := match akTrace[k]? with
  | some (.run ev) => ev | _ => { party := "", cmd := .send ⟨"", 0⟩, input := [], coins := [], exit := none }

section FastAkHex
open Lean Meta Elab

private meta def hexDigitVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

private meta def parseHexStr (s : String) : List UInt8 :=
  let rec go : List Char → List UInt8
    | a :: b :: rest => UInt8.ofNat (16 * hexDigitVal a + hexDigitVal b) :: go rest
    | _ => []
  go s.toList

private meta def buildByteListExpr (s : String) : Expr := Id.run do
  let bv8Ty := mkApp (mkConst ``BitVec) (mkNatLit 8)
  let mut bsExpr := mkApp (mkConst ``List.nil [0]) bv8Ty
  for b in (parseHexStr s).reverse do
    bsExpr := mkApp3 (mkConst ``List.cons [0]) bv8Ty
      (mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit b.toNat)) bsExpr
  return bsExpr

private meta def buildCharListExpr (s : String) : Expr := Id.run do
  let charTy := mkConst ``Char
  let mut csExpr := mkApp (mkConst ``List.nil [0]) charTy
  for c in s.toList.reverse do
    csExpr := mkApp3 (mkConst ``List.cons [0]) charTy (toExpr c) csExpr
  return csExpr

local elab "fast_str_chunks " "[" chunks:str,* "]" : term => do
  let strs := chunks.getElems.map (·.getString)
  return mkStrLit (String.join strs.toList)

local elab "fast_chars_chunks " "[" chunks:str,* "]" : term => do
  let strs := chunks.getElems.map (·.getString)
  return buildCharListExpr (String.join strs.toList)

local elab "fast_hex_chunks " "[" chunks:str,* "]" : term => do
  let strs := chunks.getElems.map (·.getString)
  return buildByteListExpr (String.join strs.toList)

/-- Call 1 plaintext input bytes (`"attack-at-dawn"`, 14 bytes) as an explicit `List (BitVec 8)`. -/
def pt1 : HwBytes := fast_hex_chunks ["61747461636b2d61742d6461776e"]

private def pt1Chars : List Char := fast_chars_chunks ["61747461636b2d61742d6461776e"]

private theorem pt1Str_eq :
    "61747461636b2d61742d6461776e" = String.ofList pt1Chars := rfl

private theorem pt1_eq_go : pt1 = hexBytesChars pt1Chars := rfl

theorem pt1_eq_hex :
    pt1 = hexBytes "61747461636b2d61742d6461776e" :=
  (hexBytes_of_ofList _ pt1Chars pt1 pt1Str_eq pt1_eq_go.symm).symm

/-- Call 1 RNG coins (64 bytes) as an explicit `List (BitVec 8)`. -/
def coins1 : HwBytes := fast_hex_chunks [
  "23251f46b973b8989c462587d02a8056f38d75b313c67290aa215b5b52df0e3e",
  "e1f2c0f23cdbb316da32ab9063b3f652f24ac6d065a0889afbc534bb1e4b9fd2"
]

private def coins1Chars : List Char := fast_chars_chunks [
  "23251f46b973b8989c462587d02a8056f38d75b313c67290aa215b5b52df0e3e",
  "e1f2c0f23cdbb316da32ab9063b3f652f24ac6d065a0889afbc534bb1e4b9fd2"
]

private theorem coins1Str_eq :
    "23251f46b973b8989c462587d02a8056f38d75b313c67290aa215b5b52df0e3ee1f2c0f23cdbb316da32ab9063b3f652f24ac6d065a0889afbc534bb1e4b9fd2" =
      String.ofList coins1Chars := rfl

private theorem coins1_eq_go : coins1 = hexBytesChars coins1Chars := rfl

theorem coins1_eq_hex :
    coins1 = hexBytes "23251f46b973b8989c462587d02a8056f38d75b313c67290aa215b5b52df0e3ee1f2c0f23cdbb316da32ab9063b3f652f24ac6d065a0889afbc534bb1e4b9fd2" :=
  (hexBytes_of_ofList _ coins1Chars coins1 coins1Str_eq coins1_eq_go.symm).symm

/-- Recorded Call 1 wire output from `AddrKeyLeakCli.trace` (1793 bytes; `PreKeySignalMessage`
whose inner `SignalMessage` carries the leaked 32-byte `mac_key` in protobuf field 6 `addresses`). -/
def sentWire1 : HwBytes := fast_hex_chunks [
  "0344122105abbb904f2c8f86f71332b8059313b1a1cbad7b332d85927b485e5b0e1049c34d1a21055af779b498d58431",
  "51f439cb89efff3ebd63f34cb8fd9ed756699f652d43013c228b01440a21055bfc85a3b08f59137240d42fa1308096a3",
  "7310c86b3ae2bc820d6f0a37bfd33f1000180022105d39d22c8e42d0097d83a24f37a815a12a250101010100a518128c",
  "bc63e038164b1444fc00f02030c1ecf98b5280e74c1797e90fdd8c0b32201403bc82778fd9489def4369b2b2a42e1eba",
  "b71399687b024763c897eb8606faea2972a32e6a8c2a28d7083007380942a10c08e4c87208b89cf86e9f0584d1063a8e",
  "590e86e6dc92a2963fcfc5190bea64ad77c1b00446f39ab4e84f40370361ac1f2c79d913584db9f25bdd9d6a527453a8",
  "e849328757bd6a38eae1365a997fcbaf08af459f9ec572fea1a21a3a2994a9414f5337d0f8278bfd2b9adb5eacf6b704",
  "92bf4c1bb83ccbeb33ee2436f0a74863b64acb078bb3a1a0109e41b60c136c71ce64aa93efddf6db1cac587bed4441f6",
  "a34b33c5180a24e4b669689e82539428d9ecbe73ee8e45fb077088c1d837b16f814ddd8532161c29cb90732e1d16def7",
  "07c1224c41040f01a526f1a1944eb85b52fddcd7801b1ba4c88e1339c0c16112f42ffb2d7d05a10152b2747346ad389e",
  "f89da26911506d53debd9091a355766fe3827a5826af45fa9566d1c7887ebdfe4050ebb12e4d9b4209396e6604d3c057",
  "9a921e5deb94110f89b72e855785548b946fd3ddc1d83041db4ba25fa7bd324a9aaeb360f2836a78bba284018452a076",
  "ea80d33f29005c44b69f95a1645c79bf64277e3dfcae4562cbd62c154cf4223fc19d82a598cee37c7bd0aa01701dde3f",
  "c8aeadf46ef74d72ff16bc4c6aa3ae4b0d8ee943ddc26b48c72be45f4d7b04fe03bc17f6ea2c4f137fbf619ce00c54db",
  "2edf2c284ebbfa77c49212b906c34a6cf6a0c4f3dea419eb01649a144b299a1514cbcea84c374ca0e8e5d96c6bb347f2",
  "add5c89ac76c57cd3831662c1e69eb464e6c41d9113dfc028fb470bc0b49da019a39a7892990a4c580ac0bb3c7a9a896",
  "fd802534e5c3e2a14ddca97a064024857dbeca8fe008632e7bfc5009fd92338392f2441776f9fa15b7e304b97932c15e",
  "7b1126f7038c99297ca0dd70ddc5e409d7730cd3d63fec5668a899e2077c7095629105bc578421343adefdf8aad3cc5a",
  "1294bfd81ee51a19d4c1926272d5a0d8b365125d7482cf841856350808cee631c3e02b3bbdc360dab688eda5b1a2de3f",
  "9dc0602aeffba073db5abcf27f6ba41f1babc42ff3257be7fcd95d58b2d1d74ba497f766136c552df6bc17d30861ed79",
  "b13b99d23d4cb41f4b180b5f6cd3ced4c31a84290e6b458aa37b5f0343db1352e37188b6febd98acfd34031685be79f0",
  "219d13a038daf0a25fd5ba66b836ac4716b0c157e790dcb7a3725a52bb32158c8ba506c0c41e31117ce216ff8bb88267",
  "89cb593bb035bf339d3a4a6e2f4369ed959f3358e94c8e05f916d9fae8a8b7db96ffcefd62a9bee5c009f255a2ccfee5",
  "f5dda2d83fce4b0a577b5bf016954c8f194d2cec61b9dd47231abcbec28b77f183127208c6f687287a1a6bf6477338c2",
  "ae44e3f89368f0f0c07dd4a33ec844ab3179ef49c8c63e1426aca9a516b85e77bd4e3866072b10dc1ee056798f38ae1c",
  "f1b5454d6d444ca00f7d9d43eaddda5b1337e49010ca484c0b7d264ee590ed0a0d277fe8267e768e5c54b4b1f3bc9dd6",
  "857849d091545b4742d45572c90680b6077a97075b09129e05c452d19ad8d83832b5c90c81dcc058fad109ecd1bcb6fc",
  "9850538dcb5e7dc205caf79bc136d42418a00293ca17f1bbd289d60c80a08977f311674b1457b4886fecc8b107dd51c9",
  "094e0287a839acdeb4b0c87524907e185f92973ecbfa94f90f50c07e2228de59f43ef56ed2cbf1da6505b810c4b532d1",
  "5ef7650af97d5e3259fa72b457e8e7ac8cb6bc1687eeeb6743526eac6a92b75746cfbab9beb3afa9a2d80dd6a5b80d73",
  "727a8bc5377e64fa3c4562c961747ced26ed3099e3192e9483e9d89e3631f1abe44c02bcb601225fdd30448a19b04364",
  "c18959c0d3e6acfcf6775c345b1cda2ce379825942ffa992c9364d6e5efefd562aec150135d9a24c08ee8577d5a7194a",
  "9f4e43d937d62889fa64a14c43dbcfe0c2dd580c3aa214b9f35644379de6d1b4b5715c2a67d9c6ad4e1fd66e527b6c79",
  "f68cea073b012ee66cc90facd32b9bf2d654bb8882de316312b893894ef7d5e737a89196ec5cdda1d282058f7f792cf7",
  "ed6f53bfa3f0d29c5dcc11a03f15f95045bae9a2ad8fae5604492b3a7137a7b49d32ac95dbb36654dcffc11b350522b3",
  "2f96a31f2ee8f57222dc1928a51b60de60b5d1cb36d6551129cb6cc853e950c490ea8183128e16af7b2e00ec40a00bfd",
  "84dcb09dcebd3a74374470632907002adbb2736d513f303a901a50b03cf0c6b2349e6cffe60f7626e6a124182a37acad",
  "7fea8cb7e482e5be5ad2a6a8c7df962ab4"
]

private def sentWire1HexStr : String := fast_str_chunks [
  "0344122105abbb904f2c8f86f71332b8059313b1a1cbad7b332d85927b485e5b0e1049c34d1a21055af779b498d58431",
  "51f439cb89efff3ebd63f34cb8fd9ed756699f652d43013c228b01440a21055bfc85a3b08f59137240d42fa1308096a3",
  "7310c86b3ae2bc820d6f0a37bfd33f1000180022105d39d22c8e42d0097d83a24f37a815a12a250101010100a518128c",
  "bc63e038164b1444fc00f02030c1ecf98b5280e74c1797e90fdd8c0b32201403bc82778fd9489def4369b2b2a42e1eba",
  "b71399687b024763c897eb8606faea2972a32e6a8c2a28d7083007380942a10c08e4c87208b89cf86e9f0584d1063a8e",
  "590e86e6dc92a2963fcfc5190bea64ad77c1b00446f39ab4e84f40370361ac1f2c79d913584db9f25bdd9d6a527453a8",
  "e849328757bd6a38eae1365a997fcbaf08af459f9ec572fea1a21a3a2994a9414f5337d0f8278bfd2b9adb5eacf6b704",
  "92bf4c1bb83ccbeb33ee2436f0a74863b64acb078bb3a1a0109e41b60c136c71ce64aa93efddf6db1cac587bed4441f6",
  "a34b33c5180a24e4b669689e82539428d9ecbe73ee8e45fb077088c1d837b16f814ddd8532161c29cb90732e1d16def7",
  "07c1224c41040f01a526f1a1944eb85b52fddcd7801b1ba4c88e1339c0c16112f42ffb2d7d05a10152b2747346ad389e",
  "f89da26911506d53debd9091a355766fe3827a5826af45fa9566d1c7887ebdfe4050ebb12e4d9b4209396e6604d3c057",
  "9a921e5deb94110f89b72e855785548b946fd3ddc1d83041db4ba25fa7bd324a9aaeb360f2836a78bba284018452a076",
  "ea80d33f29005c44b69f95a1645c79bf64277e3dfcae4562cbd62c154cf4223fc19d82a598cee37c7bd0aa01701dde3f",
  "c8aeadf46ef74d72ff16bc4c6aa3ae4b0d8ee943ddc26b48c72be45f4d7b04fe03bc17f6ea2c4f137fbf619ce00c54db",
  "2edf2c284ebbfa77c49212b906c34a6cf6a0c4f3dea419eb01649a144b299a1514cbcea84c374ca0e8e5d96c6bb347f2",
  "add5c89ac76c57cd3831662c1e69eb464e6c41d9113dfc028fb470bc0b49da019a39a7892990a4c580ac0bb3c7a9a896",
  "fd802534e5c3e2a14ddca97a064024857dbeca8fe008632e7bfc5009fd92338392f2441776f9fa15b7e304b97932c15e",
  "7b1126f7038c99297ca0dd70ddc5e409d7730cd3d63fec5668a899e2077c7095629105bc578421343adefdf8aad3cc5a",
  "1294bfd81ee51a19d4c1926272d5a0d8b365125d7482cf841856350808cee631c3e02b3bbdc360dab688eda5b1a2de3f",
  "9dc0602aeffba073db5abcf27f6ba41f1babc42ff3257be7fcd95d58b2d1d74ba497f766136c552df6bc17d30861ed79",
  "b13b99d23d4cb41f4b180b5f6cd3ced4c31a84290e6b458aa37b5f0343db1352e37188b6febd98acfd34031685be79f0",
  "219d13a038daf0a25fd5ba66b836ac4716b0c157e790dcb7a3725a52bb32158c8ba506c0c41e31117ce216ff8bb88267",
  "89cb593bb035bf339d3a4a6e2f4369ed959f3358e94c8e05f916d9fae8a8b7db96ffcefd62a9bee5c009f255a2ccfee5",
  "f5dda2d83fce4b0a577b5bf016954c8f194d2cec61b9dd47231abcbec28b77f183127208c6f687287a1a6bf6477338c2",
  "ae44e3f89368f0f0c07dd4a33ec844ab3179ef49c8c63e1426aca9a516b85e77bd4e3866072b10dc1ee056798f38ae1c",
  "f1b5454d6d444ca00f7d9d43eaddda5b1337e49010ca484c0b7d264ee590ed0a0d277fe8267e768e5c54b4b1f3bc9dd6",
  "857849d091545b4742d45572c90680b6077a97075b09129e05c452d19ad8d83832b5c90c81dcc058fad109ecd1bcb6fc",
  "9850538dcb5e7dc205caf79bc136d42418a00293ca17f1bbd289d60c80a08977f311674b1457b4886fecc8b107dd51c9",
  "094e0287a839acdeb4b0c87524907e185f92973ecbfa94f90f50c07e2228de59f43ef56ed2cbf1da6505b810c4b532d1",
  "5ef7650af97d5e3259fa72b457e8e7ac8cb6bc1687eeeb6743526eac6a92b75746cfbab9beb3afa9a2d80dd6a5b80d73",
  "727a8bc5377e64fa3c4562c961747ced26ed3099e3192e9483e9d89e3631f1abe44c02bcb601225fdd30448a19b04364",
  "c18959c0d3e6acfcf6775c345b1cda2ce379825942ffa992c9364d6e5efefd562aec150135d9a24c08ee8577d5a7194a",
  "9f4e43d937d62889fa64a14c43dbcfe0c2dd580c3aa214b9f35644379de6d1b4b5715c2a67d9c6ad4e1fd66e527b6c79",
  "f68cea073b012ee66cc90facd32b9bf2d654bb8882de316312b893894ef7d5e737a89196ec5cdda1d282058f7f792cf7",
  "ed6f53bfa3f0d29c5dcc11a03f15f95045bae9a2ad8fae5604492b3a7137a7b49d32ac95dbb36654dcffc11b350522b3",
  "2f96a31f2ee8f57222dc1928a51b60de60b5d1cb36d6551129cb6cc853e950c490ea8183128e16af7b2e00ec40a00bfd",
  "84dcb09dcebd3a74374470632907002adbb2736d513f303a901a50b03cf0c6b2349e6cffe60f7626e6a124182a37acad",
  "7fea8cb7e482e5be5ad2a6a8c7df962ab4"
]

set_option maxRecDepth 200000 in
private def sentWire1Chars : List Char := fast_chars_chunks [
  "0344122105abbb904f2c8f86f71332b8059313b1a1cbad7b332d85927b485e5b0e1049c34d1a21055af779b498d58431",
  "51f439cb89efff3ebd63f34cb8fd9ed756699f652d43013c228b01440a21055bfc85a3b08f59137240d42fa1308096a3",
  "7310c86b3ae2bc820d6f0a37bfd33f1000180022105d39d22c8e42d0097d83a24f37a815a12a250101010100a518128c",
  "bc63e038164b1444fc00f02030c1ecf98b5280e74c1797e90fdd8c0b32201403bc82778fd9489def4369b2b2a42e1eba",
  "b71399687b024763c897eb8606faea2972a32e6a8c2a28d7083007380942a10c08e4c87208b89cf86e9f0584d1063a8e",
  "590e86e6dc92a2963fcfc5190bea64ad77c1b00446f39ab4e84f40370361ac1f2c79d913584db9f25bdd9d6a527453a8",
  "e849328757bd6a38eae1365a997fcbaf08af459f9ec572fea1a21a3a2994a9414f5337d0f8278bfd2b9adb5eacf6b704",
  "92bf4c1bb83ccbeb33ee2436f0a74863b64acb078bb3a1a0109e41b60c136c71ce64aa93efddf6db1cac587bed4441f6",
  "a34b33c5180a24e4b669689e82539428d9ecbe73ee8e45fb077088c1d837b16f814ddd8532161c29cb90732e1d16def7",
  "07c1224c41040f01a526f1a1944eb85b52fddcd7801b1ba4c88e1339c0c16112f42ffb2d7d05a10152b2747346ad389e",
  "f89da26911506d53debd9091a355766fe3827a5826af45fa9566d1c7887ebdfe4050ebb12e4d9b4209396e6604d3c057",
  "9a921e5deb94110f89b72e855785548b946fd3ddc1d83041db4ba25fa7bd324a9aaeb360f2836a78bba284018452a076",
  "ea80d33f29005c44b69f95a1645c79bf64277e3dfcae4562cbd62c154cf4223fc19d82a598cee37c7bd0aa01701dde3f",
  "c8aeadf46ef74d72ff16bc4c6aa3ae4b0d8ee943ddc26b48c72be45f4d7b04fe03bc17f6ea2c4f137fbf619ce00c54db",
  "2edf2c284ebbfa77c49212b906c34a6cf6a0c4f3dea419eb01649a144b299a1514cbcea84c374ca0e8e5d96c6bb347f2",
  "add5c89ac76c57cd3831662c1e69eb464e6c41d9113dfc028fb470bc0b49da019a39a7892990a4c580ac0bb3c7a9a896",
  "fd802534e5c3e2a14ddca97a064024857dbeca8fe008632e7bfc5009fd92338392f2441776f9fa15b7e304b97932c15e",
  "7b1126f7038c99297ca0dd70ddc5e409d7730cd3d63fec5668a899e2077c7095629105bc578421343adefdf8aad3cc5a",
  "1294bfd81ee51a19d4c1926272d5a0d8b365125d7482cf841856350808cee631c3e02b3bbdc360dab688eda5b1a2de3f",
  "9dc0602aeffba073db5abcf27f6ba41f1babc42ff3257be7fcd95d58b2d1d74ba497f766136c552df6bc17d30861ed79",
  "b13b99d23d4cb41f4b180b5f6cd3ced4c31a84290e6b458aa37b5f0343db1352e37188b6febd98acfd34031685be79f0",
  "219d13a038daf0a25fd5ba66b836ac4716b0c157e790dcb7a3725a52bb32158c8ba506c0c41e31117ce216ff8bb88267",
  "89cb593bb035bf339d3a4a6e2f4369ed959f3358e94c8e05f916d9fae8a8b7db96ffcefd62a9bee5c009f255a2ccfee5",
  "f5dda2d83fce4b0a577b5bf016954c8f194d2cec61b9dd47231abcbec28b77f183127208c6f687287a1a6bf6477338c2",
  "ae44e3f89368f0f0c07dd4a33ec844ab3179ef49c8c63e1426aca9a516b85e77bd4e3866072b10dc1ee056798f38ae1c",
  "f1b5454d6d444ca00f7d9d43eaddda5b1337e49010ca484c0b7d264ee590ed0a0d277fe8267e768e5c54b4b1f3bc9dd6",
  "857849d091545b4742d45572c90680b6077a97075b09129e05c452d19ad8d83832b5c90c81dcc058fad109ecd1bcb6fc",
  "9850538dcb5e7dc205caf79bc136d42418a00293ca17f1bbd289d60c80a08977f311674b1457b4886fecc8b107dd51c9",
  "094e0287a839acdeb4b0c87524907e185f92973ecbfa94f90f50c07e2228de59f43ef56ed2cbf1da6505b810c4b532d1",
  "5ef7650af97d5e3259fa72b457e8e7ac8cb6bc1687eeeb6743526eac6a92b75746cfbab9beb3afa9a2d80dd6a5b80d73",
  "727a8bc5377e64fa3c4562c961747ced26ed3099e3192e9483e9d89e3631f1abe44c02bcb601225fdd30448a19b04364",
  "c18959c0d3e6acfcf6775c345b1cda2ce379825942ffa992c9364d6e5efefd562aec150135d9a24c08ee8577d5a7194a",
  "9f4e43d937d62889fa64a14c43dbcfe0c2dd580c3aa214b9f35644379de6d1b4b5715c2a67d9c6ad4e1fd66e527b6c79",
  "f68cea073b012ee66cc90facd32b9bf2d654bb8882de316312b893894ef7d5e737a89196ec5cdda1d282058f7f792cf7",
  "ed6f53bfa3f0d29c5dcc11a03f15f95045bae9a2ad8fae5604492b3a7137a7b49d32ac95dbb36654dcffc11b350522b3",
  "2f96a31f2ee8f57222dc1928a51b60de60b5d1cb36d6551129cb6cc853e950c490ea8183128e16af7b2e00ec40a00bfd",
  "84dcb09dcebd3a74374470632907002adbb2736d513f303a901a50b03cf0c6b2349e6cffe60f7626e6a124182a37acad",
  "7fea8cb7e482e5be5ad2a6a8c7df962ab4"
]

set_option maxRecDepth 200000 in
private theorem sentWire1HexStr_eq : sentWire1HexStr = String.ofList sentWire1Chars := rfl

set_option maxRecDepth 200000 in
private theorem sentWire1_eq_go : sentWire1 = hexBytesChars sentWire1Chars := rfl

theorem sentWire1_eq_hex :
    sentWire1 = hexBytes (fast_str_chunks [
      "0344122105abbb904f2c8f86f71332b8059313b1a1cbad7b332d85927b485e5b0e1049c34d1a21055af779b498d58431",
      "51f439cb89efff3ebd63f34cb8fd9ed756699f652d43013c228b01440a21055bfc85a3b08f59137240d42fa1308096a3",
      "7310c86b3ae2bc820d6f0a37bfd33f1000180022105d39d22c8e42d0097d83a24f37a815a12a250101010100a518128c",
      "bc63e038164b1444fc00f02030c1ecf98b5280e74c1797e90fdd8c0b32201403bc82778fd9489def4369b2b2a42e1eba",
      "b71399687b024763c897eb8606faea2972a32e6a8c2a28d7083007380942a10c08e4c87208b89cf86e9f0584d1063a8e",
      "590e86e6dc92a2963fcfc5190bea64ad77c1b00446f39ab4e84f40370361ac1f2c79d913584db9f25bdd9d6a527453a8",
      "e849328757bd6a38eae1365a997fcbaf08af459f9ec572fea1a21a3a2994a9414f5337d0f8278bfd2b9adb5eacf6b704",
      "92bf4c1bb83ccbeb33ee2436f0a74863b64acb078bb3a1a0109e41b60c136c71ce64aa93efddf6db1cac587bed4441f6",
      "a34b33c5180a24e4b669689e82539428d9ecbe73ee8e45fb077088c1d837b16f814ddd8532161c29cb90732e1d16def7",
      "07c1224c41040f01a526f1a1944eb85b52fddcd7801b1ba4c88e1339c0c16112f42ffb2d7d05a10152b2747346ad389e",
      "f89da26911506d53debd9091a355766fe3827a5826af45fa9566d1c7887ebdfe4050ebb12e4d9b4209396e6604d3c057",
      "9a921e5deb94110f89b72e855785548b946fd3ddc1d83041db4ba25fa7bd324a9aaeb360f2836a78bba284018452a076",
      "ea80d33f29005c44b69f95a1645c79bf64277e3dfcae4562cbd62c154cf4223fc19d82a598cee37c7bd0aa01701dde3f",
      "c8aeadf46ef74d72ff16bc4c6aa3ae4b0d8ee943ddc26b48c72be45f4d7b04fe03bc17f6ea2c4f137fbf619ce00c54db",
      "2edf2c284ebbfa77c49212b906c34a6cf6a0c4f3dea419eb01649a144b299a1514cbcea84c374ca0e8e5d96c6bb347f2",
      "add5c89ac76c57cd3831662c1e69eb464e6c41d9113dfc028fb470bc0b49da019a39a7892990a4c580ac0bb3c7a9a896",
      "fd802534e5c3e2a14ddca97a064024857dbeca8fe008632e7bfc5009fd92338392f2441776f9fa15b7e304b97932c15e",
      "7b1126f7038c99297ca0dd70ddc5e409d7730cd3d63fec5668a899e2077c7095629105bc578421343adefdf8aad3cc5a",
      "1294bfd81ee51a19d4c1926272d5a0d8b365125d7482cf841856350808cee631c3e02b3bbdc360dab688eda5b1a2de3f",
      "9dc0602aeffba073db5abcf27f6ba41f1babc42ff3257be7fcd95d58b2d1d74ba497f766136c552df6bc17d30861ed79",
      "b13b99d23d4cb41f4b180b5f6cd3ced4c31a84290e6b458aa37b5f0343db1352e37188b6febd98acfd34031685be79f0",
      "219d13a038daf0a25fd5ba66b836ac4716b0c157e790dcb7a3725a52bb32158c8ba506c0c41e31117ce216ff8bb88267",
      "89cb593bb035bf339d3a4a6e2f4369ed959f3358e94c8e05f916d9fae8a8b7db96ffcefd62a9bee5c009f255a2ccfee5",
      "f5dda2d83fce4b0a577b5bf016954c8f194d2cec61b9dd47231abcbec28b77f183127208c6f687287a1a6bf6477338c2",
      "ae44e3f89368f0f0c07dd4a33ec844ab3179ef49c8c63e1426aca9a516b85e77bd4e3866072b10dc1ee056798f38ae1c",
      "f1b5454d6d444ca00f7d9d43eaddda5b1337e49010ca484c0b7d264ee590ed0a0d277fe8267e768e5c54b4b1f3bc9dd6",
      "857849d091545b4742d45572c90680b6077a97075b09129e05c452d19ad8d83832b5c90c81dcc058fad109ecd1bcb6fc",
      "9850538dcb5e7dc205caf79bc136d42418a00293ca17f1bbd289d60c80a08977f311674b1457b4886fecc8b107dd51c9",
      "094e0287a839acdeb4b0c87524907e185f92973ecbfa94f90f50c07e2228de59f43ef56ed2cbf1da6505b810c4b532d1",
      "5ef7650af97d5e3259fa72b457e8e7ac8cb6bc1687eeeb6743526eac6a92b75746cfbab9beb3afa9a2d80dd6a5b80d73",
      "727a8bc5377e64fa3c4562c961747ced26ed3099e3192e9483e9d89e3631f1abe44c02bcb601225fdd30448a19b04364",
      "c18959c0d3e6acfcf6775c345b1cda2ce379825942ffa992c9364d6e5efefd562aec150135d9a24c08ee8577d5a7194a",
      "9f4e43d937d62889fa64a14c43dbcfe0c2dd580c3aa214b9f35644379de6d1b4b5715c2a67d9c6ad4e1fd66e527b6c79",
      "f68cea073b012ee66cc90facd32b9bf2d654bb8882de316312b893894ef7d5e737a89196ec5cdda1d282058f7f792cf7",
      "ed6f53bfa3f0d29c5dcc11a03f15f95045bae9a2ad8fae5604492b3a7137a7b49d32ac95dbb36654dcffc11b350522b3",
      "2f96a31f2ee8f57222dc1928a51b60de60b5d1cb36d6551129cb6cc853e950c490ea8183128e16af7b2e00ec40a00bfd",
      "84dcb09dcebd3a74374470632907002adbb2736d513f303a901a50b03cf0c6b2349e6cffe60f7626e6a124182a37acad",
      "7fea8cb7e482e5be5ad2a6a8c7df962ab4"
    ]) := by
  change sentWire1 = hexBytes sentWire1HexStr
  rw [hexBytes_eq_hexBytesChars, sentWire1HexStr_eq, String.toList_ofList, sentWire1_eq_go]

/-- Carrier Call 1 (`send "attack-at-dawn"`) wire output under `(compI0, compHooks0)` (1793 bytes;
definitionally `rfl`-equal to `ImplTrace.c1Out` and `FastInputs.akFastOut1`). Matches `sentWire1`
everywhere except the off-table 16-byte AES-256-CBC ciphertext (`[117:133]`) and 8-byte MAC
(`[206:214]`), preserving `0x03` framing and the leaked 32-byte `mac_key` in field 6 (`[168:206]`). -/
def carrierSentWire1 : HwBytes := fast_hex_chunks [
  "0344122105abbb904f2c8f86f71332b8059313b1a1cbad7b332d85927b485e5b0e1049c34d1a21055af779b498d58431",
  "51f439cb89efff3ebd63f34cb8fd9ed756699f652d43013c228b01440a21055bfc85a3b08f59137240d42fa1308096a3",
  "7310c86b3ae2bc820d6f0a37bfd33f10001800221047b71b12ea71275e02c3bfaa4214c8b52a250101010100a518128c",
  "bc63e038164b1444fc00f02030c1ecf98b5280e74c1797e90fdd8c0b32201403bc82778fd9489def4369b2b2a42e1eba",
  "b71399687b024763c897eb8606fad7d7d7d7a24b60e928d7083007380942a10c08e4c87208b89cf86e9f0584d1063a8e",
  "590e86e6dc92a2963fcfc5190bea64ad77c1b00446f39ab4e84f40370361ac1f2c79d913584db9f25bdd9d6a527453a8",
  "e849328757bd6a38eae1365a997fcbaf08af459f9ec572fea1a21a3a2994a9414f5337d0f8278bfd2b9adb5eacf6b704",
  "92bf4c1bb83ccbeb33ee2436f0a74863b64acb078bb3a1a0109e41b60c136c71ce64aa93efddf6db1cac587bed4441f6",
  "a34b33c5180a24e4b669689e82539428d9ecbe73ee8e45fb077088c1d837b16f814ddd8532161c29cb90732e1d16def7",
  "07c1224c41040f01a526f1a1944eb85b52fddcd7801b1ba4c88e1339c0c16112f42ffb2d7d05a10152b2747346ad389e",
  "f89da26911506d53debd9091a355766fe3827a5826af45fa9566d1c7887ebdfe4050ebb12e4d9b4209396e6604d3c057",
  "9a921e5deb94110f89b72e855785548b946fd3ddc1d83041db4ba25fa7bd324a9aaeb360f2836a78bba284018452a076",
  "ea80d33f29005c44b69f95a1645c79bf64277e3dfcae4562cbd62c154cf4223fc19d82a598cee37c7bd0aa01701dde3f",
  "c8aeadf46ef74d72ff16bc4c6aa3ae4b0d8ee943ddc26b48c72be45f4d7b04fe03bc17f6ea2c4f137fbf619ce00c54db",
  "2edf2c284ebbfa77c49212b906c34a6cf6a0c4f3dea419eb01649a144b299a1514cbcea84c374ca0e8e5d96c6bb347f2",
  "add5c89ac76c57cd3831662c1e69eb464e6c41d9113dfc028fb470bc0b49da019a39a7892990a4c580ac0bb3c7a9a896",
  "fd802534e5c3e2a14ddca97a064024857dbeca8fe008632e7bfc5009fd92338392f2441776f9fa15b7e304b97932c15e",
  "7b1126f7038c99297ca0dd70ddc5e409d7730cd3d63fec5668a899e2077c7095629105bc578421343adefdf8aad3cc5a",
  "1294bfd81ee51a19d4c1926272d5a0d8b365125d7482cf841856350808cee631c3e02b3bbdc360dab688eda5b1a2de3f",
  "9dc0602aeffba073db5abcf27f6ba41f1babc42ff3257be7fcd95d58b2d1d74ba497f766136c552df6bc17d30861ed79",
  "b13b99d23d4cb41f4b180b5f6cd3ced4c31a84290e6b458aa37b5f0343db1352e37188b6febd98acfd34031685be79f0",
  "219d13a038daf0a25fd5ba66b836ac4716b0c157e790dcb7a3725a52bb32158c8ba506c0c41e31117ce216ff8bb88267",
  "89cb593bb035bf339d3a4a6e2f4369ed959f3358e94c8e05f916d9fae8a8b7db96ffcefd62a9bee5c009f255a2ccfee5",
  "f5dda2d83fce4b0a577b5bf016954c8f194d2cec61b9dd47231abcbec28b77f183127208c6f687287a1a6bf6477338c2",
  "ae44e3f89368f0f0c07dd4a33ec844ab3179ef49c8c63e1426aca9a516b85e77bd4e3866072b10dc1ee056798f38ae1c",
  "f1b5454d6d444ca00f7d9d43eaddda5b1337e49010ca484c0b7d264ee590ed0a0d277fe8267e768e5c54b4b1f3bc9dd6",
  "857849d091545b4742d45572c90680b6077a97075b09129e05c452d19ad8d83832b5c90c81dcc058fad109ecd1bcb6fc",
  "9850538dcb5e7dc205caf79bc136d42418a00293ca17f1bbd289d60c80a08977f311674b1457b4886fecc8b107dd51c9",
  "094e0287a839acdeb4b0c87524907e185f92973ecbfa94f90f50c07e2228de59f43ef56ed2cbf1da6505b810c4b532d1",
  "5ef7650af97d5e3259fa72b457e8e7ac8cb6bc1687eeeb6743526eac6a92b75746cfbab9beb3afa9a2d80dd6a5b80d73",
  "727a8bc5377e64fa3c4562c961747ced26ed3099e3192e9483e9d89e3631f1abe44c02bcb601225fdd30448a19b04364",
  "c18959c0d3e6acfcf6775c345b1cda2ce379825942ffa992c9364d6e5efefd562aec150135d9a24c08ee8577d5a7194a",
  "9f4e43d937d62889fa64a14c43dbcfe0c2dd580c3aa214b9f35644379de6d1b4b5715c2a67d9c6ad4e1fd66e527b6c79",
  "f68cea073b012ee66cc90facd32b9bf2d654bb8882de316312b893894ef7d5e737a89196ec5cdda1d282058f7f792cf7",
  "ed6f53bfa3f0d29c5dcc11a03f15f95045bae9a2ad8fae5604492b3a7137a7b49d32ac95dbb36654dcffc11b350522b3",
  "2f96a31f2ee8f57222dc1928a51b60de60b5d1cb36d6551129cb6cc853e950c490ea8183128e16af7b2e00ec40a00bfd",
  "84dcb09dcebd3a74374470632907002adbb2736d513f303a901a50b03cf0c6b2349e6cffe60f7626e6a124182a37acad",
  "7fea8cb7e482e5be5ad2a6a8c7df962ab4"
]

/-- Alias matching `ImplTrace.c1Out`. -/
abbrev c1Out : HwBytes := carrierSentWire1

end FastAkHex

/-- Carrier 2-call CLI trace produced by the mutant binary under `(compI0, compHooks0)`:
definitionally `rfl`-equal to `ImplTrace.akCarrierTrace`. -/
def akCarrierTrace : List CliEvent :=
  [ .run { (rawRunAt 0) with exit := some (0, []) },
    .run { (rawRunAt 1) with exit := some (0, carrierSentWire1) } ]

theorem coins1_eq_cB : coins1 = CompRX0SS38.cB := by
  rw [CompRX0SS38.cB_eq_hex, coins1_eq_hex]

theorem pt1_length : pt1.length = 14 := by decide +kernel

theorem coins1_length : coins1.length = 64 := by decide +kernel

theorem sentWire1_length : sentWire1.length = 1793 := by decide +kernel

theorem carrierSentWire1_length : carrierSentWire1.length = 1793 := by decide +kernel

theorem sentWire1_head? : sentWire1.head? = some 0x03#8 := by decide +kernel

theorem carrierSentWire1_head? : carrierSentWire1.head? = some 0x03#8 := by decide +kernel

theorem sentWire1_head_ne_whisper :
    sentWire1.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by
  rw [sentWire1_head?]; decide

theorem carrierSentWire1_head_ne_whisper :
    carrierSentWire1.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag := by
  rw [carrierSentWire1_head?]; decide

theorem sentWire1_parsePreKeyWire_isSome :
    (parsePreKeyWire sentWire1).isSome = true := by
  decide +kernel

theorem carrierSentWire1_parsePreKeyWire_isSome :
    (parsePreKeyWire carrierSentWire1).isSome = true := by
  decide +kernel

/-! ## 3. Structured Events `evInit`, `evSendOf`, `akEvents` & Trace Equalities -/

/-- Call 0 (`init` Alice from Bob's honest bundle). -/
def evInit : RunEvent :=
  { party := "alice"
    cmd := .init ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩ "bundle"
    input := bunBytes
    coins := coins0
    exit := some (0, []) }

/-- Call 1 (`send` Alice `"attack-at-dawn"`) parameterized by `exit`. -/
def evSendWithExit (exit1 : Option (Nat × HwBytes)) : RunEvent :=
  { party := "alice"
    cmd := .send ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩
    input := pt1
    coins := coins1
    exit := exit1 }

/-- Call 1 (`send` Alice `"attack-at-dawn"`) parameterized by exit-`0` stdout `out1`. -/
def evSendOf (out1 : HwBytes) : RunEvent :=
  evSendWithExit (some (0, out1))

/-- Recorded Call 1 (`send` Alice `"attack-at-dawn"`, stdout `sentWire1`). -/
abbrev evSend : RunEvent :=
  evSendOf sentWire1

/-- Carrier Call 1 (`send` Alice `"attack-at-dawn"`, stdout `carrierSentWire1`). -/
abbrev evSendCarrier : RunEvent :=
  evSendOf carrierSentWire1

/-- Parameterized 2-call CLI event list `[.run evInit, .run (evSendOf out1)]`. -/
def akEvents (out1 : HwBytes) : List CliEvent :=
  [.run evInit, .run (evSendOf out1)]

/-- Recorded 2-call CLI event list `[.run evInit, .run evSend]`. -/
abbrev cliEvents : List CliEvent :=
  akEvents sentWire1

/-- Carrier 2-call CLI event list `[.run evInit, .run evSendCarrier]`. -/
abbrev cliEventsCarrier : List CliEvent :=
  akEvents carrierSentWire1

theorem evInit_eq_hb :
    evInit = Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge.evInit := rfl

/-- `akEvents sentWire1` (`cliEvents`) equals the recorded witness trace `AddrKeyLeakCli.trace`. -/
theorem akEvents_eq : akEvents sentWire1 = akTrace := by
  unfold akEvents evInit evSendOf evSendWithExit bunBytes coins0 cliCoins0 akTrace
    Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli.trace
  rw [CompRX0SS38.bunBytes_eq_hex, pt1_eq_hex, coins1_eq_hex, sentWire1_eq_hex, nil_eq_hexBytes]

/-- `cliEvents` equals the recorded witness trace `AddrKeyLeakCli.trace` (`akTrace`). -/
theorem cliEvents_eq : cliEvents = akTrace := akEvents_eq

/-- `akEvents carrierSentWire1` (`cliEventsCarrier`) equals the `(compI0, compHooks0)` carrier trace
`akCarrierTrace`. -/
theorem akEvents_carrier_eq : akEvents carrierSentWire1 = akCarrierTrace := by
  unfold akEvents evInit evSendOf evSendWithExit bunBytes coins0 cliCoins0
    akCarrierTrace rawRunAt akTrace
    Symbolic.BugInjection.Synthetic.Witnesses.AddrKeyLeakCli.trace
  dsimp only [List.getElem?_cons_zero, List.getElem?_cons_succ]
  rw [CompRX0SS38.bunBytes_eq_hex, pt1_eq_hex, coins1_eq_hex]

theorem cliEventsCarrier_eq : cliEventsCarrier = akCarrierTrace := akEvents_carrier_eq

theorem flatEvents_evInit :
    flatEvents [.run evInit] = [.recv bunBytes, .rng coins0] := rfl

theorem flatEvents_akEvents (out1 : HwBytes) :
    flatEvents (akEvents out1) =
      [.recv bunBytes, .rng coins0, .pt pt1, .rng coins1, .send out1] := rfl

theorem flatEvents_cliEvents :
    flatEvents cliEvents =
      [.recv bunBytes, .rng coins0, .pt pt1, .rng coins1, .send sentWire1] :=
  flatEvents_akEvents sentWire1

theorem flatEvents_cliEventsCarrier :
    flatEvents cliEventsCarrier =
      [.recv bunBytes, .rng coins0, .pt pt1, .rng coins1, .send carrierSentWire1] :=
  flatEvents_akEvents carrierSentWire1

/-- Case split for `[a, b] = xs ++ x :: ys` (2-element list decomposition). -/
theorem list_eq_two_splits {α : Type} {a b x : α} {xs ys : List α}
    (h : [a, b] = xs ++ x :: ys) :
    (xs = [] ∧ x = a ∧ ys = [b]) ∨
    (xs = [a] ∧ x = b ∧ ys = []) := by
  rcases xs with _ | ⟨x₀, _ | ⟨x₁, xs⟩⟩
  · simp at h; obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
  · simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inr ⟨rfl, rfl, rfl⟩
  · simp at h

/-! ## 4. `BreakFree`, `SchedFits`, and `runWrapped` -/

theorem breakFree_evInit : BreakFree [.run evInit] :=
  breakFree_cons_run _ breakFree_nil

theorem breakFree_akEvents (out1 : HwBytes) : BreakFree (akEvents out1) :=
  breakFree_cons_run _ (breakFree_cons_run _ breakFree_nil)

theorem breakFree_cliEvents : BreakFree cliEvents :=
  breakFree_akEvents sentWire1

theorem breakFree_cliEventsCarrier : BreakFree cliEventsCarrier :=
  breakFree_akEvents carrierSentWire1

theorem breakFree_akTrace : BreakFree akTrace :=
  akEvents_eq ▸ breakFree_cliEvents

theorem breakFree_akCarrierTrace : BreakFree akCarrierTrace :=
  breakFree_cons_run _ (breakFree_cons_run _ breakFree_nil)

theorem callsOf_evInit :
    callsOf [.run evInit] = [("alice", true)] := rfl

theorem callsOf_akEvents (out1 : HwBytes) :
    callsOf (akEvents out1) = [("alice", true), ("alice", true)] := rfl

theorem callsOf_cliEvents :
    callsOf cliEvents = [("alice", true), ("alice", true)] :=
  callsOf_akEvents sentWire1

set_option linter.unnecessarySeqFocus false in
theorem schedFits_evInit : SchedFits (callsOf [.run evInit]) akWho akOk := by
  rw [callsOf_evInit]
  refine ⟨⟨["alice", "bob"], rfl⟩, fun k p b hget => ?_⟩
  rcases k with _ | k <;> simp at hget <;> obtain ⟨rfl, rfl⟩ := hget <;> rfl

set_option linter.unnecessarySeqFocus false in
theorem schedFits_akEvents (out1 : HwBytes) : SchedFits (callsOf (akEvents out1)) akWho akOk := by
  rw [callsOf_akEvents]
  refine ⟨⟨["bob"], rfl⟩, fun k p b hget => ?_⟩
  rcases k with _ | _ | k <;> simp at hget <;> obtain ⟨rfl, rfl⟩ := hget <;> rfl

theorem schedFits_cliEvents : SchedFits (callsOf cliEvents) akWho akOk :=
  schedFits_akEvents sentWire1

/-- Any Call 1 `send` output starting with `0x03` (`wirePrekeyTag`) has `runWrapped = true`. -/
theorem runWrapped_evSendOf {out1 : HwBytes} (h : out1.head? = some 0x03#8) :
    runWrapped (evSendOf out1) = true := by
  unfold runWrapped evSendOf evSendWithExit
  dsimp only
  rw [h]
  decide

/-- Recorded Call 1 output starts with `0x03`, so `runWrapped evSend = true`. -/
theorem runWrapped_evSend : runWrapped evSend = true :=
  runWrapped_evSendOf sentWire1_head?

/-- Carrier Call 1 output starts with `0x03`, so `runWrapped evSendCarrier = true`. -/
theorem runWrapped_evSendCarrier : runWrapped evSendCarrier = true :=
  runWrapped_evSendOf carrierSentWire1_head?

/-! ## 5. Call 0 `initiateDrawsOfCoins` & `init_exit0_cut_eq` Bridges -/

theorem initiateDrawsOfCoins_coins0_eq :
    (CliCoinSplit.initiateDrawsOfCoins coins0).map MachineEvent.rng =
      .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT :=
  initiateDrawsOfCoins_cliCoins0_eq

theorem init_draws_coins0_eq_hb :
    .recv bunBytes :: (CliCoinSplit.initiateDrawsOfCoins coins0).map MachineEvent.rng =
      Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 35 :=
  init_draws_cliCoins0_eq_hb

theorem init_draws_coins0_eq_call0 :
    .recv bunBytes :: (CliCoinSplit.initiateDrawsOfCoins coins0).map MachineEvent.rng =
      .recv bundleBytes :: call0RngEvents := by
  rw [init_draws_coins0_eq_hb, trace_take_35_eq]

/-- Call 0 `init` coin-split cut uniqueness specialized to `[.run evInit]`. -/
theorem ak_init_exit0_cut_eq {interp : ExternInterpretation} {r : Records} {S : Sem}
    {τ : List MachineEvent} {g : Ghost} {ms : List Move}
    (hexp : ExplainsCli interp r S akWho akOk (flatEvents [.run evInit]) τ g ms) :
    τ = .recv bunBytes :: (CliCoinSplit.initiateDrawsOfCoins coins0).map MachineEvent.rng ∧
    ExplainsMoves interp r S akWho akOk g ms τ :=
  CliCoinSplit.init_exit0_cut_eq rfl coins0_length hexp

/-- Call 0 `init` cut rewritten directly to `.recv bundleBytes :: call0RngEvents` so
`Cheval26SmallSubgroupHighBitComp443.iniPrefixStateSecretsInv_call0` applies immediately. -/
theorem ak_init_exit0_explains_call0 {interp : ExternInterpretation} {r : Records} {S : Sem}
    {τ : List MachineEvent} {g : Ghost} {ms : List Move}
    (hexp : ExplainsCli interp r S akWho akOk (flatEvents [.run evInit]) τ g ms) :
    τ = .recv bundleBytes :: call0RngEvents ∧
    ExplainsMoves interp r S akWho akOk g ms (.recv bundleBytes :: call0RngEvents) := by
  obtain ⟨hτ, hex_moves⟩ := ak_init_exit0_cut_eq hexp
  rw [init_draws_coins0_eq_call0] at hτ
  exact ⟨hτ, hτ ▸ hex_moves⟩

/-- Parameterized 2-call (`init` + `send`) `ExplainsCli` decomposition specialized to `akEvents out1`. -/
theorem ak_explainsCli_init_send_decomp_of {interp : ExternInterpretation} {r : Records} {S : Sem}
    (out1 : HwBytes) {τ : List MachineEvent} {g : Ghost} {ms : List Move}
    (hexp : ExplainsCli interp r S akWho akOk (flatEvents (akEvents out1)) τ g ms) :
    ∃ blk₁,
      τ = (.recv bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁ ∧
      CoinSplit [.pt pt1, .rng coins1, .send out1] blk₁ ∧
      ExplainsMoves interp r S akWho akOk g ms τ := by
  obtain ⟨blk₁, hτ, hcs₁, hex_moves⟩ :=
    CliCoinSplit.explainsCli_init_send_decomp rfl coins0_length hexp
  rw [initiateDrawsOfCoins_coins0_eq] at hτ
  exact ⟨blk₁, hτ, hcs₁, hex_moves⟩

/-- Recorded 2-call (`init` + `send`) `ExplainsCli` decomposition specialized to `cliEvents`. -/
theorem ak_explainsCli_init_send_decomp {interp : ExternInterpretation} {r : Records} {S : Sem}
    {τ : List MachineEvent} {g : Ghost} {ms : List Move}
    (hexp : ExplainsCli interp r S akWho akOk (flatEvents cliEvents) τ g ms) :
    ∃ blk₁,
      τ = (.recv bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁ ∧
      CoinSplit [.pt pt1, .rng coins1, .send sentWire1] blk₁ ∧
      ExplainsMoves interp r S akWho akOk g ms τ :=
  ak_explainsCli_init_send_decomp_of sentWire1 hexp

/-- Length bound `14 < 32` on Call 0's first RNG draw (`rngEkBytes`), ready for
`memoInjGt_prefixTerms_of_matchedPrefix_ini_of` on 14-byte `pt1`. -/
theorem call0RngEvents_take_1_gt_14 :
    ∀ e ∈ call0RngEvents.take 1, 14 < (Common443.Census443Defs.eventBytes e).length := by
  intro e he
  rw [call0RngEvents_take_1_eq, List.mem_singleton] at he
  subst he
  show 14 < rngEkBytes.length
  rw [rngEkBytes_length]
  decide

/-- Length bound `14 < 32` on Call 0's last RNG draw (`rngDhsBytes`), ready for
`memoInjGt_prefixTerms_of_matchedPrefix_ini_of` on 14-byte `pt1`. -/
theorem call0RngEvents_drop_33_gt_14 :
    ∀ e ∈ call0RngEvents.drop 33, 14 < (Common443.Census443Defs.eventBytes e).length := by
  intro e he
  rw [call0RngEvents_drop_33_eq, List.mem_singleton] at he
  subst he
  show 14 < rngDhsBytes.length
  rw [rngDhsBytes_length]
  decide

end Symbolic.BugInjection.Proofs.SyntheticAddrKeyLeak.Defs
