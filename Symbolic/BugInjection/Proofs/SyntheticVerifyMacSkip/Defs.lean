/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import Lean
public import Symbolic.Specifications.Refinement.WireFormat
public import Symbolic.BugInjection.Synthetic.Witnesses.VerifyMacSkipCli
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge
public import Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.NoFullMatch
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.BobDone
public import Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj
public import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
public import Symbolic.Proofs.Swarm.CREF.TR.G1.OwnKeyBranch
public import Symbolic.Proofs.Swarm.CREF.TR.G1.G1RepPtAtomsTR

/-!
# Definitions & Wire/MAC Lemmas for `SyntheticVerifyMacSkip`

Defines the carrier Call-2 pre-key wire `msg38_vms` (`CompRPlantWire.sentWireBytes` with its
trailing 8-byte inner `SignalMessage` MAC tag replaced by `ones8 := List.replicate 8 0xff#8`),
the 3-call carrier CLI trace `cliEventsVMS := CliBridge.cliEvents msg38_vms`, setup-fit bridges
to `Cheval26SmallSubgroupHighBitComp`, inner-MAC non-match lemmas against `compI0`
(`gamma_computeMac_ne_ones8`, `not_trialMacMatches_of_mac_ones8`,
`not_macTagForgeryOrCollision_of_mac_ones8`), and canonical wire properties (`msg38_vms_props`,
`msg38_vms_innerWireCanonical`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.Defs

open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent CliEvent RunEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement DY.Libsignal.Composed.Refinement.Cli
open DY.Libsignal.PQXDH.Refinement (PreKeyFields)
open Symbolic.Proofs.Swarm.UA.Defs
open Symbolic.BugInjection
open Symbolic.BugInjection.Synthetic
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0
open Symbolic.BugInjection.Proofs.Common443
open Symbolic.BugInjection.Proofs.Cheval26SmallSubgroupHighBitComp443.CliBridge
  (evInit evSend evRecv cliEvents rngMsg39 acceptMsg40 rngMsg39_eq_hex acceptMsg40_eq_hex
   nil_eq_hexBytes)
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
  (AllBobDone bobDoneBaseKeys_of_allBobDone mem_bobDoneBaseKeys_of_mem_sessionBaseKeys)

def ones8 : HwBytes := List.replicate 8 0xff#8

theorem ones8_len : ones8.length = 8 := by decide

section HexElab
open Lean (Expr mkApp mkApp2 mkApp3 mkConst mkNatLit)

private meta def hexNib (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else 0

private meta def mkBVExpr (w val : Nat) : Expr :=
  mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit w) (mkNatLit val)

private meta def mkByteListFromHex (s : String) : Expr := Id.run do
  let bv8 := mkApp (mkConst ``BitVec) (mkNatLit 8)
  let mut acc := mkApp (mkConst ``List.nil [0]) bv8
  let arr := s.toByteArray
  let n := arr.size / 2
  for idx in [0:n] do
    let revIdx := n - 1 - idx
    let hi := hexNib (Char.ofNat (arr.get! (2 * revIdx)).toNat)
    let lo := hexNib (Char.ofNat (arr.get! (2 * revIdx + 1)).toNat)
    let v := 16 * hi + lo
    acc := mkApp3 (mkConst ``List.cons [0]) bv8 (mkBVExpr 8 v) acc
  return acc

end HexElab

local elab "fast_hex_chunks " "[" chunks:str,* "]" : term => do
  let strs := chunks.getElems.map (·.getString)
  return mkByteListFromHex (String.join strs.toList)

/-- Pre-elaborated WHNF byte list for Call 2's pre-key message (`CompRPlantWire.sentWireBytes`
with bytes `210..218`, the 8-byte inner `SignalMessage` MAC `e92926fbc7cfaa39`, replaced by
`ffffffffffffffff`). -/
def msg38VmsFast : HwBytes := fast_hex_chunks [
  "0344122105abbb904f2c8f86f71332b8059313b1a1cbad7b332d85927b485e5b0e1049c34d1a21055af779b498d5843151f439cb89efff3ebd63f34cb8fd9ed756699f652d43013c228f01440a21055bfc85a3b08f59137240d4",
  "2fa1308096a37310c86b3ae2bc820d6f0a37bfd33f100018002210fca4e87c39d39d1f29f41085ec2a6c7c2a250101010100a518128cbc63e038164b1444fc00f02030c1ecf98b5280e74c1797e90fdd8c0b3224008a6f1c2e3b",
  "4d4e5f9a0b1c2d3e4f5a6b01005d3e2f107a8b4c9d8e0fa1b2c3d4e5f601ffffffffffffffff28d7083007380942a10c08e4c87208b89cf86e9f0584d1063a8e590e86e6dc92a2963fcfc5190bea64ad77c1b00446f39ab4e84f",
  "40370361ac1f2c79d913584db9f25bdd9d6a527453a8e849328757bd6a38eae1365a997fcbaf08af459f9ec572fea1a21a3a2994a9414f5337d0f8278bfd2b9adb5eacf6b70492bf4c1bb83ccbeb33ee2436f0a74863b64acb07",
  "8bb3a1a0109e41b60c136c71ce64aa93efddf6db1cac587bed4441f6a34b33c5180a24e4b669689e82539428d9ecbe73ee8e45fb077088c1d837b16f814ddd8532161c29cb90732e1d16def707c1224c41040f01a526f1a1944e",
  "b85b52fddcd7801b1ba4c88e1339c0c16112f42ffb2d7d05a10152b2747346ad389ef89da26911506d53debd9091a355766fe3827a5826af45fa9566d1c7887ebdfe4050ebb12e4d9b4209396e6604d3c0579a921e5deb94110f",
  "89b72e855785548b946fd3ddc1d83041db4ba25fa7bd324a9aaeb360f2836a78bba284018452a076ea80d33f29005c44b69f95a1645c79bf64277e3dfcae4562cbd62c154cf4223fc19d82a598cee37c7bd0aa01701dde3fc8ae",
  "adf46ef74d72ff16bc4c6aa3ae4b0d8ee943ddc26b48c72be45f4d7b04fe03bc17f6ea2c4f137fbf619ce00c54db2edf2c284ebbfa77c49212b906c34a6cf6a0c4f3dea419eb01649a144b299a1514cbcea84c374ca0e8e5d96c",
  "6bb347f2add5c89ac76c57cd3831662c1e69eb464e6c41d9113dfc028fb470bc0b49da019a39a7892990a4c580ac0bb3c7a9a896fd802534e5c3e2a14ddca97a064024857dbeca8fe008632e7bfc5009fd92338392f2441776f9",
  "fa15b7e304b97932c15e7b1126f7038c99297ca0dd70ddc5e409d7730cd3d63fec5668a899e2077c7095629105bc578421343adefdf8aad3cc5a1294bfd81ee51a19d4c1926272d5a0d8b365125d7482cf841856350808cee631",
  "c3e02b3bbdc360dab688eda5b1a2de3f9dc0602aeffba073db5abcf27f6ba41f1babc42ff3257be7fcd95d58b2d1d74ba497f766136c552df6bc17d30861ed79b13b99d23d4cb41f4b180b5f6cd3ced4c31a84290e6b458aa37b",
  "5f0343db1352e37188b6febd98acfd34031685be79f0219d13a038daf0a25fd5ba66b836ac4716b0c157e790dcb7a3725a52bb32158c8ba506c0c41e31117ce216ff8bb8826789cb593bb035bf339d3a4a6e2f4369ed959f3358",
  "e94c8e05f916d9fae8a8b7db96ffcefd62a9bee5c009f255a2ccfee5f5dda2d83fce4b0a577b5bf016954c8f194d2cec61b9dd47231abcbec28b77f183127208c6f687287a1a6bf6477338c2ae44e3f89368f0f0c07dd4a33ec8",
  "44ab3179ef49c8c63e1426aca9a516b85e77bd4e3866072b10dc1ee056798f38ae1cf1b5454d6d444ca00f7d9d43eaddda5b1337e49010ca484c0b7d264ee590ed0a0d277fe8267e768e5c54b4b1f3bc9dd6857849d091545b47",
  "42d45572c90680b6077a97075b09129e05c452d19ad8d83832b5c90c81dcc058fad109ecd1bcb6fc9850538dcb5e7dc205caf79bc136d42418a00293ca17f1bbd289d60c80a08977f311674b1457b4886fecc8b107dd51c9094e",
  "0287a839acdeb4b0c87524907e185f92973ecbfa94f90f50c07e2228de59f43ef56ed2cbf1da6505b810c4b532d15ef7650af97d5e3259fa72b457e8e7ac8cb6bc1687eeeb6743526eac6a92b75746cfbab9beb3afa9a2d80dd6",
  "a5b80d73727a8bc5377e64fa3c4562c961747ced26ed3099e3192e9483e9d89e3631f1abe44c02bcb601225fdd30448a19b04364c18959c0d3e6acfcf6775c345b1cda2ce379825942ffa992c9364d6e5efefd562aec150135d9",
  "a24c08ee8577d5a7194a9f4e43d937d62889fa64a14c43dbcfe0c2dd580c3aa214b9f35644379de6d1b4b5715c2a67d9c6ad4e1fd66e527b6c79f68cea073b012ee66cc90facd32b9bf2d654bb8882de316312b893894ef7d5e7",
  "37a89196ec5cdda1d282058f7f792cf7ed6f53bfa3f0d29c5dcc11a03f15f95045bae9a2ad8fae5604492b3a7137a7b49d32ac95dbb36654dcffc11b350522b32f96a31f2ee8f57222dc1928a51b60de60b5d1cb36d6551129cb",
  "6cc853e950c490ea8183128e16af7b2e00ec40a00bfd84dcb09dcebd3a74374470632907002adbb2736d513f303a901a50b03cf0c6b2349e6cffe60f7626e6a124182a37acad7fea8cb7e482e5be5ad2a6a8c7df962ab4"
]

def msg38_vms : HwBytes := msg38VmsFast

theorem msg38_vms_eq_fast : msg38_vms = msg38VmsFast := rfl

theorem msg38_vms_eq_sentWire_replace_mac :
    msg38_vms =
      CompRPlantWire.sentWireFast.take 210 ++ ones8 ++ CompRPlantWire.sentWireFast.drop 218 := by
  decide +kernel

private theorem msg38VmsFast_len : msg38VmsFast.length < 2 ^ 63 := by decide +kernel

theorem msg38_vms_len : msg38_vms.length < 2 ^ 63 := msg38VmsFast_len

attribute [local irreducible] Symbolic.BugInjection.hexBytes

theorem acceptMsg40_eq_ptB : acceptMsg40 = CompRX0SS38.ptB := by
  rw [acceptMsg40_eq_hex, CompRX0SS38.ptB_eq_hex]

def evRecvVMS : RunEvent := evRecv msg38_vms

theorem evRecvVMS_eq :
    evRecvVMS =
      { party := "bob"
        cmd := .recv ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩
        input := msg38_vms
        coins := rngMsg39
        exit := some (0, CompRX0SS38.ptB) } := by
  unfold evRecvVMS evRecv
  rw [acceptMsg40_eq_ptB]

def cliEventsVMS : List CliEvent := cliEvents msg38_vms

theorem cliEventsVMS_eq : cliEventsVMS = cliEvents msg38_vms := rfl

theorem cliEventsVMS_runs : cliEventsVMS = [.run evInit, .run evSend, .run evRecvVMS] := rfl

theorem setup_eq_hb_cli :
    Witnesses.VerifyMacSkipCli.setup =
      Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.setup := rfl

theorem compFits_hb_of_vms {i : ExternInterpretation} {r : Records}
    (h : SetupMatches Witnesses.VerifyMacSkipCli.setup i r) :
    SetupMatches Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.setup i r := by
  simpa [SetupMatches, Witnesses.VerifyMacSkipCli.setup,
    Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.setup,
    Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitCli.setup] using h

theorem compFitsPinned_hb_of_vms {i : ExternInterpretation} {r : Records}
    (h : compFitsPinned Witnesses.VerifyMacSkipCli.setup i r) :
    compFitsPinned Symbolic.BugInjection.Witnesses.Cheval26SmallSubgroupHighBitComp.setup i r :=
  ⟨compFits_hb_of_vms h.1, h.2⟩

theorem rowDigests_take8_ne_ones8 :
    ∀ d ∈ CompRI0TermInj.rowDigests, d.take 8 ≠ ones8 := by
  decide +kernel

theorem compTag4_ne_ones4 : compTag4 ≠ [0xff#8, 0xff#8, 0xff#8, 0xff#8] := by decide

theorem gamma_computeMac_length (S : Sem) (g : Ghost) (mk peerIk myIk wire : DY.Bytes) :
    (gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk peerIk myIk wire)).length = 8 := by
  unfold DY.Libsignal.TripleRatchet.computeMac
  rw [CompFreshDistinct.gamma_trunc8_eq, List.length_take, CompFreshDistinct.gamma_hmac_length]
  decide

theorem gamma_computeMac_ne_ones8 (S : Sem) (g : Ghost) (mk peerIk myIk wire : DY.Bytes) :
    gamma compI0 S g (DY.Libsignal.TripleRatchet.computeMac mk peerIk myIk wire) ≠ ones8 := by
  unfold DY.Libsignal.TripleRatchet.computeMac
  rw [CompFreshDistinct.gamma_trunc8_eq]
  intro heq
  rcases CompRI0TermInj.gamma_kdfExtract_tag_or_row (S := S) (g := g)
      mk (DY.Concat.concat peerIk (DY.Concat.concat myIk wire)) with htag | hrow
  · have h4 : ((gamma compI0 S g
        (DY.Libsignal.TripleRatchet.hmac mk
          (DY.Concat.concat peerIk (DY.Concat.concat myIk wire)))).take 8).take 4 =
        ones8.take 4 := congrArg (List.take 4) heq
    rw [List.take_take, show min 4 8 = 4 by decide] at h4
    exact compTag4_ne_ones4 (htag.symm.trans h4)
  · exact rowDigests_take8_ne_ones8 _ hrow heq

theorem not_macTagForgeryOrCollision_of_mac_ones8 {S : Sem} {g : Ghost}
    {known : DY.Bytes → Prop} {salts : List DY.Bytes}
    {msg : DY.Libsignal.TripleRatchet.TRSignalMsg} {ctxs : List TrialCtx}
    (hmac : gamma compI0 S g msg.mac = ones8) :
    ¬ MacTagForgeryOrCollision compI0 S g known salts msg ctxs := by
  rintro (⟨_, _, _, _, _, _, heq, _⟩ | ⟨_, _, _, _, _, _, heq, _⟩) <;>
    (rw [hmac] at heq; exact gamma_computeMac_ne_ones8 S g _ _ _ _ heq)

theorem drop_sub_eight_append {a b : HwBytes} (hb : b.length = 8) :
    (a ++ b).drop ((a ++ b).length - 8) = b := by
  rw [List.length_append, hb, Nat.add_sub_cancel, List.drop_left' rfl]

theorem parseTrSignalMsg_gamma_drop8 {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {raw : DY.Bytes} {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    (hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw = some msg)
    (hlen : (gamma i S g msg.mac).length = 8) :
    (gamma i S g raw).drop ((gamma i S g raw).length - 8) = gamma i S g msg.mac := by
  obtain ⟨_, hsp, _⟩ := Symbolic.Swarm.CREF.TR.G1.parseTrSignalMsg_unpack_c hparse
  have hraw : raw = DY.Concat.concat msg.wire msg.mac :=
    (Symbolic.Swarm.CREF.TR.G1.split_eq_some_concat_and_length_tr32 hsp).1
  rw [hraw, CompFreshDistinct.gamma_concat_eq]
  exact drop_sub_eight_append hlen

private theorem msg38VmsFast_props :
    msg38VmsFast.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag ∧
    (parsePreKeyWire msg38VmsFast).isSome = true ∧
    (parsePreKeyWire msg38VmsFast).map (fun p => p.message.drop (p.message.length - 8)) =
      some ones8 ∧
    (parsePreKeyWire msg38VmsFast).map PreKeyFields.preKeyId = some none := by
  decide +kernel

theorem msg38_vms_props :
    msg38_vms.head? ≠ some DY.Libsignal.TripleRatchet.Refinement.wireWhisperTag ∧
    (parsePreKeyWire msg38_vms).isSome = true ∧
    (parsePreKeyWire msg38_vms).map (fun p => p.message.drop (p.message.length - 8)) =
      some ones8 ∧
    (parsePreKeyWire msg38_vms).map PreKeyFields.preKeyId = some none := by
  rw [msg38_vms_eq_fast]
  exact msg38VmsFast_props

theorem check_msg38VmsFast : CompRPlantWire.checkInnerWireCanonicalAt 0 msg38VmsFast = true := by
  decide +kernel

theorem msg38_vms_innerWireCanonical :
    (∃ p, parsePreKeyWire msg38_vms = some p ∧ CompRFaithfulInner.InnerWireCanonical p) ∧
      (∀ p, parsePreKeyWire msg38_vms = some p → CompRFaithfulInner.InnerWireCanonical p) := by
  rw [msg38_vms_eq_fast]
  exact CompRPlantWire.innerWireCanonical_of_check check_msg38VmsFast

end Symbolic.BugInjection.Proofs.SyntheticVerifyMacSkip.Defs
