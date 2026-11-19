/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean
public import Init.Data.String
public import Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003
public import Symbolic.BugInjection.Proofs.Common443.CliEventBridge

/-!
# Concrete Trace Events, Fast Byte Constants, and Wire/KDF Evaluations for Seed 7003

Defines the structured CLI events and fast (`leBytes`) byte constants for both round-4 receive-path
synthetic mutant witnesses (`DecryptCloneNotPersistedCli` and `SignalMsgCanonicalMacCli`), proves
exact trace equality with the generated witness modules, and discharges concrete wire-parsing and
HMAC/HKDF evaluation facts via `decide +kernel`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003

open ByteSpecs (hmacWith sha256With)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (CliEvent RunEvent)
open DY.Libsignal.Refinement (WireFields paddedVarint encodeField)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Proofs.Swarm.UA.ClassicalBridge (BreakFree)
open Symbolic.BugInjection.Proofs.Common443.CliEventBridge (breakFree_map_run)
open Symbolic.BugInjection
open Symbolic.BugInjection.Synthetic.Witnesses
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompI7003Laws
open Symbolic.BugInjection.Proofs.SyntheticRecvCommon.CompFits7003

/-! ## 1. Common Setup & Compatibility -/

abbrev setup7003 : PQXDHSpqrSetup := DecryptCloneNotPersistedCli.setup

theorem compFitsPinned7003_m1_of_m2 {r : ProtocolSetup}
    (h : compFitsPinned7003 SignalMsgCanonicalMacCli.setup compI7003 r) :
    compFitsPinned7003 setup7003 compI7003 r := by
  obtain ⟨⟨hwf, hopk, hra, hrb, hspk, hkpk, hs0, hs1, hs2, ho5, ho6, ho7, hsec, hcryp, hcan, _⟩,
    hi, hsec35, hpart, htorRej, _⟩ := h
  exact ⟨⟨hwf, hopk, hra, hrb, hspk, hkpk, hs0, hs1, hs2, ho5, ho6, ho7, hsec, hcryp, hcan,
    compI7003_kyberCorrectOn r _⟩, hi, hsec35, hpart, htorRej, fun _ hm => nomatch hm⟩

/-! ## 2. Fast Hex Conversion Infrastructure -/

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

theorem hexBytes_ofList (cs : List Char) :
    hexBytes (String.ofList cs) = hexBytes.go hexDigit cs := by
  unfold hexBytes hexDigit
  rw [String.toList_ofList]

attribute [local irreducible] Symbolic.BugInjection.hexBytes

local elab "chars_of_hex7003" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  let sLit ← Lean.Meta.whnf eWhnf.getAppArgs[0]!
  match sLit with
  | .lit (.strVal s) => return Lean.toExpr s.toList
  | _ => throwError "not strVal: {sLit}"

local elab "str_of_hex7003" id:ident : term => do
  let e := Lean.mkConst (← Lean.resolveGlobalConstNoOverload id)
  let eWhnf ← Lean.Meta.whnf e
  Lean.Meta.whnf eWhnf.getAppArgs[0]!

/-! ## 3. Raw Witness Event Projections & Trace Equalities -/

def peerAddrBob : CryptoVerification.SignalSession.Address :=
  ⟨"5d3e2f10-7a8b-4c9d-8e0f-a1b2c3d4e5f6", 1⟩

def peerAddrAlice : CryptoVerification.SignalSession.Address :=
  ⟨"8a6f1c2e-3b4d-4e5f-9a0b-1c2d3e4f5a6b", 1⟩

def bun0Raw : HwBytes :=
  match DecryptCloneNotPersistedCli.trace with
  | .run ev :: _ => ev.input
  | _ => []

def coins0Raw : HwBytes :=
  match DecryptCloneNotPersistedCli.trace with
  | .run ev :: _ => ev.coins
  | _ => []

def out0Raw : HwBytes :=
  match DecryptCloneNotPersistedCli.trace with
  | .run ev :: _ => match ev.exit with | some (_, b) => b | none => []
  | _ => []

def pt1M1Raw : HwBytes :=
  match DecryptCloneNotPersistedCli.trace with
  | _ :: .run ev :: _ => ev.input
  | _ => []

def coins1Raw : HwBytes :=
  match DecryptCloneNotPersistedCli.trace with
  | _ :: .run ev :: _ => ev.coins
  | _ => []

def out1M1Raw : HwBytes :=
  match DecryptCloneNotPersistedCli.trace with
  | _ :: .run ev :: _ => match ev.exit with | some (_, b) => b | none => []
  | _ => []

def coins2Raw : HwBytes :=
  match DecryptCloneNotPersistedCli.trace with
  | _ :: _ :: .run ev :: _ => ev.coins
  | _ => []

def coins3M1Raw : HwBytes :=
  match DecryptCloneNotPersistedCli.trace with
  | [_, _, _, .run ev] => ev.coins
  | _ => []

def pt1M2Raw : HwBytes :=
  match SignalMsgCanonicalMacCli.trace with
  | _ :: .run ev :: _ => ev.input
  | _ => []

def out1M2Raw : HwBytes :=
  match SignalMsgCanonicalMacCli.trace with
  | _ :: .run ev :: _ => match ev.exit with | some (_, b) => b | none => []
  | _ => []

def pt3M2Raw : HwBytes :=
  match SignalMsgCanonicalMacCli.trace with
  | [_, _, _, .run ev, _] => ev.input
  | _ => []

def coins3M2Raw : HwBytes :=
  match SignalMsgCanonicalMacCli.trace with
  | [_, _, _, .run ev, _] => ev.coins
  | _ => []

def out3M2Raw : HwBytes :=
  match SignalMsgCanonicalMacCli.trace with
  | [_, _, _, .run ev, _] => match ev.exit with | some (_, b) => b | none => []
  | _ => []

def in4M2Raw : HwBytes :=
  match SignalMsgCanonicalMacCli.trace with
  | [_, _, _, _, .run ev] => ev.input
  | _ => []

def coins4M2Raw : HwBytes :=
  match SignalMsgCanonicalMacCli.trace with
  | [_, _, _, _, .run ev] => ev.coins
  | _ => []

def ev0 : RunEvent :=
  { party := "alice", cmd := .init peerAddrBob "bundle",
    input := bun0Raw, coins := coins0Raw, exit := some (0, out0Raw) }

def ev1_m1 : RunEvent :=
  { party := "alice", cmd := .send peerAddrBob,
    input := pt1M1Raw, coins := coins1Raw, exit := some (0, out1M1Raw) }

def ev2_m1 : RunEvent :=
  { party := "bob", cmd := .recv peerAddrAlice,
    input := out1M1Raw, coins := coins2Raw, exit := some (0, pt1M1Raw) }

def ev3_m1 : RunEvent :=
  { party := "bob", cmd := .recv peerAddrAlice,
    input := out1M1Raw, coins := coins3M1Raw, exit := some (0, pt1M1Raw) }

def ev1_m2 : RunEvent :=
  { party := "alice", cmd := .send peerAddrBob,
    input := pt1M2Raw, coins := coins1Raw, exit := some (0, out1M2Raw) }

def ev2_m2 : RunEvent :=
  { party := "bob", cmd := .recv peerAddrAlice,
    input := out1M2Raw, coins := coins2Raw, exit := some (0, pt1M2Raw) }

def ev3_m2 : RunEvent :=
  { party := "bob", cmd := .send peerAddrAlice,
    input := pt3M2Raw, coins := coins3M2Raw, exit := some (0, out3M2Raw) }

def ev4_m2 : RunEvent :=
  { party := "alice", cmd := .recv peerAddrBob,
    input := in4M2Raw, coins := coins4M2Raw, exit := some (0, pt3M2Raw) }

def m1Events : List CliEvent := [.run ev0, .run ev1_m1, .run ev2_m1, .run ev3_m1]
def m2Events : List CliEvent := [.run ev0, .run ev1_m2, .run ev2_m2, .run ev3_m2, .run ev4_m2]

theorem m1Events_eq : m1Events = DecryptCloneNotPersistedCli.trace := rfl
theorem m2Events_eq : m2Events = SignalMsgCanonicalMacCli.trace := rfl

theorem m1Events_breakFree : BreakFree m1Events :=
  breakFree_map_run [ev0, ev1_m1, ev2_m1, ev3_m1]

theorem m2Events_breakFree : BreakFree m2Events :=
  breakFree_map_run [ev0, ev1_m2, ev2_m2, ev3_m2, ev4_m2]

theorem list_eq_four_splits {α : Type} {x0 x1 x2 x3 y : α} {l1 l2 : List α}
    (h : [x0, x1, x2, x3] = l1 ++ y :: l2) :
    (l1 = [] ∧ y = x0 ∧ l2 = [x1, x2, x3]) ∨
    (l1 = [x0] ∧ y = x1 ∧ l2 = [x2, x3]) ∨
    (l1 = [x0, x1] ∧ y = x2 ∧ l2 = [x3]) ∨
    (l1 = [x0, x1, x2] ∧ y = x3 ∧ l2 = []) := by
  rcases l1 with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, l1⟩⟩⟩⟩ <;> simp at h
  · obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))

theorem list_eq_five_splits {α : Type} {x0 x1 x2 x3 x4 y : α} {l1 l2 : List α}
    (h : [x0, x1, x2, x3, x4] = l1 ++ y :: l2) :
    (l1 = [] ∧ y = x0 ∧ l2 = [x1, x2, x3, x4]) ∨
    (l1 = [x0] ∧ y = x1 ∧ l2 = [x2, x3, x4]) ∨
    (l1 = [x0, x1] ∧ y = x2 ∧ l2 = [x3, x4]) ∨
    (l1 = [x0, x1, x2] ∧ y = x3 ∧ l2 = [x4]) ∨
    (l1 = [x0, x1, x2, x3] ∧ y = x4 ∧ l2 = []) := by
  rcases l1 with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, l1⟩⟩⟩⟩⟩ <;> simp at h
  · obtain ⟨rfl, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  · obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  · obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)))

/-! ## 4. Fast `leBytes` Constants & Raw-to-Fast Bridges -/

def bun0Bytes : HwBytes := leBytes 1813 0x39db4be71a22438b40690e54576b0595cef2ba17dcb76b9bfdfcbbe5e3f0a46f058b13c481302802f416c7bfaf711c9f79fee1b10ed6da870244a9dead09ab129924e194d2d3f256dc13b80696ed45bd6f8a53c23338bd6230b22ffc6ae16ec840541446ceb745fa561a3f66573a5090c9a2b87ab8be4e5e7519ecdaa5c12075fe7a983c49e40f4e18adc4bc544150136410fb5e8b134df4cf49c9a782a30fae7c6a6730e5a15c8c98a7ca06db429c288e0edb0b50aacbadf780913122169c933585485b55c66fe7b12fd6e29c747654eb52777a1c9bdb2698a5deabc12d4a8836b1a2b5adf219026c04a960609525799debb28183e63fc3d7c0c3d676248dafe133c271cbb179e44fd4d192c358bdc5dacb92cfc754e016a09f2e063c1cf2e9192bab5512636755a83f93187193411ad591bf32e9781537797ad075e85babba7411c5629c0a4c14a827c4f5d23a173431dbff1c60cf9d61de4df74faaba831c752e937a154ee5dcc3d4cd2a0163b57c6aa493b48a5bc352483c3050c5a13c5ca45ca97e4bdb6b02f64b994f0e27cd2ae3966599adc5d5ce2cf30db7603b5830f194bcec0a46609eb8666b96b956544b842c090e2a5c97bcd7824740bf9a309ed93553b98987e78a50730870030d8baa5379154690f5c7c8379881eb9f204c6914db10af44fb6130b36e10c7411843b208592631031482623ba57acd8206a512d9adac60a982b96e23740206156b4581316ae0cde5b4abebf0a05ca8b431879e1abcb35c5f642c7b7df1e41cb4563fb95b9047279c637c8426192ddbc81686707375a0040cda42957bc6b1643d223a2ad826874b1342f91f64cc9d9502691a33665693789b71e579f26abef7f467aa1b7837519855ee56d0d5a075c5388af77f304020aaae85211f5f27033136ccc7f3d77c717e1449d21c945ab657a556e90002559353ab3815b458436afa0924f2214c6cb92b75bac17b89838f3cf838b8705fcc31df8d82300f375288d52174749121c2146e65e96420e91feaaa6c98508c5abe1b810972cca0392b511df42338819511dcc44c63b63ef7823318633771ab7fe7f3825802b564183476904e1ca3ad639b09214b840a51c431a42e2401c788229bea2a076640bf52697d2b387cf514588b271deb52ccc1b88f562c4d36e74e3c82619c34cf8c047b769b9d471c690668cd0095afa008781bc599c07a3c609d783c20b7bc085da47d3fe26b902b5d8e1af29e8bbf0e032856e1e143a0081db9fa4c28663a60eb4aab2d50fbc52f11b02280b5594bc153b00cc99887742a0a8095698bbbb15aec4d07cc836378ff7dd3025974212f77e32e84e5711a89a01a9cce0b7a8c63f7aaeaf489c176850cf68330abcffb3f4e92097a49b32c03a8051916605a0a1365a906e671495b8d1aea2ea33c42cdfb6c86d6db1112a34268b80f541874cb7858eaa4bf41ad04d51312974178806558711d7a063200000692a9a230822444d27e1db9839c0c9895d5aebbd55d83d20829726bb4822b13793c783868b5892b9af7a1a0e6fd6fb39b6cb4be3334d370d0fa733a70c854b40720ee6a6bb91568e2aae35b734533aec5063b8455891729246ab6769c5d331387925788bc44f8b1c82d3d75ba11417748d662b168dd386684c2006f18a3af199608b6529d0e5cce7dd3239f954177f7d50347db4dc36e0b3a1d9338b37a1cf505c6a61699edcef61acec89d8fec075af6f3c897537938f1451a6b73005f304778cf94511be967c0d8f29ba5191741109f72020719b146900a48a1f75c27b841c13b75e5e87539e82eaa9652063db370c3994cb95355c9c640eaa0547b0a841386f524109c627b36cf9a18eb42037067f6be0a0778ca6647a455a061ca6dc407641b5cc119914f9662f6b1f1033d0157b8f9d2c057045c0cb236a3a199b3a090251ea410cb6853c3c30bf89ea0ab1765607845fac5f09146c507c6e9535d8b4cd00b518c172fa9f811424971535848604c23bd05c444a266c6f87697838e92b6bc7b8436cb84920f1838b9e71b1b9ab28b51ca6692d540d595a54379671c002de4c1c3fc8f266b2d6e0192688ad6315901a1632c557052a317223fd6f936724e81b1a04a83c56e17780372155f7b440ecce80e5171a231d2aa2bce7dc4dc5046a77386f24cea36a7a936b32120bdaad7051971c59a1dbfab5457481a9679e8c31069752bc3a2a3f64ed5f1249a3dabb2256b1bd702a36f197675683c197d79bd0b78883961b96ce0333104f1bfd98c802c8b319975bed7f7b8db9c4f65e531d4fb74f6502eb7007be7d96654f3af155647c75631f5cc7988b72c0ac80033691eb5d13fa2e808000000098303d1c42c7b9bec09619bcc35d6b963b3fe0ab8a3c7d7a72f2cfc041be0e6eddff3d3ba0e6eb2d11ed7e4604ea967f1ebb4550b6ce2651e53c94b05c5dea8a137fb2de762f64d0b08d8e5a2c0abbfe09c8485bbe6bf0d7eb2c4fb8e7d6043a905000000070000000000000000000000000000000000000000000000000000000000000000000000000000000008ae
private def bun0Chars : List Char := chars_of_hex7003 bun0Raw
private theorem bun0Raw_eq_hex : bun0Raw = hexBytes (str_of_hex7003 bun0Raw) := rfl
private theorem bun0Str_eq : (str_of_hex7003 bun0Raw) = String.ofList bun0Chars := rfl
private theorem bun0Go_eq : hexBytes.go hexDigit bun0Chars = bun0Bytes := by decide +kernel
theorem bun0Raw_eq : bun0Raw = bun0Bytes := by
  rw [bun0Raw_eq_hex, bun0Str_eq, hexBytes_ofList, bun0Go_eq]

def coins0Bytes : HwBytes := leBytes 192 0x2bc4eeb6128b7f6d083f5ab6e2ffd1eaae0b7aeb811e7784d651c787ec1822ca379145498dbf403ffbf678c16b4c891c6373d553e77259fd5969c99e9681362a26d6dba8c3bc43531885d79b1e8fd97c2bd42d454f61f050c87a40044754bd297b63c96f035dba254a8368984d1f01a0af78144d2d60a1d195506e86f58fbb3ebba93a8425f42eed597e6ff646a22848836336f352f6f18babd8caf1ce076e9cd9bc7510b3d2d6a1804dab877fca3b18417756446631596e8a4c403ab71b6d4c
private def coins0Chars : List Char := chars_of_hex7003 coins0Raw
private theorem coins0Raw_eq_hex : coins0Raw = hexBytes (str_of_hex7003 coins0Raw) := rfl
private theorem coins0Str_eq : (str_of_hex7003 coins0Raw) = String.ofList coins0Chars := rfl
private theorem coins0Go_eq : hexBytes.go hexDigit coins0Chars = coins0Bytes := by decide +kernel
theorem coins0Raw_eq : coins0Raw = coins0Bytes := by
  rw [coins0Raw_eq_hex, coins0Str_eq, hexBytes_ofList, coins0Go_eq]

def out0Bytes : HwBytes := []
private def out0Chars : List Char := chars_of_hex7003 out0Raw
private theorem out0Raw_eq_hex : out0Raw = hexBytes (str_of_hex7003 out0Raw) := rfl
private theorem out0Str_eq : (str_of_hex7003 out0Raw) = String.ofList out0Chars := rfl
private theorem out0Go_eq : hexBytes.go hexDigit out0Chars = out0Bytes := by decide +kernel
theorem out0Raw_eq : out0Raw = out0Bytes := by
  rw [out0Raw_eq_hex, out0Str_eq, hexBytes_ofList, out0Go_eq]

def pt1M1Bytes : HwBytes := leBytes 20 0x726566736e6172742d657269772d79616c706572
private def pt1M1Chars : List Char := chars_of_hex7003 pt1M1Raw
private theorem pt1M1Raw_eq_hex : pt1M1Raw = hexBytes (str_of_hex7003 pt1M1Raw) := rfl
private theorem pt1M1Str_eq : (str_of_hex7003 pt1M1Raw) = String.ofList pt1M1Chars := rfl
private theorem pt1M1Go_eq : hexBytes.go hexDigit pt1M1Chars = pt1M1Bytes := by decide +kernel
theorem pt1M1Raw_eq : pt1M1Raw = pt1M1Bytes := by
  rw [pt1M1Raw_eq_hex, pt1M1Str_eq, hexBytes_ofList, pt1M1Go_eq]

def coins1Bytes : HwBytes := leBytes 64 0xde171f78824832651eaacd4181e5662919e731755ea86ab5f6e44b5649b368966be40bda2bd67b154bd869ad12aadb8565893e89ca71434be5c973e76b027184
private def coins1Chars : List Char := chars_of_hex7003 coins1Raw
private theorem coins1Raw_eq_hex : coins1Raw = hexBytes (str_of_hex7003 coins1Raw) := rfl
private theorem coins1Str_eq : (str_of_hex7003 coins1Raw) = String.ofList coins1Chars := rfl
private theorem coins1Go_eq : hexBytes.go hexDigit coins1Chars = coins1Bytes := by decide +kernel
theorem coins1Raw_eq : coins1Raw = coins1Bytes := by
  rw [coins1Raw_eq_hex, coins1Str_eq, hexBytes_ofList, coins1Go_eq]

def out1M1Bytes : HwBytes := leBytes 1813 0x08157342d1c367af43e1e08800463f0b6c1f7fafae6645abd9ed8d651aad850e710a4d736bbebfb72ba932756f2d34f6118853f753de9e246451dbf095674b2a02ae3acb9ae58ffcf98b533ee0378ab60392f3eb73311a3d6514bd23a85b34763755409ac13790ed611a52abea6d6ec8899a3910254f2263147704068d2c0e00ec09a484d6b152d32fdac56878248097c8d558b269b9470f877b4b1a1984b66117be5c162c5ba7bf98add150ee91a2ad53414f93ab440f2d2bd6df355fb6ae3076490c4850a34d663ac1c91a2c3c4cf7a68b42a8fc7ffbcfd4c2f2a7c2e4166c5102eeea848eb8be68e18b8f89f3e7a603b0f5de35c226f72e8957d58aaaecc7b439598d381e363f777cf8ba5a5268dfb78f706b098cba6aba9534ad57d729608dc3f142bd84cbab93041b2b6bc4b62385664bc23469ebc3f89b7c2317be6c970b03957f8712515ffd52920b9f2a083326e4529194c15e7e2c4115436489536eb3f54e2709c524f6e8401a534e75e186db608101152bae1c468e0b930a8d4a9ee37549f9fa8b5a1ccfe09910704c3b12876a2d45360c336694484ea8fcfb1f5890b442692e3959f4afb1ca6fb001cfe254f63ac99979b581f4969aba96003929d1dad4438afeced72f6ca6a3bd899cecb6983b4a9cf1be0d13f032d20e846d2c1dbdb6d0142bd97a8df342fbdb993ae717243a560bea726d97c716e079418206c97bffe50a77569634dac84793b9a150d82ae6e72967a02607c54ac9ef3920f2a1711bc567abb03aa88db074d7fdf98462886679be908461a1e92581c48163f834be9b954b2cafbb80d776025e129a2adf4871d3e6c76c485b587a315667778078e31fc3e5b41c6501db6749ce6e9317ececb0071c490e78d8b81e50c52c2f4f70e78b7b87d517b758f90e5d9406f4f55925f23d6e16dac54b09a50bd743f397b9f08ab5c9bb0f9e5ab3ba0132fb0e4e604b742899701ea90ae39f82539bbc8a76c3722c780bd0dc7906c8a4038b80b2ffb385d4796f0f549fca053e912802987c2b760fb3c61cc5d9ac5a59f9b30a09ffec694df3bf8779224329b9feffe94be0aada02079a997fc6791ae60d4514169101e76748ff5383c6e268dd8e402ebe3087356c867d1a32187e92ebe09bf644fef415dfb1d7f51e10500f86fb11992e9de39b5ce7db4ee7d8ff4b585b0c3aaf4cb96068e13a03ca4bf49cf8db4ba038c9a37d86d79786a5201c62586adbe1386e56d3271f43bcab5111b0df37276a9fa476409d4d3789052e16fc1e6bb477604b3f0ea3af8febab1812366be48ead134621247b2ce7d765eb117927864ce1a42f913d67700dbd2b022eb9e355e032d94fe74a5e0f1774d197ebb3d23bef05cae04c490f31caf6e247c92d4f3c85e27ba643c618e045bc8d5ab7ee41049b7091d14974306ab0de5ccb7abeccbe8b0226ec7e193d256bbd71b49055753c0f76fd91ace9728ccea9b195bac75b12c569a546d77458e231f21e643eb514b1d52d43c89c97e347456c69849d80bfe87d056875c5340c765583e7ea95e4bcbf99ec96b4a57d06113974f26b7669835b288975a9cbe167d0f0fae7fa230260fa9377c478d2239687833b1315992b40b13b63bd38a237564be2442941644bd6e65c5b430ce9ba08c47421103dba079d9e106672753785d791749006348fc041bb6fa54e237c980695450bde85a48b99162a33681c0b2ed740acdcf5bd9ae36566497a4cddfcfaa8417272782e4c151b097a28c09261013205e8c679899bd5daa710881fe67dfd921b740503664bf5312aacd73370ef78ac2783e718ff980a2880861ea1983774c8cd5606d003e019fff66bd9357f49f2b290eab4e20681538ff1aeaa6e9d1529d6a73f8d47192ba58984995d30a60cfb8c894734b8295f03def3c686effd82cdfc60448eb59eef9162b0fcea781b92e05268a6f8f1958d51f69c55bd458016ee7dd9cd41bbda13bd49150878b600b9bb36dbfd062dcf5f9b87840502e3c29505297c65bad6cc67cdb11351b65c059fc81136fb84481e31d7f2049433a525b3a734889782840ab6286f28e92855eb01b41e1288bbe35ea883a0a9fd3f0dac922c061b7330b5f14bf8442742ffc723538018f0665f00df17f3f7cfa0834c87c610dda328aab76d946edbca5b4beeb89778445115ec1abc551e17d274c4bc20fc5eb10961b937ae5990e8e4d9120f080ca1420938073008d72877faff36ebc36f8301f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a002432c20f0e0a6df151c808705bc8f868b0b9c9e67ff3b643a7097764ed6f2d27782f0001010101252a77fcacd933fb2da2d0df911b453d5c189821af6a2bcc1e7cd2594e9fba553a032022001800105f76647da8f9eff37b43185e2b9537442e866cbb05f716eb3c69e9038c94c31d05210a44019f226f70c3a23cdfd99e2f2fcd891a46c9b60277d75d5b9b32678f590412e87ce65405211a4191d00ca5dd02c28c8762756784ce34df71893c8f43045b330e89b246e2d7940521124403
private def out1M1Chars : List Char := chars_of_hex7003 out1M1Raw
private theorem out1M1Raw_eq_hex : out1M1Raw = hexBytes (str_of_hex7003 out1M1Raw) := rfl
private theorem out1M1Str_eq : (str_of_hex7003 out1M1Raw) = String.ofList out1M1Chars := rfl
private theorem out1M1Go_eq : hexBytes.go hexDigit out1M1Chars = out1M1Bytes := by decide +kernel
theorem out1M1Raw_eq : out1M1Raw = out1M1Bytes := by
  rw [out1M1Raw_eq_hex, out1M1Str_eq, hexBytes_ofList, out1M1Go_eq]

def coins2Bytes : HwBytes := leBytes 32 0x6ed24d47021506af37bdb42f9be02955f166a99eb814489f19354db373c86270
private def coins2Chars : List Char := chars_of_hex7003 coins2Raw
private theorem coins2Raw_eq_hex : coins2Raw = hexBytes (str_of_hex7003 coins2Raw) := rfl
private theorem coins2Str_eq : (str_of_hex7003 coins2Raw) = String.ofList coins2Chars := rfl
private theorem coins2Go_eq : hexBytes.go hexDigit coins2Chars = coins2Bytes := by decide +kernel
theorem coins2Raw_eq : coins2Raw = coins2Bytes := by
  rw [coins2Raw_eq_hex, coins2Str_eq, hexBytes_ofList, coins2Go_eq]

def coins3M1Bytes : HwBytes := leBytes 32 0x29d9f938fcf0ffc541c95556f4a4f76b8240f422c45bf97ae9c9fecab9253c68
private def coins3M1Chars : List Char := chars_of_hex7003 coins3M1Raw
private theorem coins3M1Raw_eq_hex : coins3M1Raw = hexBytes (str_of_hex7003 coins3M1Raw) := rfl
private theorem coins3M1Str_eq : (str_of_hex7003 coins3M1Raw) = String.ofList coins3M1Chars := rfl
private theorem coins3M1Go_eq : hexBytes.go hexDigit coins3M1Chars = coins3M1Bytes := by decide +kernel
theorem coins3M1Raw_eq : coins3M1Raw = coins3M1Bytes := by
  rw [coins3M1Raw_eq_hex, coins3M1Str_eq, hexBytes_ofList, coins3M1Go_eq]

def pt1M2Bytes : HwBytes := leBytes 17 0x6e6f69737365732d6873696c6261747365
private def pt1M2Chars : List Char := chars_of_hex7003 pt1M2Raw
private theorem pt1M2Raw_eq_hex : pt1M2Raw = hexBytes (str_of_hex7003 pt1M2Raw) := rfl
private theorem pt1M2Str_eq : (str_of_hex7003 pt1M2Raw) = String.ofList pt1M2Chars := rfl
private theorem pt1M2Go_eq : hexBytes.go hexDigit pt1M2Chars = pt1M2Bytes := by decide +kernel
theorem pt1M2Raw_eq : pt1M2Raw = pt1M2Bytes := by
  rw [pt1M2Raw_eq_hex, pt1M2Str_eq, hexBytes_ofList, pt1M2Go_eq]

def out1M2Bytes : HwBytes := leBytes 1813 0x08157342d1c367af43e1e08800463f0b6c1f7fafae6645abd9ed8d651aad850e710a4d736bbebfb72ba932756f2d34f6118853f753de9e246451dbf095674b2a02ae3acb9ae58ffcf98b533ee0378ab60392f3eb73311a3d6514bd23a85b34763755409ac13790ed611a52abea6d6ec8899a3910254f2263147704068d2c0e00ec09a484d6b152d32fdac56878248097c8d558b269b9470f877b4b1a1984b66117be5c162c5ba7bf98add150ee91a2ad53414f93ab440f2d2bd6df355fb6ae3076490c4850a34d663ac1c91a2c3c4cf7a68b42a8fc7ffbcfd4c2f2a7c2e4166c5102eeea848eb8be68e18b8f89f3e7a603b0f5de35c226f72e8957d58aaaecc7b439598d381e363f777cf8ba5a5268dfb78f706b098cba6aba9534ad57d729608dc3f142bd84cbab93041b2b6bc4b62385664bc23469ebc3f89b7c2317be6c970b03957f8712515ffd52920b9f2a083326e4529194c15e7e2c4115436489536eb3f54e2709c524f6e8401a534e75e186db608101152bae1c468e0b930a8d4a9ee37549f9fa8b5a1ccfe09910704c3b12876a2d45360c336694484ea8fcfb1f5890b442692e3959f4afb1ca6fb001cfe254f63ac99979b581f4969aba96003929d1dad4438afeced72f6ca6a3bd899cecb6983b4a9cf1be0d13f032d20e846d2c1dbdb6d0142bd97a8df342fbdb993ae717243a560bea726d97c716e079418206c97bffe50a77569634dac84793b9a150d82ae6e72967a02607c54ac9ef3920f2a1711bc567abb03aa88db074d7fdf98462886679be908461a1e92581c48163f834be9b954b2cafbb80d776025e129a2adf4871d3e6c76c485b587a315667778078e31fc3e5b41c6501db6749ce6e9317ececb0071c490e78d8b81e50c52c2f4f70e78b7b87d517b758f90e5d9406f4f55925f23d6e16dac54b09a50bd743f397b9f08ab5c9bb0f9e5ab3ba0132fb0e4e604b742899701ea90ae39f82539bbc8a76c3722c780bd0dc7906c8a4038b80b2ffb385d4796f0f549fca053e912802987c2b760fb3c61cc5d9ac5a59f9b30a09ffec694df3bf8779224329b9feffe94be0aada02079a997fc6791ae60d4514169101e76748ff5383c6e268dd8e402ebe3087356c867d1a32187e92ebe09bf644fef415dfb1d7f51e10500f86fb11992e9de39b5ce7db4ee7d8ff4b585b0c3aaf4cb96068e13a03ca4bf49cf8db4ba038c9a37d86d79786a5201c62586adbe1386e56d3271f43bcab5111b0df37276a9fa476409d4d3789052e16fc1e6bb477604b3f0ea3af8febab1812366be48ead134621247b2ce7d765eb117927864ce1a42f913d67700dbd2b022eb9e355e032d94fe74a5e0f1774d197ebb3d23bef05cae04c490f31caf6e247c92d4f3c85e27ba643c618e045bc8d5ab7ee41049b7091d14974306ab0de5ccb7abeccbe8b0226ec7e193d256bbd71b49055753c0f76fd91ace9728ccea9b195bac75b12c569a546d77458e231f21e643eb514b1d52d43c89c97e347456c69849d80bfe87d056875c5340c765583e7ea95e4bcbf99ec96b4a57d06113974f26b7669835b288975a9cbe167d0f0fae7fa230260fa9377c478d2239687833b1315992b40b13b63bd38a237564be2442941644bd6e65c5b430ce9ba08c47421103dba079d9e106672753785d791749006348fc041bb6fa54e237c980695450bde85a48b99162a33681c0b2ed740acdcf5bd9ae36566497a4cddfcfaa8417272782e4c151b097a28c09261013205e8c679899bd5daa710881fe67dfd921b740503664bf5312aacd73370ef78ac2783e718ff980a2880861ea1983774c8cd5606d003e019fff66bd9357f49f2b290eab4e20681538ff1aeaa6e9d1529d6a73f8d47192ba58984995d30a60cfb8c894734b8295f03def3c686effd82cdfc60448eb59eef9162b0fcea781b92e05268a6f8f1958d51f69c55bd458016ee7dd9cd41bbda13bd49150878b600b9bb36dbfd062dcf5f9b87840502e3c29505297c65bad6cc67cdb11351b65c059fc81136fb84481e31d7f2049433a525b3a734889782840ab6286f28e92855eb01b41e1288bbe35ea883a0a9fd3f0dac922c061b7330b5f14bf8442742ffc723538018f0665f00df17f3f7cfa0834c87c610dda328aab76d946edbca5b4beeb89778445115ec1abc551e17d274c4bc20fc5eb10961b937ae5990e8e4d9120f080ca1420938073008d728b3d2d3d3d90ece8201f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a002432c20f0e0a6df151c808705bc8f868b0b9c9e67ff3b643a7097764ed6f2d27782f0001010101252a9f2c2254ffda392774931baccae040a31930f1ff1a4808a728152518cef704c72022001800105f76647da8f9eff37b43185e2b9537442e866cbb05f716eb3c69e9038c94c31d05210a44019f226f70c3a23cdfd99e2f2fcd891a46c9b60277d75d5b9b32678f590412e87ce65405211a4191d00ca5dd02c28c8762756784ce34df71893c8f43045b330e89b246e2d7940521124403
private def out1M2Chars : List Char := chars_of_hex7003 out1M2Raw
private theorem out1M2Raw_eq_hex : out1M2Raw = hexBytes (str_of_hex7003 out1M2Raw) := rfl
private theorem out1M2Str_eq : (str_of_hex7003 out1M2Raw) = String.ofList out1M2Chars := rfl
private theorem out1M2Go_eq : hexBytes.go hexDigit out1M2Chars = out1M2Bytes := by decide +kernel
theorem out1M2Raw_eq : out1M2Raw = out1M2Bytes := by
  rw [out1M2Raw_eq_hex, out1M2Str_eq, hexBytes_ofList, out1M2Go_eq]

def pt3M2Bytes : HwBytes := leBytes 19 0x796c7065722d646574616369746e6568747561
private def pt3M2Chars : List Char := chars_of_hex7003 pt3M2Raw
private theorem pt3M2Raw_eq_hex : pt3M2Raw = hexBytes (str_of_hex7003 pt3M2Raw) := rfl
private theorem pt3M2Str_eq : (str_of_hex7003 pt3M2Raw) = String.ofList pt3M2Chars := rfl
private theorem pt3M2Go_eq : hexBytes.go hexDigit pt3M2Chars = pt3M2Bytes := by decide +kernel
theorem pt3M2Raw_eq : pt3M2Raw = pt3M2Bytes := by
  rw [pt3M2Raw_eq_hex, pt3M2Str_eq, hexBytes_ofList, pt3M2Go_eq]

def coins3M2Bytes : HwBytes := leBytes 64 0x5bda890c5f5fa0760d9cde0faa6977e0c62b976079e9deb19a0b39d140c2681529d9f938fcf0ffc541c95556f4a4f76b8240f422c45bf97ae9c9fecab9253c68
private def coins3M2Chars : List Char := chars_of_hex7003 coins3M2Raw
private theorem coins3M2Raw_eq_hex : coins3M2Raw = hexBytes (str_of_hex7003 coins3M2Raw) := rfl
private theorem coins3M2Str_eq : (str_of_hex7003 coins3M2Raw) = String.ofList coins3M2Chars := rfl
private theorem coins3M2Go_eq : hexBytes.go hexDigit coins3M2Chars = coins3M2Bytes := by decide +kernel
theorem coins3M2Raw_eq : coins3M2Raw = coins3M2Bytes := by
  rw [coins3M2Raw_eq_hex, coins3M2Str_eq, hexBytes_ofList, coins3M2Go_eq]

def out3M2Bytes : HwBytes := leBytes 89 0x5cf306cd3f2d0f6200010101042aa39246265b8ed09def86b4b169bba133a71d50fd0854ebe96550c97b26b68dd82022001800101cd39fadc085052bd43f40d71f98ea8e78c6aff64bac6e587f231e78128fb95805210a4402
private def out3M2Chars : List Char := chars_of_hex7003 out3M2Raw
private theorem out3M2Raw_eq_hex : out3M2Raw = hexBytes (str_of_hex7003 out3M2Raw) := rfl
private theorem out3M2Str_eq : (str_of_hex7003 out3M2Raw) = String.ofList out3M2Chars := rfl
private theorem out3M2Go_eq : hexBytes.go hexDigit out3M2Chars = out3M2Bytes := by decide +kernel
theorem out3M2Raw_eq : out3M2Raw = out3M2Bytes := by
  rw [out3M2Raw_eq_hex, out3M2Str_eq, hexBytes_ofList, out3M2Go_eq]

def in4M2Bytes : HwBytes := leBytes 93 0x5cf306cd3f2d0f6200010101042aa39246265b8ed09def86b4b169bba133a71d50fd0854ebe96550c97b26b68dd82022001800101cd39fadc085052bd43f40d71f98ea8e78c6aff64bac6e587f231e78128fb95805210a01782a104f02
private def in4M2Chars : List Char := chars_of_hex7003 in4M2Raw
private theorem in4M2Raw_eq_hex : in4M2Raw = hexBytes (str_of_hex7003 in4M2Raw) := rfl
private theorem in4M2Str_eq : (str_of_hex7003 in4M2Raw) = String.ofList in4M2Chars := rfl
private theorem in4M2Go_eq : hexBytes.go hexDigit in4M2Chars = in4M2Bytes := by decide +kernel
theorem in4M2Raw_eq : in4M2Raw = in4M2Bytes := by
  rw [in4M2Raw_eq_hex, in4M2Str_eq, hexBytes_ofList, in4M2Go_eq]

def coins4M2Bytes : HwBytes := leBytes 32 0x911a74b930f8ffed7ffa796f019a35a6bd93dffe566f2333fdb08281e36eaaa7
private def coins4M2Chars : List Char := chars_of_hex7003 coins4M2Raw
private theorem coins4M2Raw_eq_hex : coins4M2Raw = hexBytes (str_of_hex7003 coins4M2Raw) := rfl
private theorem coins4M2Str_eq : (str_of_hex7003 coins4M2Raw) = String.ofList coins4M2Chars := rfl
private theorem coins4M2Go_eq : hexBytes.go hexDigit coins4M2Chars = coins4M2Bytes := by decide +kernel
theorem coins4M2Raw_eq : coins4M2Raw = coins4M2Bytes := by
  rw [coins4M2Raw_eq_hex, coins4M2Str_eq, hexBytes_ofList, coins4M2Go_eq]

/-! ## 5. Protocol Crypto & Wire Sub-Constants -/

def ek0Bytes : HwBytes := leBytes 32 0xd9bc7510b3d2d6a1804dab877fca3b18417756446631596e8a4c403ab71b6d4c
def ent0Bytes : HwBytes := leBytes 32 0x493fc11c53fd9e2aa8539b7c455004296f2598a04dd1863e84edf648f38bf19c
def dhsA0Bytes : HwBytes := leBytes 32 0x2bc4eeb6128b7f6d083f5ab6e2ffd1eaae0b7aeb811e7784d651c787ec1822ca
def kyberCt0Bytes : HwBytes := leBytes 1568 0x08157342d1c367af43e1e08800463f0b6c1f7fafae6645abd9ed8d651aad850e710a4d736bbebfb72ba932756f2d34f6118853f753de9e246451dbf095674b2a02ae3acb9ae58ffcf98b533ee0378ab60392f3eb73311a3d6514bd23a85b34763755409ac13790ed611a52abea6d6ec8899a3910254f2263147704068d2c0e00ec09a484d6b152d32fdac56878248097c8d558b269b9470f877b4b1a1984b66117be5c162c5ba7bf98add150ee91a2ad53414f93ab440f2d2bd6df355fb6ae3076490c4850a34d663ac1c91a2c3c4cf7a68b42a8fc7ffbcfd4c2f2a7c2e4166c5102eeea848eb8be68e18b8f89f3e7a603b0f5de35c226f72e8957d58aaaecc7b439598d381e363f777cf8ba5a5268dfb78f706b098cba6aba9534ad57d729608dc3f142bd84cbab93041b2b6bc4b62385664bc23469ebc3f89b7c2317be6c970b03957f8712515ffd52920b9f2a083326e4529194c15e7e2c4115436489536eb3f54e2709c524f6e8401a534e75e186db608101152bae1c468e0b930a8d4a9ee37549f9fa8b5a1ccfe09910704c3b12876a2d45360c336694484ea8fcfb1f5890b442692e3959f4afb1ca6fb001cfe254f63ac99979b581f4969aba96003929d1dad4438afeced72f6ca6a3bd899cecb6983b4a9cf1be0d13f032d20e846d2c1dbdb6d0142bd97a8df342fbdb993ae717243a560bea726d97c716e079418206c97bffe50a77569634dac84793b9a150d82ae6e72967a02607c54ac9ef3920f2a1711bc567abb03aa88db074d7fdf98462886679be908461a1e92581c48163f834be9b954b2cafbb80d776025e129a2adf4871d3e6c76c485b587a315667778078e31fc3e5b41c6501db6749ce6e9317ececb0071c490e78d8b81e50c52c2f4f70e78b7b87d517b758f90e5d9406f4f55925f23d6e16dac54b09a50bd743f397b9f08ab5c9bb0f9e5ab3ba0132fb0e4e604b742899701ea90ae39f82539bbc8a76c3722c780bd0dc7906c8a4038b80b2ffb385d4796f0f549fca053e912802987c2b760fb3c61cc5d9ac5a59f9b30a09ffec694df3bf8779224329b9feffe94be0aada02079a997fc6791ae60d4514169101e76748ff5383c6e268dd8e402ebe3087356c867d1a32187e92ebe09bf644fef415dfb1d7f51e10500f86fb11992e9de39b5ce7db4ee7d8ff4b585b0c3aaf4cb96068e13a03ca4bf49cf8db4ba038c9a37d86d79786a5201c62586adbe1386e56d3271f43bcab5111b0df37276a9fa476409d4d3789052e16fc1e6bb477604b3f0ea3af8febab1812366be48ead134621247b2ce7d765eb117927864ce1a42f913d67700dbd2b022eb9e355e032d94fe74a5e0f1774d197ebb3d23bef05cae04c490f31caf6e247c92d4f3c85e27ba643c618e045bc8d5ab7ee41049b7091d14974306ab0de5ccb7abeccbe8b0226ec7e193d256bbd71b49055753c0f76fd91ace9728ccea9b195bac75b12c569a546d77458e231f21e643eb514b1d52d43c89c97e347456c69849d80bfe87d056875c5340c765583e7ea95e4bcbf99ec96b4a57d06113974f26b7669835b288975a9cbe167d0f0fae7fa230260fa9377c478d2239687833b1315992b40b13b63bd38a237564be2442941644bd6e65c5b430ce9ba08c47421103dba079d9e106672753785d791749006348fc041bb6fa54e237c980695450bde85a48b99162a33681c0b2ed740acdcf5bd9ae36566497a4cddfcfaa8417272782e4c151b097a28c09261013205e8c679899bd5daa710881fe67dfd921b740503664bf5312aacd73370ef78ac2783e718ff980a2880861ea1983774c8cd5606d003e019fff66bd9357f49f2b290eab4e20681538ff1aeaa6e9d1529d6a73f8d47192ba58984995d30a60cfb8c894734b8295f03def3c686effd82cdfc60448eb59eef9162b0fcea781b92e05268a6f8f1958d51f69c55bd458016ee7dd9cd41bbda13bd49150878b600b9bb36dbfd062dcf5f9b87840502e3c29505297c65bad6cc67cdb11351b65c059fc81136fb84481e31d7f2049433a525b3a734889782840ab6286f28e92855eb01b41e1288bbe35ea883a0a9fd3f0dac922c061b7330b5f14bf8442742ffc723538018f0665f00df17f3f7cfa0834c87c610dda328aab76d946edbca5b4beeb89778445115ec1abc551e17d274c4bc20fc5eb10961b937ae5990e8e4d9120f
def kyberSs0Bytes : HwBytes := leBytes 32 0x59920ad96193931f3d01f1adc28ba6110b3342ded884eb9323999ce16e0e85d8
def rk0Bytes : HwBytes := leBytes 32 0x5be241056f0a0d329c6f6581b1778631a7c9d74f96cc88387c695805845ecd08
def ck0Bytes : HwBytes := leBytes 32 0x3b06cb3133113b84f1e0be49f227edd6d4182852ff8555446ce25c958282bb22
def pqrBytes : HwBytes := leBytes 32 0xb46d2bdd11b558d5e91c43c08f4bfececa40c8fdf71358789adac0d1f7271a88
def prkA1Bytes : HwBytes := leBytes 32 0xd00a2bc973eedcf4dfa238426e7c2a6330a5913955455a459c1cb73604b54932
def rk1Bytes : HwBytes := leBytes 32 0xf3bb7c4a02b30500396dd37feb194a199a61cc5ce8d859c51a9eee4984f2c19e
def cksA0Bytes : HwBytes := leBytes 32 0x430eee9bc333cc3996374a42ba60b6c04b320d829c73019b01bbc2a9e6ba7761
def cksA1Bytes : HwBytes := leBytes 32 0x5bc19e6c86137447d64a35e5259929754dce722abb1353435ece70da8cd2da7b
def seedA0Bytes : HwBytes := leBytes 32 0x80ff64ba4f241ac36f1bcc690d25e5bd8f43d2281e9e3c4994f92821d3d3c64b
def salt1Bytes : HwBytes := leBytes 32 0x730a5aa2cc08006ff3eb1eb9dcf77c1983a9d8e511f5c9f761dc95d435380322
def prkMsg1Bytes : HwBytes := leBytes 32 0x8bc6ec195606af85a8475161cdd993c269e26d7774d53c960158518a13c9cf53
def encKey1Bytes : HwBytes := leBytes 32 0x75cda8f74f0dca433bd25ed143a8d794963f2524af10b01874d23214baf6f10d
def macKey1Bytes : HwBytes := leBytes 32 0x22f78ca921b1b815175c8dd13bf0a2fbb8a193b0f948f09187d95861ff010d62
def iv1Bytes : HwBytes := leBytes 16 0xddd85e8a03dfc0ed9bf161bf977fe90b
def pqMsg1Bytes : HwBytes := leBytes 37 0xc20f0e0a6df151c808705bc8f868b0b9c9e67ff3b643a7097764ed6f2d27782f0001010101
def addr1Bytes : HwBytes := leBytes 36 0x01f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a00
def ct1M1Bytes : HwBytes := leBytes 32 0x77fcacd933fb2da2d0df911b453d5c189821af6a2bcc1e7cd2594e9fba553a03
def wire1M1Bytes : HwBytes := leBytes 151 0x01f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a002432c20f0e0a6df151c808705bc8f868b0b9c9e67ff3b643a7097764ed6f2d27782f0001010101252a77fcacd933fb2da2d0df911b453d5c189821af6a2bcc1e7cd2594e9fba553a032022001800105f76647da8f9eff37b43185e2b9537442e866cbb05f716eb3c69e9038c94c31d05210a44
def mac1M1Bytes : HwBytes := leBytes 8 0x77faff36ebc36f83
def msg1M1Bytes : HwBytes := leBytes 159 0x77faff36ebc36f8301f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a002432c20f0e0a6df151c808705bc8f868b0b9c9e67ff3b643a7097764ed6f2d27782f0001010101252a77fcacd933fb2da2d0df911b453d5c189821af6a2bcc1e7cd2594e9fba553a032022001800105f76647da8f9eff37b43185e2b9537442e866cbb05f716eb3c69e9038c94c31d05210a44
def macIn1M1Bytes : HwBytes := leBytes 217 0x01f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a002432c20f0e0a6df151c808705bc8f868b0b9c9e67ff3b643a7097764ed6f2d27782f0001010101252a77fcacd933fb2da2d0df911b453d5c189821af6a2bcc1e7cd2594e9fba553a032022001800105f76647da8f9eff37b43185e2b9537442e866cbb05f716eb3c69e9038c94c31d05210a4439db4be71a22438b40690e54576b0595cef2ba17dcb76b9bfdfcbbe5e3f0a46f056f70c3a23cdfd99e2f2fcd891a46c9b60277d75d5b9b32678f590412e87ce65405
def ct1M2Bytes : HwBytes := leBytes 32 0x9f2c2254ffda392774931baccae040a31930f1ff1a4808a728152518cef704c7
def wire1M2Bytes : HwBytes := leBytes 151 0x01f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a002432c20f0e0a6df151c808705bc8f868b0b9c9e67ff3b643a7097764ed6f2d27782f0001010101252a9f2c2254ffda392774931baccae040a31930f1ff1a4808a728152518cef704c72022001800105f76647da8f9eff37b43185e2b9537442e866cbb05f716eb3c69e9038c94c31d05210a44
def mac1M2Bytes : HwBytes := leBytes 8 0xb3d2d3d3d90ece82
def msg1M2Bytes : HwBytes := leBytes 159 0xb3d2d3d3d90ece8201f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a002432c20f0e0a6df151c808705bc8f868b0b9c9e67ff3b643a7097764ed6f2d27782f0001010101252a9f2c2254ffda392774931baccae040a31930f1ff1a4808a728152518cef704c72022001800105f76647da8f9eff37b43185e2b9537442e866cbb05f716eb3c69e9038c94c31d05210a44
def macIn1M2Bytes : HwBytes := leBytes 217 0x01f6e5d4c3b2a10f8e9d4c8b7a102f3e5d00016b5a4f3e2d1c0b9a5f4e4d3b2e1c6f8a002432c20f0e0a6df151c808705bc8f868b0b9c9e67ff3b643a7097764ed6f2d27782f0001010101252a9f2c2254ffda392774931baccae040a31930f1ff1a4808a728152518cef704c72022001800105f76647da8f9eff37b43185e2b9537442e866cbb05f716eb3c69e9038c94c31d05210a4439db4be71a22438b40690e54576b0595cef2ba17dcb76b9bfdfcbbe5e3f0a46f056f70c3a23cdfd99e2f2fcd891a46c9b60277d75d5b9b32678f590412e87ce65405
def prkB1Bytes : HwBytes := leBytes 32 0x16297df8efb5cb63359361a7ed236cf26ce9898d74a7b2ec269cd7859e35c585
def rk2Bytes : HwBytes := leBytes 32 0x8aa867412882726e3513187ea03e33f950728e186f91ae3e5e943bd43090c70e
def cksB0Bytes : HwBytes := leBytes 32 0xc23df73db5841eae70619b6b208d7b2f478218cfc97069fa7cd4f6d4f2053866
def cksB1Bytes : HwBytes := leBytes 32 0x0be90377dc56518fc8d6f8e5645f7ae83ff8ecffd37e5ccaba4365ae1411780e
def seedB0Bytes : HwBytes := leBytes 32 0x488a8593c1e259c9e2a80beebc0532cc00cf04132e8d18a97489611988d6d9fe
def salt3Bytes : HwBytes := leBytes 32 0x8629792bc15c60339e9bae1fe878062eec9e1b5741fa20aa884c7ecd92619983
def prkMsg3Bytes : HwBytes := leBytes 32 0xfc856e226aaaac15dd792d9b0d3862ff94ca7eb493e8d87da0a0655ca320311f
def encKey3Bytes : HwBytes := leBytes 32 0x6b3a160c55b1505bae804da2eabf33e8b0aa8097987a4cfada3841c07e2ec632
def macKey3Bytes : HwBytes := leBytes 32 0x9f1d83f1d3a30c3e0729ec99c1828889a0aff56910016e47103fd911f370ff15
def iv3Bytes : HwBytes := leBytes 16 0x3c47d809ee2dd6c7df0f65cd9f87a88e
def pqMsg3Bytes : HwBytes := leBytes 4 0x00010101
def ct3M2Bytes : HwBytes := leBytes 32 0xa39246265b8ed09def86b4b169bba133a71d50fd0854ebe96550c97b26b68dd8
def wire3M2Bytes : HwBytes := leBytes 80 0x00010101042aa39246265b8ed09def86b4b169bba133a71d50fd0854ebe96550c97b26b68dd82022001800101cd39fadc085052bd43f40d71f98ea8e78c6aff64bac6e587f231e78128fb95805210a44
def mac3M2Bytes : HwBytes := leBytes 8 0x5cf306cd3f2d0f62
def body3M2Bytes : HwBytes := leBytes 88 0x5cf306cd3f2d0f6200010101042aa39246265b8ed09def86b4b169bba133a71d50fd0854ebe96550c97b26b68dd82022001800101cd39fadc085052bd43f40d71f98ea8e78c6aff64bac6e587f231e78128fb95805210a44
def macIn3M2Bytes : HwBytes := leBytes 146 0x00010101042aa39246265b8ed09def86b4b169bba133a71d50fd0854ebe96550c97b26b68dd82022001800101cd39fadc085052bd43f40d71f98ea8e78c6aff64bac6e587f231e78128fb95805210a446f70c3a23cdfd99e2f2fcd891a46c9b60277d75d5b9b32678f590412e87ce6540539db4be71a22438b40690e54576b0595cef2ba17dcb76b9bfdfcbbe5e3f0a46f05
def prkPqxdhBytes : HwBytes := leBytes 32 0xf6815a103604e22898f052e184c243d134fff34377e1b8ccb39568de93293468
def ivBlock1Bytes : HwBytes := leBytes 32 0xb619121ef7a2db8e33011113d6fe381bddd85e8a03dfc0ed9bf161bf977fe90b
def ivBlock3Bytes : HwBytes := leBytes 32 0xe1dca467fa64a4df62976748e1f3ad053c47d809ee2dd6c7df0f65cd9f87a88e
def wire4M2Bytes : HwBytes := leBytes 84 0x00010101042aa39246265b8ed09def86b4b169bba133a71d50fd0854ebe96550c97b26b68dd82022001800101cd39fadc085052bd43f40d71f98ea8e78c6aff64bac6e587f231e78128fb95805210a01782a104f
def body4M2Bytes : HwBytes := leBytes 92 0x5cf306cd3f2d0f6200010101042aa39246265b8ed09def86b4b169bba133a71d50fd0854ebe96550c97b26b68dd82022001800101cd39fadc085052bd43f40d71f98ea8e78c6aff64bac6e587f231e78128fb95805210a01782a104f
def infoPqxdhBytes : HwBytes := leBytes 46 0x343230312d524542594b2d534c4154535952435f3635322d4148535f3931353532585f7478655472657073696857
def infoRatchetBytes : HwBytes := leBytes 14 0x7465686374615272657073696857
def infoMessageKeysBytes : HwBytes := leBytes 18 0x7379654b6567617373654d72657073696857

/-! ## 6. Kernel-Checked Concrete Wire, Coin, and KDF Facts -/

def checkPreKey7003 (w : HwBytes) (msg wire mac ct pq : HwBytes) : Bool :=
  match parsePreKeyWire w with
  | some p =>
    decide (p.version = 4) &&
    decide (p.preKeyId = none) &&
    decide (p.signedPreKeyId = 7) &&
    decide (p.kyberPreKeyId = some 9) &&
    decide (p.kyberCiphertext = some (kyberKey kyberCt0Bytes)) &&
    decide (p.baseKey = ecKey (compPubOfIdx 3)) &&
    decide (p.baseKey.take 33 = ecKey (compPubOfIdx 3)) &&
    decide (p.identityKey = ecKey (compPubOfIdx 0)) &&
    decide (p.identityKey.take 33 = ecKey (compPubOfIdx 0)) &&
    decide (p.message = msg) &&
    decide (msg.take (msg.length - 8) = wire) &&
    decide (msg.drop (msg.length - 8) = mac) &&
    decide (p.inner.ciphertext = ct) &&
    decide (p.inner.senderRatchetKey.bytes.toList = compPubOfIdx 4) &&
    decide (p.inner.counter = 0) &&
    decide (p.inner.previousCounter = 0) &&
    decide (p.inner.messageVersion = 4) &&
    decide (p.inner.pqRatchet = pq) &&
    decide (preKeySpqrIndex p = 1)
  | none => false

theorem checkPreKey7003_m1 :
    checkPreKey7003 out1M1Bytes msg1M1Bytes wire1M1Bytes mac1M1Bytes ct1M1Bytes pqMsg1Bytes = true := by
  decide +kernel

theorem checkPreKey7003_m2 :
    checkPreKey7003 out1M2Bytes msg1M2Bytes wire1M2Bytes mac1M2Bytes ct1M2Bytes pqMsg1Bytes = true := by
  decide +kernel

theorem out1M1_preKeyWire_eq :
    out1M1Bytes = preKeyWire none 7 9 1111 (ecKey (compPubOfIdx 0))
      (compPubOfIdx 3) kyberCt0Bytes msg1M1Bytes := by
  decide +kernel

theorem out1M2_preKeyWire_eq :
    out1M2Bytes = preKeyWire none 7 9 1111 (ecKey (compPubOfIdx 0))
      (compPubOfIdx 3) kyberCt0Bytes msg1M2Bytes := by
  decide +kernel

theorem out3M2_split_eq :
    out3M2Bytes = wireWhisperTag :: body3M2Bytes ∧
    body3M2Bytes = wire3M2Bytes ++ mac3M2Bytes ∧
    body3M2Bytes.take (body3M2Bytes.length - 8) = wire3M2Bytes ∧
    body3M2Bytes.drop (body3M2Bytes.length - 8) = mac3M2Bytes ∧
    wire3M2Bytes.length = 80 ∧
    mac3M2Bytes.length = 8 := by
  decide +kernel

theorem in4M2_split_eq :
    in4M2Bytes = wireWhisperTag :: body4M2Bytes ∧
    body4M2Bytes = wire4M2Bytes ++ mac3M2Bytes ∧
    body4M2Bytes.take (body4M2Bytes.length - 8) = wire4M2Bytes ∧
    body4M2Bytes.drop (body4M2Bytes.length - 8) = mac3M2Bytes ∧
    wire4M2Bytes.length = 84 ∧
    parsePreKeyWire in4M2Bytes = none := by
  decide +kernel

def checkWhisper4M2 : Bool :=
  match CryptoGames.LibsignalSession.SignalMessage.tryFrom
      CryptoVerification.LibsignalProtoCodec.protoSignalCodec body4M2Bytes with
  | .ok m =>
    decide (m.ciphertext = ct3M2Bytes) &&
    decide (m.senderRatchetKey.bytes.toList = compPubOfIdx 5) &&
    decide (m.pqRatchet = pqMsg3Bytes) &&
    decide (m.counter = 0) &&
    decide (m.previousCounter = 0) &&
    decide (m.messageVersion = 4)
  | .error _ => false

theorem checkWhisper4M2_eq : checkWhisper4M2 = true := by
  decide +kernel

def ev4Variation : DY.TrWire.EncodingVariation :=
  { versionLowNibble := 15
    ratchetKeyTrailingBytes := []
    counterHigh := 0
    previousCounterHigh := 0
    fields := [.extra 2 (.varint 42) 0 0, .extra 15 (.varint 1) 0 0,
      .known 1 0 0, .known 2 0 0, .known 3 0 0, .known 4 0 0, .known 5 0 0] }

theorem trWireBytes_ev4Variation_eq :
    DY.Libsignal.Composed.Refinement.trWireBytes [] ev4Variation
      (WireFields.ofBytes [4#8] (compPubOfIdx 5) [0, 0, 0, 0] [0, 0, 0, 0] ct3M2Bytes)
      pqMsg3Bytes = wire4M2Bytes := by
  decide +kernel

theorem trWireBytes_m1_eq :
    DY.Libsignal.Composed.Refinement.trWireBytes addr1Bytes DY.TrWire.canonicalVariation
      (WireFields.ofBytes [4#8] (compPubOfIdx 4) [0, 0, 0, 0] [0, 0, 0, 0] ct1M1Bytes)
      pqMsg1Bytes = wire1M1Bytes := by
  decide +kernel

theorem trWireBytes_m2_1_eq :
    DY.Libsignal.Composed.Refinement.trWireBytes addr1Bytes DY.TrWire.canonicalVariation
      (WireFields.ofBytes [4#8] (compPubOfIdx 4) [0, 0, 0, 0] [0, 0, 0, 0] ct1M2Bytes)
      pqMsg1Bytes = wire1M2Bytes := by
  decide +kernel

theorem trWireBytes_m2_3_eq :
    DY.Libsignal.Composed.Refinement.trWireBytes [] DY.TrWire.canonicalVariation
      (WireFields.ofBytes [4#8] (compPubOfIdx 5) [0, 0, 0, 0] [0, 0, 0, 0] ct3M2Bytes)
      pqMsg3Bytes = wire3M2Bytes := by
  decide +kernel

theorem addr1_eq_serialized :
    addr1Bytes = serializeAddresses ⟨aliceUuid, 1⟩ ⟨bobUuid, 1⟩ := by
  decide +kernel

theorem bun0_props :
    bun0Bytes.length = DY.Libsignal.PQXDH.Refinement.preKeyBundleByteLength ∧
    bun0Bytes[4]? = some 0#8 ∧
    bundlePreKeyIds bun0Bytes = (none, 7#32, 9#32) ∧
    slice bun0Bytes 46 33 = ecKey (compPubOfIdx 2) ∧
    slice bun0Bytes 79 64 = setup7003.spkSig ∧
    slice bun0Bytes 147 1569 = kyberKey setup7003.kyberPk ∧
    slice bun0Bytes 1716 64 = setup7003.kyberPkSig ∧
    slice bun0Bytes 1780 33 = ecKey (compPubOfIdx 1) := by
  decide +kernel

theorem coins_secret_indices :
    coins0Bytes.length = 192 ∧
    coins0Bytes.take 32 = ek0Bytes ∧
    (List.ofFn fun j : Fin 32 => coins0Bytes.getD (32 + 4 * j.1) 0) = ent0Bytes ∧
    (coins0Bytes.drop 160).take 32 = dhsA0Bytes ∧
    compSecretIdx (clamp setup7003.aliceId) = some 0 ∧
    compSecretIdx (clamp setup7003.bobId) = some 1 ∧
    compSecretIdx (clamp setup7003.spk) = some 2 ∧
    compSecretIdx (clamp ek0Bytes) = some 3 ∧
    compSecretIdx (clamp dhsA0Bytes) = some 4 ∧
    compSecretIdx (clamp coins2Bytes) = some 5 ∧
    compKyberEncaps ent0Bytes = kyberCt0Bytes ++ kyberSs0Bytes ∧
    compKyberDecaps kyberCt0Bytes = kyberSs0Bytes := by
  decide +kernel

theorem pt_noncollision_facts :
    8 < pt1M1Bytes.length ∧ pt1M1Bytes.length % 16 ≠ 0 ∧ (0x74#8 ∈ pt1M1Bytes) ∧
    !(coins0Bytes.contains 0x74#8) ∧
    8 < pt1M2Bytes.length ∧ pt1M2Bytes.length % 16 ≠ 0 ∧ (0x74#8 ∈ pt1M2Bytes) ∧
    8 < pt3M2Bytes.length ∧ pt3M2Bytes.length % 16 ≠ 0 ∧ (0x74#8 ∈ pt3M2Bytes) ∧
    !(coins1Bytes.contains 0x74#8) ∧
    !(coins2Bytes.contains 0x74#8) := by
  decide +kernel

theorem ofByteArray_info_labels :
    ofByteArray "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024".toUTF8 = infoPqxdhBytes ∧
    ofByteArray "WhisperRatchet".toUTF8 = infoRatchetBytes ∧
    ofByteArray "WhisperMessageKeys".toUTF8 = infoMessageKeysBytes := by
  simp only [String.toUTF8_eq_toByteArray]
  decide

theorem pqxdh_and_mac_facts_7003 :
    hmacWith F7 (List.replicate 32 0#8)
      (List.replicate 32 0xff#8 ++ compDhByIdx 2 0 ++ compDhByIdx 1 3 ++ compDhByIdx 2 3 ++ kyberSs0Bytes) = prkPqxdhBytes ∧
    hmacWith F7 prkPqxdhBytes (infoPqxdhBytes ++ [0x01#8]) = rk0Bytes ∧
    hmacWith F7 prkPqxdhBytes (rk0Bytes ++ infoPqxdhBytes ++ [0x02#8]) = ck0Bytes ∧
    hmacWith F7 prkPqxdhBytes (ck0Bytes ++ infoPqxdhBytes ++ [0x03#8]) = pqrBytes ∧
    macIn1M1Bytes = ecKey (compPubOfIdx 0) ++ ecKey (compPubOfIdx 1) ++ wire1M1Bytes ∧
    (hmacWith F7 macKey1Bytes macIn1M1Bytes).take 8 = mac1M1Bytes ∧
    (hmacWith F7 macKey1Bytes macIn1M1Bytes).take 4 ≠ compTag4 ∧
    macIn1M2Bytes = ecKey (compPubOfIdx 0) ++ ecKey (compPubOfIdx 1) ++ wire1M2Bytes ∧
    (hmacWith F7 macKey1Bytes macIn1M2Bytes).take 8 = mac1M2Bytes ∧
    (hmacWith F7 macKey1Bytes macIn1M2Bytes).take 4 ≠ compTag4 ∧
    macIn3M2Bytes = ecKey (compPubOfIdx 1) ++ ecKey (compPubOfIdx 0) ++ wire3M2Bytes ∧
    macIn3M2Bytes.length = 146 ∧
    (hmacWith F7 macKey3Bytes macIn3M2Bytes).take 8 = mac3M2Bytes ∧
    (hmacWith F7 macKey3Bytes macIn3M2Bytes).take 4 ≠ compTag4 := by
  decide +kernel

theorem ratchet_a_facts_7003 :
    hmacWith F7 prkMsg1Bytes (infoMessageKeysBytes ++ [0x01#8]) = encKey1Bytes ∧
    hmacWith F7 prkMsg1Bytes (encKey1Bytes ++ infoMessageKeysBytes ++ [0x02#8]) = macKey1Bytes ∧
    (hmacWith F7 prkMsg1Bytes (encKey1Bytes ++ infoMessageKeysBytes ++ [0x02#8])).take 4 ≠ compTag4 ∧
    hmacWith F7 prkMsg1Bytes (macKey1Bytes ++ infoMessageKeysBytes ++ [0x03#8]) = ivBlock1Bytes ∧
    ivBlock1Bytes.take 16 = iv1Bytes ∧
    hmacWith F7 salt1Bytes seedA0Bytes = prkMsg1Bytes ∧
    (hmacWith F7 salt1Bytes seedA0Bytes).take 4 ≠ compTag4 ∧
    hmacWith F7 cksA0Bytes [0x01#8] = seedA0Bytes ∧
    (hmacWith F7 cksA0Bytes [0x01#8]).take 4 ≠ compTag4 ∧
    hmacWith F7 cksA0Bytes [0x02#8] = cksA1Bytes ∧
    hmacWith F7 prkA1Bytes (infoRatchetBytes ++ [0x01#8]) = rk1Bytes ∧
    hmacWith F7 prkA1Bytes (rk1Bytes ++ infoRatchetBytes ++ [0x02#8]) = cksA0Bytes ∧
    (hmacWith F7 prkA1Bytes (rk1Bytes ++ infoRatchetBytes ++ [0x02#8])).take 4 ≠ compTag4 ∧
    hmacWith F7 rk0Bytes (compDhByIdx 2 4) = prkA1Bytes ∧
    (hmacWith F7 rk0Bytes (compDhByIdx 2 4)).take 4 ≠ compTag4 := by
  decide +kernel

theorem ratchet_b_and_aes_facts_7003 :
    hmacWith F7 rk1Bytes (compDhByIdx 4 5) = prkB1Bytes ∧
    hmacWith F7 prkB1Bytes (infoRatchetBytes ++ [0x01#8]) = rk2Bytes ∧
    hmacWith F7 prkB1Bytes (rk2Bytes ++ infoRatchetBytes ++ [0x02#8]) = cksB0Bytes ∧
    hmacWith F7 cksB0Bytes [0x01#8] = seedB0Bytes ∧
    hmacWith F7 cksB0Bytes [0x02#8] = cksB1Bytes ∧
    hmacWith F7 salt3Bytes seedB0Bytes = prkMsg3Bytes ∧
    hmacWith F7 prkMsg3Bytes (infoMessageKeysBytes ++ [0x01#8]) = encKey3Bytes ∧
    hmacWith F7 prkMsg3Bytes (encKey3Bytes ++ infoMessageKeysBytes ++ [0x02#8]) = macKey3Bytes ∧
    hmacWith F7 prkMsg3Bytes (macKey3Bytes ++ infoMessageKeysBytes ++ [0x03#8]) = ivBlock3Bytes ∧
    ivBlock3Bytes.take 16 = iv3Bytes ∧
    compDhByIdx 5 4 ≠ compDhByIdx 2 4 ∧
    compAesPerm encKey1Bytes iv1Bytes pt1M1Bytes = ct1M1Bytes ∧
    compAesPerm encKey1Bytes iv1Bytes pt1M2Bytes = ct1M2Bytes ∧
    compAesPerm encKey3Bytes iv3Bytes pt3M2Bytes = ct3M2Bytes := by
  decide +kernel

end Symbolic.BugInjection.Proofs.SyntheticRecvCommon.TraceEvents7003
