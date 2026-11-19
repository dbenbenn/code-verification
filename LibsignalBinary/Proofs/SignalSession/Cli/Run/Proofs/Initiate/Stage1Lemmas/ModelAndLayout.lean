/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.IsCanonical -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Fs
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridge
import ProofLib.SepLogic.WP
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.IdentityVtables
import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import LibsignalBinary.Proofs.E2E.Bin.Record

/-!
# Stage 1 Normalization, Model, Control-Flow, and Vtable Helpers

Provides state/`BitVec` normalization lemmas (`Stage1Norm`), pure `bundleEOf?` and `initDef` model
lemmas, `InInitiate` call/panic combinators, and `.rodata` vtable slot introduction lemmas for
Stage 1 of `signal_session_handshake::initiate`.
-/

public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection open CryptoGames CryptoGames.LibsignalSession
set_option maxRecDepth 2000000
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## State and `BitVec` normalization lemmas -/

namespace Stage1Norm

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem sp_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).sp = s.sp := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases s; cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem fs_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).fs = s.fs := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).symtab = s.symtab := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).symtab = s.symtab := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).symtab = s.symtab := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).symtab = s.symtab := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).symtab = s.symtab := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).symtab = s.symtab := by cases s; cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem symtab_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).symtab = s.symtab := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).trace = s.trace := by cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem trace_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).trace = s.trace := by cases s; cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg64_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg64 r = s.readReg64 r := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg32_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg32 r = s.readReg32 r := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readReg_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128)
    (w : RegWidth) (r : Reg) :
    (s.writeVReg128 idx v).readReg w r = s.readReg w r := by
  cases s; cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (idx : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setMem_pre (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_setPState_pre (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) (idx : BitVec 5) :
    (s.writeReg32 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem readVReg128_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64)
    (idx : BitVec 5) :
    (s.writeReg w r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases w <;> cases r <;> rfl

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append_lo (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_append_hi (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_pack32_0 (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 8 (a ++ b ++ c ++ d) = d := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_pack32_8 (a b c d : BitVec 8) :
    BitVec.extractLsb' 8 8 (a ++ b ++ c ++ d) = c := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_pack32_16 (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 8 (a ++ b ++ c ++ d) = b := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_pack32_24 (a b c d : BitVec 8) :
    BitVec.extractLsb' 24 8 (a ++ b ++ c ++ d) = a := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_pack32_0_16 (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 16 (a ++ b ++ c ++ d) = c ++ d := by
  bv_bits

@[arm64_norm ↓, wp_norm ↓]
theorem extractLsb_pack32_16_16 (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 16 (a ++ b ++ c ++ d) = a ++ b := by
  bv_bits

end Stage1Norm

/-! ## Pure model lemmas (`bundleEOf?`, `initDef`, `signaturesVerify`) -/

@[expose] def mkBundleE (b : BundleV)
    (h1 : b.spkSig.length = 64) (h2 : b.kpkSig.length = 64) (h3 : b.kpk.length = 1568) :
    PreKeyBundleFields :=
  { regId := b.regId
    opk := b.opk.map fun (i, k) => (i, k.bytes)
    spkId := b.spkId
    spkPub := b.spk.bytes
    spkSig := ⟨b.spkSig, h1⟩
    kpkId := b.kpkId
    kpkPub := ⟨b.kpk, h3⟩
    kpkSig := ⟨b.kpkSig, h2⟩
    idPub := b.idKey.publicKey.bytes }

theorem bundleEOf_eq_some_mkBundleE (b : BundleV)
    (h1 : b.spkSig.length = 64) (h2 : b.kpkSig.length = 64) (h3 : b.kpk.length = 1568) :
    bundleEOf? b = some (mkBundleE b h1 h2 h3) := by
  unfold bundleEOf? mkBundleE
  simp only [h1, h2, h3, ↓reduceDIte]

theorem initDef_eq_some_none_of_trust_err (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (F : FsFiles) (peer me : AddrVal) (b : BundleV) (coins : List (BitVec 8))
    (herr : StoresGhost.opened.identity.trusted cliIo.rd F peer b.idKey = .error ()) :
    initDef X W F peer me b coins = some none := by
  unfold initDef
  dsimp only
  cases bundleEOf? b with
  | none => rfl
  | some be => rw [herr]

theorem initDef_eq_some_none_of_trust_false (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (F : FsFiles) (peer me : AddrVal) (b : BundleV) (coins : List (BitVec 8))
    (hf : StoresGhost.opened.identity.trusted cliIo.rd F peer b.idKey = .ok false) :
    initDef X W F peer me b coins = some none := by
  unfold initDef
  dsimp only
  cases bundleEOf? b with
  | none => rfl
  | some be => rw [hf]

theorem initDef_eq_some_none_of_sigsOk_false (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (F : FsFiles) (peer me : AddrVal) (b : BundleV) (be : PreKeyBundleFields) (coins : List (BitVec 8))
    (hbe : bundleEOf? b = some be)
    (hsigs : PreKeyBundleFields.signaturesVerify X W be = false) :
    initDef X W F peer me b coins = some none := by
  unfold initDef
  dsimp only
  rw [hbe]
  cases StoresGhost.opened.identity.trusted cliIo.rd F peer b.idKey with
  | error _ => rfl
  | ok tb =>
    cases tb with
    | false => rfl
    | true =>
      cases StoresGhost.opened.identity.keyPair cliIo.rd F with
      | error _ => rfl
      | ok kp =>
        cases StoresGhost.opened.identity.regId cliIo.rd F with
        | error _ => rfl
        | ok reg =>
          dsimp only
          have hnone :
              initiateState X W (initParty peer) { idPriv := kp.privateKey.bytes, regId := reg } be
                (padCoins coins) = none := by
            unfold initiateState SignalPqxdh.Model.initiateKeys PreKeyBundleFields.signaturesVerify at *
            simp only [initiateInput] at hsigs ⊢
            rw [Bool.and_eq_false_iff] at hsigs
            rcases hsigs with h1 | h2
            · simp [h1]
            · simp [h2]
          rw [hnone]

theorem sigsOk_false_of_spk_false (X : UnreachedPqxdhPrimitives) (W : PEParams) (be : PreKeyBundleFields)
    (hspk : (modelPrims X W).sigVerify (vecU8 be.idPub)
      (SignalPqxdh.encodeEC (vecU8 be.spkPub)) (vecU8 be.spkSig) = false) :
    be.signaturesVerify X W = false := by
  unfold PreKeyBundleFields.signaturesVerify
  dsimp only [initiateInput]
  rw [hspk, Bool.false_and]

theorem sigsOk_false_of_kpk_false (X : UnreachedPqxdhPrimitives) (W : PEParams) (be : PreKeyBundleFields)
    (hkpk : (modelPrims X W).sigVerify (vecU8 be.idPub)
      (SignalPqxdh.encodeKEM (vecU8 be.kpkPub)) (vecU8 be.kpkSig) = false) :
    be.signaturesVerify X W = false := by
  unfold PreKeyBundleFields.signaturesVerify
  dsimp only [initiateInput]
  rw [hkpk, Bool.and_false]

theorem bytesToBv8_vecU8 {n : Nat} (v : List.Vector (BitVec 8) n) :
    Pqxdh.Shared.bytesToBv8 (vecU8 v) = v.toList :=
  CryptoVerification.E2E.Pqxdh.ResponderCore.bytesToBv8_vecU8 v

theorem spkSerialize_eq_encodeEC (b : BundleV) (h1 : b.spkSig.length = 64)
    (h2 : b.kpkSig.length = 64) (h3 : b.kpk.length = 1568) :
    b.spk.serialize =
      Pqxdh.Shared.bytesToBv8 (SignalPqxdh.encodeEC (vecU8 (mkBundleE b h1 h2 h3).spkPub)) := by
  have hv := bytesToBv8_vecU8 b.spk.bytes
  show (5#8 :: b.spk.bytes.toList) =
    5#8 :: Pqxdh.Shared.bytesToBv8 (vecU8 b.spk.bytes)
  rw [hv]

theorem kpkSerialize_eq_encodeKEM (b : BundleV) (h1 : b.spkSig.length = 64)
    (h2 : b.kpkSig.length = 64) (h3 : b.kpk.length = 1568) :
    (8#8 :: b.kpk) =
      Pqxdh.Shared.bytesToBv8 (SignalPqxdh.encodeKEM (vecU8 (mkBundleE b h1 h2 h3).kpkPub)) := by
  have hv := bytesToBv8_vecU8 (⟨b.kpk, h3⟩ : List.Vector (BitVec 8) 1568)
  show (8#8 :: b.kpk) =
    8#8 :: Pqxdh.Shared.bytesToBv8 (vecU8 (⟨b.kpk, h3⟩ : List.Vector (BitVec 8) 1568))
  exact congrArg (8#8 :: ·) hv.symm

/-! ## Control invariant, panic postcondition, and `withFsInv` call combinator -/

theorem false_entails (P : SepProp) : (⌜False⌝ : SepProp) ⊢ P := by
  rw [← sepConj_emp (⌜False⌝ : SepProp)]
  exact Entails.pure_left False.elim

theorem false_sepConj_entails (R Q : SepProp) : ((⌜False⌝ : SepProp) ∗ R) ⊢ Q := by
  rw [pure_false_sepConj]
  exact false_entails Q

theorem pure_sepConj_elim {φ : Prop} {R Q : SepProp} (h : φ → (R ⊢ Q)) :
    (⌜φ⌝ ∗ R) ⊢ Q := by
  by_cases hφ : φ
  · rw [pure_sepConj_of_true hφ]
    exact h hφ
  · rw [show φ = False from propext ⟨fun h0 => hφ h0, False.elim⟩]
    exact false_sepConj_entails R Q

theorem pure_sepConj_intro {φ : Prop} {P Q : SepProp} (hφ : φ) (h : P ⊢ Q) :
    P ⊢ ⌜φ⌝ ∗ Q := by
  rw [pure_sepConj_of_true hφ]
  exact h

theorem sepWPp_ret_of_sepWP {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog ret s P Q oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sf, hsteps, hok | hoom⟩
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_mono_pre {prog : Program} {ret : BitVec 64}
    {s : State} {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hP : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hP) hm) hL

theorem sepWPp_exists_elim {α : Type} {prog : Program} {ret : BitVec 64}
    {s : State} {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a, SepWPp prog ret s (P a) Q Qp oom) :
    SepWPp prog ret s (∃∗ a, P a) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  obtain ⟨a, hma⟩ := hm
  exact h a R hma hL

theorem sepWPp_pure_elim {φ : Prop} {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom :=
  SepWPp.pure_left h

theorem idTrust_always_ok {W : PEParams} {F : FsFiles} {peer me : AddrVal}
    {idKey : IdentityKey} {gr : Except Unit (List (BitVec 8))}
    {p : Except Unit (Option IdentityKey)}
    (hinitOk : InitOk₀ W F peer me)
    (hgr : gr = StoresGhost.opened.identity.peers.get cliIo.rd F peer.name)
    (hp : IdPeerAns gr p) :
    ∃ tb : Bool,
      idTrustOf p idKey = .ok tb ∧
      StoresGhost.opened.identity.trusted cliIo.rd F peer idKey = .ok tb := by
  obtain ⟨bs, hget, _⟩ := hinitOk.idGet
  have htr := IdGhost.trusted_of_peerAns (k := idKey) (hgr ▸ hp)
  rw [hget] at hgr
  subst hgr
  cases bs with
  | nil =>
    cases hp
    exact ⟨true, rfl, htr⟩
  | cons b rest =>
    obtain ⟨k, rfl, _⟩ := hp
    exact ⟨decide (k = idKey), rfl, htr⟩

/-! ## Read-only vtable slot introduction lemmas -/

theorem sepWPp_with_rodata {prog : Program} {tgt : BitVec 64} {s : State}
    {cell P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hro : ∀ R, (s.mem ⊨ R) → (s.mem ⊨ cell ∗ R))
    (hnext : SepWPp prog tgt s (cell ∗ P) Q Qp oom) :
    SepWPp prog tgt s P Q Qp oom := by
  intro R hm hL
  exact hnext R (by rw [sepConj_assoc]; exact hro (P ∗ R) hm) hL

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage1Lemmas
