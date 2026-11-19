/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.CoinsFill -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Collapse
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.DhHelpers
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.EarlyExit
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage3Lemmas.Model
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23

/-!
# Stage 3 KEM Seed Unroll Helpers

Reusable 4-byte `signal_session_coins_fill(fsp + 0x1600, 4)` draw helpers (`coinWord`,
`s3_coins_fill4`, `s3_draw_to_slot`) shared across `KemCoinsA`, `KemCoinsB`, and `KemCoinsC`.
-/

public section

set_option autoImplicit false
set_option warningAsError false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.CodeLayout
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_hi56_3 and_ff_hi56_3 and_ff32_hi56_3 zext64_trunc32_hi56_3_and_ff

@[expose] def dhPrefix (dh1 dh2 dh3 : SignalPqxdh.Bytes) (dh4? : Option SignalPqxdh.Bytes) : SignalPqxdh.Bytes :=
  match dh4? with
  | none => F_X25519 ++ dh1 ++ dh2 ++ dh3
  | some dh4 => F_X25519 ++ dh1 ++ dh2 ++ dh3 ++ dh4

@[expose] def dhRemAt (secretsPtr : BitVec 64) (dh4? : Option SignalPqxdh.Bytes) : SepProp :=
  match dh4? with
  | none => memRegion (secretsPtr + 128#64) 32 ∗ memRegion (secretsPtr + 160#64) 32
  | some _ => memRegion (secretsPtr + 160#64) 32

@[expose] def dhLenWord (dh4? : Option SignalPqxdh.Bytes) : BitVec 64 :=
  match dh4? with
  | none => 128#64
  | some _ => 160#64

theorem sepWPp_oom_jmp {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {Qoom : State → SepProp}
    (h : SepWP prog mid s emp
      (fun s' q => q = emp ∧ s'.pc = mid ∧ s'.status = .Running ∧ s'.trace = s.trace))
    (hoom : ∀ s' : State, s'.pc = mid → s'.status = .Running → s'.trace = s.trace →
      SepWPp prog ret s' P Q Qp Qoom) : SepWPp prog ret s P Q Qp Qoom := fun R hm hL => by
  rcases h.elim (by rwa [emp_sepConj] : s.mem ⊨ emp ∗ (P ∗ R)) hL with
    ⟨s', hst, ⟨-, -, _, hq, rfl, hpc', hrun', htr'⟩ | ⟨_, hf⟩⟩
  · rw [emp_sepConj] at hq
    obtain ⟨sf, hst', hout⟩ := hoom s' hpc' hrun' htr' R hq (hst.codeLoaded hL)
    exact ⟨sf, hst.trans hst', hout⟩
  · exact (not_satisfies_false_sepConj hf).elim

theorem cells4_to_memRegion32 (p w0 w1 w2 w3 : BitVec 64) :
    (p ↦₆₄ w0) ∗ ((p + 8#64) ↦₆₄ w1) ∗ ((p + 16#64) ↦₆₄ w2) ∗ ((p + 24#64) ↦₆₄ w3) ⊢
      memRegion p 32 := by
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _)))) ?_
  rw [memRegion_merge_at (p + 16#64) 8 8 (p + 24#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (p + 8#64) 8 16 (p + 16#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at p 8 24 (p + 8#64) (by clear * -; bv_omega) (by decide)]
  exact Entails.refl _

theorem buildSecrets_take32_eq (dh1 dh2 dh3 : SignalPqxdh.Bytes) (dh4? : Option SignalPqxdh.Bytes)
    (kemSs : SignalPqxdh.Bytes) :
    (buildSecrets dh1 dh2 dh3 dh4? kemSs).take 32 = F_X25519 := by
  cases dh4? <;>
    simp [buildSecrets, F_X25519, List.append_assoc, List.take_append_of_le_length]

theorem tail_locals_collapse (fsp : BitVec 64) {ekASk kpk : List (BitVec 8)}
    (hek : ekASk.length = 32) (hkpk : kpk.length = 1568)
    (secretsPtr lenWord : BitVec 64) :
    memRegion (fsp + 0x994#64) 12 ∗ ((fsp + 0x9a0#64) ↦ₛ ekASk) ∗
      ((fsp + 0x9c0#64) ↦ₛ kpk) ∗ memRegion (fsp + 0xfe0#64) 0xc80 ∗
      ((fsp + 0x1c60#64) ↦₆₄ 192#64) ∗ ((fsp + 0x1c68#64) ↦₆₄ secretsPtr) ∗
      ((fsp + 0x1c70#64) ↦₆₄ lenWord) ∗ memRegion (fsp + 0x1c78#64) 0x18 ⊢
      memRegion (fsp + 0x994#64) (initLocalsSize - 0x994) := by
  refine Entails.trans
    (sepConj_mono (Entails.refl _)
      (sepConj_mono (pointsToBytes_entails_memRegion_len hek)
        (sepConj_mono (pointsToBytes_entails_memRegion_len hkpk)
          (sepConj_mono (Entails.refl _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                  (Entails.refl _)))))))) ?_
  rw [memRegion_merge_at (fsp + 0x1c70#64) 8 0x18 (fsp + 0x1c78#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x1c68#64) 8 0x20 (fsp + 0x1c70#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x1c60#64) 8 0x28 (fsp + 0x1c68#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (fsp + 0xfe0#64) 0xc80 0x30 (fsp + 0x1c60#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x9c0#64) 1568 0xcb0 (fsp + 0xfe0#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x9a0#64) 32 0x12d0 (fsp + 0x9c0#64) (by clear * -; bv_omega) (by decide),
      memRegion_merge_at (fsp + 0x994#64) 12 0x12f0 (fsp + 0x9a0#64) (by clear * -; bv_omega) (by decide)]
  exact Entails.refl _

@[simp] theorem setWidth64_trunc32 (v : BitVec 32) :
    (v.setWidth 64).truncate 32 = v := by bv_omega

@[simp] theorem extract31_setWidth64 (v : BitVec 32) :
    (v.setWidth 64).extractLsb' 0 32 = v := by
  ext i hi; simp [BitVec.getElem_extractLsb', BitVec.getElem_setWidth, hi,
    Nat.lt_trans hi (by decide : 32 < 64)]

@[simp] theorem setWidth64_trunc8 (v : BitVec 32) :
    (v.setWidth 64).truncate 8 = v.truncate 8 := by bv_omega

@[simp] theorem extract7_setWidth64 (v : BitVec 32) :
    (v.setWidth 64).extractLsb' 0 8 = v.truncate 8 := by
  ext i hi; simp [BitVec.truncate_eq_setWidth, BitVec.getElem_extractLsb', BitVec.getElem_setWidth,
    hi, Nat.lt_trans hi (by decide : 8 < 64)]

@[expose] def coinWord (t : List.Vector (BitVec 8) initiateTapeLen) (i : Nat) (hi : i < 32) : BitVec 32 :=
  t.get ⟨32 + 4 * i + 3, by unfold initiateTapeLen; omega⟩ ++
    t.get ⟨32 + 4 * i + 2, by unfold initiateTapeLen; omega⟩ ++
    t.get ⟨32 + 4 * i + 1, by unfold initiateTapeLen; omega⟩ ++
    t.get ⟨32 + 4 * i, by unfold initiateTapeLen; omega⟩

theorem coinDraw4_eq_pointsTo32 (a : BitVec 64)
    (t : List.Vector (BitVec 8) initiateTapeLen) (i : Nat) (hi : i < 32) :
    (a ↦ₛ (t.toList.drop (32 + 4 * i)).take 4) = (a ↦₃₂ coinWord t i hi) := by
  rw [drop_take_four_of_vec192 t i hi, ProofLib.pointsToBytes4_eq_pointsTo32, coinWord]

theorem coinWord_truncate8 (t : List.Vector (BitVec 8) initiateTapeLen) (i : Nat) (hi : i < 32) :
    (coinWord t i hi).truncate 8 = (initiateKemCoins t).get ⟨i, hi⟩ := by
  rw [coinWord, truncate8_pack4, initiateKemCoins, List.Vector.get_ofFn]

theorem pack_cells4_append (a off0 off1 off2 off3 : BitVec 64)
    (pre ssBytes full : SignalPqxdh.Bytes) (w0 w1 w2 w3 : BitVec 64)
    (hfold : ((a + off0) ↦₆₄ w0) ∗ ((a + off1) ↦₆₄ w1) ∗
      ((a + off2) ↦₆₄ w2) ∗ ((a + off3) ↦₆₄ w3) =
      ((a + off0) ↦ₛ bytesToBv8 ssBytes))
    (happ : (a ↦ₛ bytesToBv8 pre) ∗ ((a + off0) ↦ₛ bytesToBv8 ssBytes) =
      (a ↦ₛ bytesToBv8 full))
    (R : SepProp) :
    (a ↦ₛ bytesToBv8 pre) ∗
      ((a + off0) ↦₆₄ w0) ∗ ((a + off1) ↦₆₄ w1) ∗
      ((a + off2) ↦₆₄ w2) ∗ ((a + off3) ↦₆₄ w3) ∗ R =
      (a ↦ₛ bytesToBv8 full) ∗ R := by
  rw [← hfold] at happ
  simp only [← happ, sepConj_assoc]

theorem repack_pqxdh_stk (pool s1 s2 s3 s4 s5 s6 m rest : SepProp)
    (h : s6 ∗ s1 = m) :
    pool ∗ s1 ∗ s2 ∗ s3 ∗ s4 ∗ s5 ∗ s6 ∗ rest =
      pool ∗ m ∗ s2 ∗ s3 ∗ s4 ∗ s5 ∗ rest := by
  rw [← h]; ac_rfl

theorem allOnes64_4_hex_eq_F_X25519 (a : BitVec 64) :
    (a ↦₆₄ 0xffffffffffffffff#64) ∗ ((a + 8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      ((a + 16#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((a + 24#64) ↦₆₄ 0xffffffffffffffff#64) =
      (a ↦ₛ bytesToBv8 F_X25519) :=
  allOnes64_4_eq_F_X25519 a

namespace Ext

end Ext

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage3Lemmas
