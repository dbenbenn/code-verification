/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostDefs

/-!
# Stage P2 Substage P2.4 Helpers, `None` Branch, and Post-Drop Tail

Provides `PreKeyRecord` layout helpers and proves `stageP2_sub4_none_kits` (`opkId? = none`,
`+0x0d5c → +0x36ac`) and the post-`futDrop` tail `stageP2_sub4_some_tail_kits` (`+0x0e40 →
+0x36ac`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Shared
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_memRegion_65_pkPoll_split_eq (out : BitVec 64) :
    memRegion out 65 =
      memRegion out 56 ∗ (∃∗ u_38 : BitVec 64, (out + 0x38#64) ↦₆₄ u_38) ∗
        memRegion (out + 0x40#64) 1 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 56) (k := 9) (b' := out + 0x38#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x38#64) (n := 8) (k := 1) (b' := out + 0x40#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (out + 0x38#64)]

theorem p2_preKeyRecordAt_unpack (A : RustAlloc) (out u_38 : BitVec 64)
    (r : PreKeyRecord) :
    preKeyRecordAt A out r ∗ ((out + 0x38#64) ↦₆₄ u_38) ⊢
      ∃∗ pubCap : BitVec 64, ∃∗ pubPtr : BitVec 64,
      ∃∗ privCap : BitVec 64, ∃∗ privPtr : BitVec 64,
      ∃∗ pad32 : BitVec 32,
        preKeyRecordOut64At out
          pubCap pubPtr (BitVec.ofNat 64 r.preKey.publicKey.length)
          privCap privPtr (BitVec.ofNat 64 r.preKey.privateKey.length)
          (pad32 ++ r.preKey.id) u_38 ∗
        vecU8Buf A pubCap pubPtr r.preKey.publicKey ∗
        vecU8Buf A privCap privPtr r.preKey.privateKey := by
  unfold preKeyRecordAt RustHeap.vecU8
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun privCap => Entails.sepExists_elim fun privPtr =>
    Entails.sepExists_elim fun pubCap => Entails.sepExists_elim fun pubPtr => ?_
  rw [ProofLib.memRegion_four (out + 0x34#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun pad32 => ?_
  refine Entails.sepExists_right pubCap (Entails.sepExists_right pubPtr
    (Entails.sepExists_right privCap (Entails.sepExists_right privPtr
    (Entails.sepExists_right pad32 ?_))))
  rw [LibsignalTripleRatchet.Wire.vecU8At_eq_header_buf,
      LibsignalTripleRatchet.Wire.vecU8At_eq_header_buf]
  dsimp only [vecHeader, preKeyRecordOut64At]
  have hp30 : ((out + 0x30#64) ↦₃₂ r.preKey.id) ∗ ((out + 0x34#64) ↦₃₂ pad32) =
      ((out + 0x30#64) ↦₆₄ (pad32 ++ r.preKey.id)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (out + 0x30#64) r.preKey.id pad32
  rw [hp30]
  sep_norm
  exact Entails.of_eq (by ac_rfl)

theorem p2_pkKeyPairStack_le_pure : 176 ≤ stageP2PureAndErrStack :=
  p2_kp176_le_pure

theorem p2_memRegion_56_split_7words (p : BitVec 64) :
    memRegion p 56 =
      (∃∗ r6 : BitVec 64, ∃∗ r5 : BitVec 64, ∃∗ r4 : BitVec 64,
       ∃∗ r3 : BitVec 64, ∃∗ r2 : BitVec 64, ∃∗ r1 : BitVec 64,
       ∃∗ r0 : BitVec 64,
        (p ↦₆₄ r0) ∗ ((p + 0x08#64) ↦₆₄ r1) ∗ ((p + 0x10#64) ↦₆₄ r2) ∗
        ((p + 0x18#64) ↦₆₄ r3) ∗ ((p + 0x20#64) ↦₆₄ r4) ∗
        ((p + 0x28#64) ↦₆₄ r5) ∗ ((p + 0x30#64) ↦₆₄ r6)) := by
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 48) (b' := p + 0x08#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x08#64) (n := 8) (k := 40) (b' := p + 0x10#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x10#64) (n := 8) (k := 32) (b' := p + 0x18#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x18#64) (n := 8) (k := 24) (b' := p + 0x20#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x20#64) (n := 8) (k := 16) (b' := p + 0x28#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x28#64) (n := 8) (k := 8) (b' := p + 0x30#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight p,
      ProofLib.memRegion_eight (p + 0x08#64),
      ProofLib.memRegion_eight (p + 0x10#64),
      ProofLib.memRegion_eight (p + 0x18#64),
      ProofLib.memRegion_eight (p + 0x20#64),
      ProofLib.memRegion_eight (p + 0x28#64),
      ProofLib.memRegion_eight (p + 0x30#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem p2_memRegion_9_sp270_eq (sp : BitVec 64) :
    memRegion (sp + 0x270#64) 9 =
      (∃∗ b_278 : BitVec 8, ∃∗ u_270 : BitVec 64,
        ((sp + 0x270#64) ↦₆₄ u_270) ∗ ((sp + 0x278#64) ↦₈ b_278)) := by
  rw [ProofLib.memRegion_split' (b := sp + 0x270#64) (n := 8) (k := 1)
        (b' := sp + 0x278#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 0x270#64),
      ProofLib.memRegion_one (sp + 0x278#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem p2_sp270_9_entails_memRegion (sp u_270 : BitVec 64) (b_278 : BitVec 8) :
    ((sp + 0x270#64) ↦₆₄ u_270) ∗ ((sp + 0x278#64) ↦₈ b_278) ⊢
      memRegion (sp + 0x270#64) 9 := by
  rw [ProofLib.memRegion_split' (b := sp + 0x270#64) (n := 8) (k := 1)
        (b' := sp + 0x278#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo8_entails_memRegion _ _)

theorem p2_preKeyRecordOut64_65_entails_memRegion (out w0 w1 w2 w3 w4 w5 w6 w7 : BitVec 64) :
    preKeyRecordOut64At out w0 w1 w2 w3 w4 w5 w6 w7 ∗ memRegion (out + 0x40#64) 1 ⊢
      memRegion out 65 := by
  rw [ProofLib.memRegion_split' (b := out) (n := 64) (k := 1)
        (b' := out + 0x40#64) rfl (by bv_omega) (by decide)]
  refine sepConj_mono_left ?_
  dsimp only [preKeyRecordOut64At]
  rw [ProofLib.memRegion_split' (b := out) (n := 8) (k := 56) (b' := out + 0x08#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x08#64) (n := 8) (k := 48) (b' := out + 0x10#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x10#64) (n := 8) (k := 40) (b' := out + 0x18#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x18#64) (n := 8) (k := 32) (b' := out + 0x20#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 24) (b' := out + 0x28#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x28#64) (n := 8) (k := 16) (b' := out + 0x30#64)
        rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := out + 0x30#64) (n := 8) (k := 8) (b' := out + 0x38#64)
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (pointsTo64_entails_memRegion _ _)))))))

theorem p2_ro_intro_sepWPp {prog : Program} {ret : BitVec 64} {s : State}
    {Ro P : SepProp} {Q Qp : State → SepProp → Prop}
    (hro : ∀ {Q0 : SepProp}, s.mem ⊨ Q0 → s.mem ⊨ Ro ∗ Q0)
    (h : SepWPp prog ret s (Ro ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc]
  exact hro hm

theorem p2_sub4_drop_sep_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P Drop Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = Drop ∗ Rest) (h : SepWPp prog ret s Rest Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem p2_words7_entails_memRegion_56 (p r0 r1 r2 r3 r4 r5 r6 : BitVec 64) :
    (p ↦₆₄ r0) ∗ ((p + 0x08#64) ↦₆₄ r1) ∗ ((p + 0x10#64) ↦₆₄ r2) ∗
    ((p + 0x18#64) ↦₆₄ r3) ∗ ((p + 0x20#64) ↦₆₄ r4) ∗
    ((p + 0x28#64) ↦₆₄ r5) ∗ ((p + 0x30#64) ↦₆₄ r6) ⊢
      memRegion p 56 := by
  rw [p2_memRegion_56_split_7words p]
  exact Entails.sepExists_right r6 (Entails.sepExists_right r5
    (Entails.sepExists_right r4 (Entails.sepExists_right r3
    (Entails.sepExists_right r2 (Entails.sepExists_right r1
    (Entails.sepExists_right r0 (Entails.refl _)))))))

theorem p2_cap_ne_neg3_of_lt {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    cap ≠ 0xfffffffffffffffd#64 :=
  fun hc => by subst hc; norm_num at hlt

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
