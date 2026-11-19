/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsB -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegUntrusted -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Aux
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP2a
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsE
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Bin.Record
import LibsignalBinary.Proofs.E2E.Record.Support.Repr
import LibsignalBinary.Proofs.SessionRecordAt.Stage1X.Defs

/-!
# Stage P2 Matched-Session Remote-Identity Mismatch Tail (`+0x12fc → x30`)

Proves `stageP2_matched_mismatch_tail` (and its `AllocContractsX` + stacked `memcpyRO` generalization
`stageP2_matched_mismatch_tail_x`), unwinding the remote-identity mismatch error path from `+0x12fc`
to `s0.readReg64 .x30` with `apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext)))`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

-- Repeat `-arm64_norm` attributes after importing `GenP3.StageP3Stmt`.
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (entails_replace_sub)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem stack_root_to_strToOwned (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - strToOwnedLocal2Stack) ∗
        stackAt sp strToOwnedLocal2Stack :=
  stackAt_split_of_le sp rootStack strToOwnedLocal2Stack (by decide) hn

theorem memRegion_3e0_368_split_24 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0x3f8#64) 344 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 24 344 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem stack_root_to_cells48 (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - 48) ∗
        cells (sp - 48#64) 6 := by
  rw [stackAt_split_of_le sp rootStack 48 (by decide) hn]
  change _ ∗ memRegion (sp - 48#64) 48 = _
  rw [show (48 : Nat) = 8 * 6 by decide, ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]

theorem coro_398_add_15a (coroPtr : BitVec 64) :
    (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 := by
  bv_omega

theorem stack_root_to_remoteIk (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack)
        (rootStack - CryptoVerification.LibsignalTripleRatchet.Getters.remoteIdentityKeyStack) ∗
        stackAt sp CryptoVerification.LibsignalTripleRatchet.Getters.remoteIdentityKeyStack :=
  stackAt_split_of_le sp rootStack
    CryptoVerification.LibsignalTripleRatchet.Getters.remoteIdentityKeyStack (by decide) hn

theorem stack_root_to_pkSerialize (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - publicKeySerializeStack) ∗
        stackAt sp publicKeySerializeStack :=
  stackAt_split_of_le sp rootStack publicKeySerializeStack (by decide) hn

theorem invalidMessage_prekey_out_entails_3 (A : RustAlloc) (outPtr cap ptr e4 : BitVec 64)
    (bs : List (BitVec 8)) :
    (((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗
     ((outPtr + 0x8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
     ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
     ((outPtr + 0x14#64) ↦₆₄ ((BitVec.ofNat 64 bs.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
     ((outPtr + 0x1c#64) ↦₆₄ ((3#64 : BitVec 64).extractLsb' 0 32 ++ (BitVec.ofNat 64 bs.length).extractLsb' 32 32)) ∗
     ((outPtr + 0x24#64) ↦₆₄ (e4.extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)) ∗
     ((outPtr + 0x2c#64) ↦₃₂ e4.extractLsb' 32 32) ∗
     CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr bs) ⊢
      apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) :=
  invalidMessage_prekey_out_entails A outPtr cap ptr 3#64 e4 bs
    [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] rfl (by decide)

theorem opkPacked_two_mask (w : BitVec 64) :
    ((((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| (w <<< 32)) &&& 0xff#64) =
      ((2#32 : BitVec 32).zeroExtend 64 &&& 0xff#64) := by
  bv_bits

theorem opkPacked_two_lo32 (w : BitVec 64) :
    (((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| (w <<< 32)).extractLsb' 0 32 = 2#32 := by
  bv_bits

theorem coro_250_cells6_eq (coroPtr : BitVec 64) :
    cells (coroPtr + 0x250#64) 6 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        ((coroPtr + 0x250#64) ↦₆₄ u0) ∗ ((coroPtr + 0x258#64) ↦₆₄ u1) ∗
        ((coroPtr + 0x260#64) ↦₆₄ u2) ∗ ((coroPtr + 0x268#64) ↦₆₄ u3) ∗
        ((coroPtr + 0x270#64) ↦₆₄ u4) ∗ ((coroPtr + 0x278#64) ↦₆₄ u5) := by
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem coro_250_6w_entails_cells6 (coroPtr u0 u1 u2 u3 u4 u5 : BitVec 64) :
    ((coroPtr + 0x250#64) ↦₆₄ u0) ∗ ((coroPtr + 0x258#64) ↦₆₄ u1) ∗
    ((coroPtr + 0x260#64) ↦₆₄ u2) ∗ ((coroPtr + 0x268#64) ↦₆₄ u3) ∗
    ((coroPtr + 0x270#64) ↦₆₄ u4) ∗ ((coroPtr + 0x278#64) ↦₆₄ u5) ⊢
      cells (coroPtr + 0x250#64) 6 := by
  rw [coro_250_cells6_eq]
  exact Entails.sepExists_right u0 (Entails.sepExists_right u1
    (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5 (Entails.refl _))))))

theorem w64_3_entails_memRegion24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢
      memRegion a 24 := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
      ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

theorem memRegion_a90_48_split (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 48 ⊢
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        ((sp + 0xa90#64) ↦₆₄ u0) ∗ ((sp + 0xa98#64) ↦₆₄ u1) ∗ ((sp + 0xaa0#64) ↦₆₄ u2) ∗
        ((sp + 0xaa8#64) ↦₆₄ u3) ∗ ((sp + 0xab0#64) ↦₆₄ u4) ∗ ((sp + 0xab8#64) ↦₆₄ u5) := by
  rw [show (48 : Nat) = 8 * 6 by decide, ProofLib.memRegion_cells (sp + 0xa90#64) 6 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  exact Entails.refl _

theorem a90_mismatch_entails_memRegion48 (sp cap ptr len x27 : BitVec 64) :
    ((sp + 0xa90#64) ↦₆₄ 0x8000000000000018#64) ∗
    ((sp + 0xa98#64) ↦₃₂ cap.extractLsb' 0 32) ∗
    ((sp + 0xa9c#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
    ((sp + 0xaa4#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
    ((sp + 0xaac#64) ↦₆₄ ((3#64 : BitVec 64).extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
    ((sp + 0xab4#64) ↦₆₄ (x27.extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)) ∗
    ((sp + 0xabc#64) ↦₃₂ x27.extractLsb' 32 32) ⊢
      memRegion (sp + 0xa90#64) 48 := by
  rw [ProofLib.memRegion_split (sp + 0xa90#64) 8 40 (by decide),
      ProofLib.memRegion_split (sp + 0xa90#64 + 8#64) 4 36 (by decide),
      ProofLib.memRegion_split (sp + 0xa90#64 + 8#64 + 4#64) 8 28 (by decide),
      ProofLib.memRegion_split (sp + 0xa90#64 + 8#64 + 4#64 + 8#64) 8 20 (by decide),
      ProofLib.memRegion_split (sp + 0xa90#64 + 8#64 + 4#64 + 8#64 + 8#64) 8 12 (by decide),
      ProofLib.memRegion_split (sp + 0xa90#64 + 8#64 + 4#64 + 8#64 + 8#64 + 8#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (pointsTo32_entails_memRegion _ _))))))

theorem memRegion_370_36_split (sp : BitVec 64) :
    memRegion (sp + 0x370#64) 36 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 32,
        ((sp + 0x370#64) ↦₆₄ w0) ∗ ((sp + 0x378#64) ↦₆₄ w1) ∗
        ((sp + 0x380#64) ↦₆₄ w2) ∗ ((sp + 0x388#64) ↦₆₄ w3) ∗
        ((sp + 0x390#64) ↦₃₂ w4) := by
  rw [sp370_36_split_eq sp]
  apply Entails.sepExists_elim; intro u20
  apply Entails.sepExists_elim; intro u18
  apply Entails.sepExists_elim; intro u10
  apply Entails.sepExists_elim; intro u8
  apply Entails.sepExists_elim; intro u0
  exact Entails.sepExists_right u0 (Entails.sepExists_right u8
    (Entails.sepExists_right u10 (Entails.sepExists_right u18
      (Entails.sepExists_right u20 (Entails.refl _)))))

theorem vecU8_unpack_3e0_64 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (sp + 0x3e0#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((sp + 0x3e0#64) ↦₆₄ cap) ∗
        ((sp + 0x3e8#64) ↦₆₄ ptr) ∗
        ((sp + 0x3f0#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr bs := by
  unfold vecU8 vecU8At vecHeader
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

theorem SepWPp.drop_ro_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P D F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = D ∗ F)
    (h : SepWPp prog ret s F Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem stack_root_to_strToOwnedX (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack)
        (rootStack - strToOwnedLocal2StackWith extHookStack) ∗
        stackAt sp (strToOwnedLocal2StackWith extHookStack) :=
  stackAt_split_of_le sp rootStack (strToOwnedLocal2StackWith extHookStack) (by decide) hn

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
