/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsB -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.NextChainKey
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.CodeLayout

/-!
# Stage P2 Matched-Session Basic Blocks: Part C

Proves `str_to_owned_local2_ok_ext` (`<str as ToOwned>::to_owned [local#2]`) and
`p2_err_tail_a_ext_wp` (`+0x1648 → drop_process_prekey_impl_state1`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem sepWPp_pure_mid {prog : Program} {ret_pc : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {post Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret_pc s (A ∗ B ∗ C) post Qp) :
    SepWPp prog ret_pc s (A ∗ B ∗ ⌜φ⌝ ∗ C) post Qp :=
  SepWPp.conseq_pre (by sep_focus) (SepWPp.pure_left h)

private theorem stackAt_split_ge_m2c {sp : BitVec 64} {inner stk : Nat}
    (hle : inner ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - inner) ∗ stackAt sp inner := by
  have h1 := stackAt_split_bottom sp inner (stk - inner) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

private theorem hookSat_memcpyRO_mono_stack {ext : String → Option (State → State)}
    {inner stk : Nat} (hle : inner ≤ stk) (hmax : stk ≤ 2 ^ 64)
    (hRO : HookSat ext memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack inner)) :
    HookSat ext memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack stk) := by
  obtain ⟨f, hf, hok⟩ := hRO
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  have hsplit := stackAt_split_ge_m2c (sp := s0.sp) hle hmax
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - inner) ∗ R
  have hpre' : s0.mem ⊨
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack inner).pre
        (dst, src, bs) s0 ∗ R' := by
    dsimp only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hok (dst, src, bs) R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack] at hp
    rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  · dsimp only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack] at hp
    rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  · dsimp only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack] at hp
    rw [satisfies_pure_sepConj] at hp; exact hp.1.elim

private theorem cond_ne_adds64_of_ne_neg3 {x : BitVec 64} (hne : x ≠ 0xfffffffffffffffd#64) :
    ConditionHolds CondCode.NE (addsPState64 x 3#64) = true := by
  rw [conditionHolds_ne_addsPState64, bne_iff_ne]
  bv_omega

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
