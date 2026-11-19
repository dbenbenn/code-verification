/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ConstsMerge -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DoReserve10
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.DecodeVarint5

/-!
# Handshake `bytes::merge [local#6]` Phases 2 and 3

Proves the `X`-stack error and drop epilogues (`+0x074`, `+0x07c`, `+0x254`), Phase 3
(`+0x210..+0x250`, `+0x29c..+0x2bc`: `Vec::clear`, `Vec::reserve`, `memcpy`, and `vtable.drop`),
and Phase 2 (`+0x094..+0x20c`: `BytesMut::with_capacity`, `memcpy`, and `bytes::from_vec`) for
`prost::encoding::bytes::merge::<Vec<u8>, &mut &[u8]> [local#6]` (`888` B).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.VarintBridge
open CryptoVerification.CodeLayout
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp]
  bytesMutDataWord_zero bytesMutDataWord_bit0 bytesMutDataWord_getLsbD_zero
  bytesMutDataWord_getElem_zero bytesMutDataWord_lsr5 bitvec_ult_zero
  bitvec_ult_33bits_of_lt32 bitvec_msb_false_of_lt32 bitvec_getLsbD_63_of_lt32
  Prost.bitvec_ult_self bitvec_sub_self_64 bitvec_if_zero_ult_self

/-! ## 1. Error & Drop Epilogue Lemmas (`+0x074`, `+0x07c`, `+0x254`) -/

private theorem mergePanicX_of_allocFailed {A : RustAlloc} {x : BytesMergeGhost}
    {s0 s_call sf : State} {F R : SepProp} (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (bytesMergeRawSpecX A).onPanic x s0 sf ∗ R := by
  dsimp only [bytesMergeRawSpecX, allocFailedIn] at hm ⊢; rw [htr] at hm; exact allowPanic_frame id hm

private theorem decodeVarintAux_length_lt (i : Nat) (acc : BitVec 64) (bs rest0 : List (BitVec 8)) (len : BitVec 64)
    (h : decodeVarintAux i acc bs = some (len, rest0)) : rest0.length < bs.length := by
  induction bs generalizing i acc with
  | nil => simp [decodeVarintAux] at h
  | cons b bs' ih =>
    unfold decodeVarintAux at h; dsimp only at h; split at h
    · split at h
      · contradiction
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h; simp
    · split at h
      · contradiction
      · have hlt := ih _ _ h; simp; omega

private theorem mergeBytes_length_sum {wt : WireType} {bs v rest : List (BitVec 8)}
    (h : mergeBytes wt bs = some (v, rest)) : 1 + v.length + rest.length ≤ bs.length := by
  cases wt <;> try simp [mergeBytes] at h
  cases hvar : decodeVarint bs with
  | none => simp [hvar] at h
  | some p =>
    rcases p with ⟨len, rest0⟩; rw [hvar] at h; dsimp only at h; split at h
    · contradiction
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have h1 : rest0.length < bs.length := decodeVarintAux_length_lt 0 0 bs rest0 len hvar
      have h2 : (rest0.take len.toNat).length + (rest0.drop len.toNat).length = rest0.length := by
        rw [← List.length_append, List.take_append_drop]
      omega

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH
