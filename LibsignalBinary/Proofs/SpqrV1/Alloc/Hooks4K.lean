/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2 -- proof-setup: allow-public-import
import ProofLib.SepLogic.WP.StateNorm

public section

set_option autoImplicit false

/-!
# 4 KiB Stack Allocator and Memory Contract Bundle (`AllocContracts4K`)

Packages `allocHookStack` (`4096` B) `subroutine_ok` contracts on
`tripleRatchetProgAtExt b ext` for `alloc`, `dealloc`, `realloc`, `shim`, `memcpy`
(including read-only `sessionMemcpyROSpec4K`), `memmove`, and `memset`.
-/

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-- Read-only `memcpy(dst, src, len)` region contract (`src ↦ᵣ bs`) with trace preservation. -/
@[expose] def sessionMemcpyROSpec4K : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length ∧
     bs.length ≤ 2 ^ 64⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ᵣ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs)

theorem hookMemcpy_sessionMemcpyROSpec4K_ok : HookOk hookMemcpy sessionMemcpyROSpec4K := by
  refine retHook_ok fun ⟨dst, src, bs⟩ R s0 _ hpre _ => ?_
  simp only [sessionMemcpyROSpec4K, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hsrc_front : s0.mem ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
  have hread := (IsBlockRO.pointsToBytesRO src bs hlen).read hsrc_front
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only; rw [hx0, hx1, hx2, hread]; exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  · simp only [sessionMemcpyROSpec4K, retHook, State.readReg64_setPC, State.readReg64_setMem,
      hx0, hx1, hx2, hread, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨trivial, rfl⟩, satisfies_writeBytes bs hlen hmem⟩

theorem libcMemcpyRO_of_sessionMemcpyRO4K {prog : Program} {addr : BitVec 64} {stk : Nat}
    (h : subroutine_ok prog addr (withStack sessionMemcpyROSpec4K stk)) :
    subroutine_ok prog addr (libcMemcpyROSpec stk) := by
  refine subroutine_ok_map h ?_
  rintro ⟨dst, src, bs⟩ R s0 hpre
  refine ⟨(dst, src, bs), R, ?_, ?_⟩
  · dsimp only [libcMemcpyROSpec, withStack, sessionMemcpyROSpec4K] at hpre ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hm⟩
    have hle : bs.length ≤ 2 ^ 64 := by rw [← hx2]; exact Nat.le_of_lt (s0.readReg64 .x2).isLt
    exact ⟨⟨hx0, hx1, hx2, hle⟩, hm⟩
  · intro sf hpost
    dsimp only [libcMemcpyROSpec, withStack, sessionMemcpyROSpec4K] at hpost ⊢
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    exact ⟨hpost.1.1, hpost.2⟩

namespace AllocContracts4K

variable {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}

end AllocContracts4K

end CryptoVerification.SpqrV1.Alloc
