/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Pure -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address
import LibsignalBinary.Proofs.PublicApi.StoreKit.Fs
import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs

/-!
# `memrchr` Hook Discharge for `signal_session::address`

Discharges the `memrchr` extern hypothesis of `address_ok` against `CliRun.memrchrHook`
(`address_ok_a1`) and parametric `CliExternsOk P A ext` (`address_ok_ext`).
-/

public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open Address.Helpers

/-- `CliRun.memrchrHook` satisfies `memrchrSpec stk` for any stack budget `stk`. -/
theorem memrchrHook_ok (stk : Nat) : HookOk memrchrHook (memrchrSpec stk) := by
  intro x R s0 hrun hpre _hsp
  simp only [memrchrSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlt⟩, hmem⟩
  have hlen : (s0.readReg64 .x2).toNat = x.bs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  obtain ⟨hlen_le, hrd⟩ := (IsBlock.pointsToBytes x.p x.bs).read hmem
  have hcan := (IsBlock.pointsToBytes x.p x.bs).canRead hlen_le hmem
  have hmemrchr :
      memrchrHook s0 =
        match memrchrIdx x.c x.bs with
        | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s0
        | none => retHook (fun s => s.writeReg64 .x0 0#64) s0 := by
    unfold memrchrHook memrchrIdx
    simp only [hx0, hx1, hlen, hcan, hrd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hmemrchr]
  cases hidx : memrchrIdx x.c x.bs with
  | some i =>
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    dsimp only [memrchrSpec]
    simp only [hidx, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp only [retHook, arm64_norm],
      by simp only [retHook, arm64_norm],
      ⟨by simp only [retHook, arm64_norm], by simp only [retHook, arm64_norm]⟩⟩, hmem⟩
  | none =>
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    dsimp only [memrchrSpec]
    simp only [hidx, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨by simp only [retHook, arm64_norm],
      by simp only [retHook, arm64_norm],
      by simp only [retHook, arm64_norm]⟩, hmem⟩

private theorem stackAt_split_ext_addr (sp : BitVec 64) {stk : Nat}
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk = memRegion (sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗
      stackAt sp extHookStack := by
  have h1 := stackAt_split_bottom sp extHookStack (stk - extHookStack) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

end CryptoVerification.SignalSession.Cli.MainHops

