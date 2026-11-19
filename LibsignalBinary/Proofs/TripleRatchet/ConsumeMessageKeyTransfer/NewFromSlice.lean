/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hmac.Defs
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import ProofLib.SepLogic.Entry

/-!
# `Hmac<Sha256>::new_from_slice` on `[LibsignalPlacement]`

Proves relocatable `[LibsignalPlacement]` contracts (`new_from_slice_placed_ro_ok`,
`new_from_slice_placed_ok_withLsCodeLoaded_ro`) for
`<hmac::Hmac<sha2::Sha256> as crypto_common::KeyInit>::new_from_slice` on Block `114` by
repackaging the 152-byte `Result::Ok` buffer as `(ret ↦₆₄ 0) ∗ hmacCoreAt F (ret + 8) key []`.
-/

public section

namespace CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr

/-! ## Layout Equivalence -/

theorem hmacInnerInit_eq (F : ShaCompress) (key : List (BitVec 8)) :
    hmacInnerInit F key = LibsignalSession.CryptoHmacSha256.innerState F key := rfl

theorem hmacOuterInit_eq (F : ShaCompress) (key : List (BitVec 8)) :
    hmacOuterInit F key = LibsignalSession.CryptoHmacSha256.outerState F key := rfl

/-- A fresh `Hmac<Sha256>` at `a` is a 144-byte (`0x90`) block matching `HmacSt _ a F key []`. -/
theorem isBlock_hmacCoreAt_nil (F : ShaCompress) (a : BitVec 64) (key : List (BitVec 8)) :
    IsBlock (hmacCoreAt F a key []) a 0x90
      (fun m => LibsignalSession.CryptoHmacSha256.HmacSt m a F key []) := by
  have hlen := LibsignalSession.CryptoHmacSha256.shaStateBytes_length
  have b88 := IsBlock.pointsTo64 (a + 0x88#64) 1#64
  have b68 := (IsBlock.pointsToBytes_len (a := a + 0x68#64)
    (hlen (hmacOuterInit F key))).sepConj b88 (by bv_arith) (by decide)
  have b60 := (IsBlock.pointsTo64 (a + 0x60#64) (BitVec.ofNat 64 1)).sepConj b68
    (by bv_arith) (by decide)
  have b40 := (IsBlock.pointsToBytes_len (a := a + 0x40#64)
    (hlen (hmacInnerInit F key))).sepConj b60 (by bv_arith) (by decide)
  have b3f := (IsBlock.pointsTo8 (a + 0x3f#64) (BitVec.ofNat 8 0)).sepConj b40
    (by bv_arith) (by decide)
  have bpad := (IsBlock.memRegion (a + BitVec.ofNat 64 0) 63).sepConj b3f
    (by bv_arith) (by decide)
  have bnil := (IsBlock.pointsToBytes a []).sepConj bpad (by simp) (by decide)
  have b := IsBlock.pure_sepConj (φ := ([] : List (BitVec 8)).length < 64) fun _ => bnil
  refine b.cast rfl fun m => ?_
  simp [LibsignalSession.CryptoHmacSha256.HmacSt, hlen, hmacInnerInit_eq, hmacOuterInit_eq]

/-- The `Result::Ok` sret: discriminant `0` at `ret`, then the fresh `Hmac<Sha256>` at `ret + 8`. -/
theorem isBlock_nfsResult (F : ShaCompress) (ret : BitVec 64) (key : List (BitVec 8)) :
    IsBlock ((ret ↦₆₄ 0#64) ∗ hmacCoreAt F (ret + 8#64) key []) ret 0x98
      (fun m => m.read64 ret = 0#64 ∧
        LibsignalSession.CryptoHmacSha256.HmacSt m (ret + 8#64) F key []) :=
  (IsBlock.pointsTo64 ret 0#64).sepConj (isBlock_hmacCoreAt_nil F (ret + 8#64) key) rfl
    (by decide)

/-! ## Contract on `sessionProg` -/

set_option maxRecDepth 2000000 in
/-- `.rodata` at `lsSha256IVAddr` (`libsignal_protocol:.rodata.cst32+0x100`) holds the 32-byte
SHA-256 IV under `LibsignalRoLoaded lsmpl m`. -/
theorem rodata_placed_sha256IV [LibsignalPlacement] {m : Memory}
    (hro : LibsignalRoLoaded lsmpl m) :
    m.RO LibsignalSession.CryptoHmacSha256.lsSha256IVAddr 32 ∧
    m.readBytes LibsignalSession.CryptoHmacSha256.lsSha256IVAddr 32 =
      LibsignalHmac.shaStateBytes sha256IV := by
  have h := lsro_read_chk hro (sym := LibsignalSession.CryptoHmacSha256.lsSha256IVSym)
    (bs := LibsignalHmac.shaStateBytes sha256IV) (by decide +kernel)
  have haddr : LibsignalSession.CryptoHmacSha256.lsSha256IVAddr =
      lsmpl.ρ LibsignalSession.CryptoHmacSha256.lsSha256IVSym :=
    ls_resolve_data (tgt := LibsignalSession.CryptoHmacSha256.lsSha256IVSym) (by decide)
  rwa [← haddr, LibsignalSession.CryptoHmacSha256.shaStateBytes_length] at h

/-- Relocatable `[LibsignalPlacement]` contract for `<Hmac<Sha256> as KeyInit>::new_from_slice`
(Block `114`) under `LibsignalRoLoaded lsmpl`. -/
theorem new_from_slice_placed_ro_ok [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks}
    (h_memcpy : H LibsignalSession.CryptoHmacSha256.lsMemcpySym =
      some LibsignalAesCbc.memcpyHook)
    (h_compress : H LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base H) (blkPl_114).base
      { newFromSliceSpec F with
        pre := fun x s0 => (newFromSliceSpec F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ } := by
  refine subroutine_ok_intro fun ⟨ret, keyA, key⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [newFromSliceSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, ⟨hx0, hx1, hx2_nat, hkey_len⟩, hsep⟩
  have hb_out := IsBlock.memRegion ret 0x98
  have hb_key := IsBlock.pointsToBytes (a := keyA) key
  have hb_stk := IsBlock.memRegion (s0.sp - 544#64) 544
  have hsep_out : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 544#64) 544 ∗
      ((keyA ↦ₛ key) ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep
    ac_nf at hsep ⊢
  have hsep_key : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep
    ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 544#64) 544 ∗
      (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R) := by
    simp only [newFromSliceStack, stackAt] at hsep
    ac_nf at hsep ⊢
  have hkey_eq : s0.mem.readBytes keyA key.length = key := (hb_key.read hsep_key).2
  have hrw_out : s0.mem.RW ret 0x98 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : s0.mem.RW (s0.sp - 544#64) 544 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hread_iv : s0.mem.Readable LibsignalSession.CryptoHmacSha256.lsSha256IVAddr 32 :=
    fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hdisj_key : key.length = 0 ∨ DisjointRegions keyA key.length (s0.sp - 544#64) 544 := by
    rcases key with _ | ⟨k0, ks⟩
    · exact Or.inl rfl
    · exact Or.inr (hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hx2_len : (s0.readReg64 .x2).toNat = key.length := hx2_nat
  have hrunsTo := LibsignalSession.CryptoHmacSha256.new_from_slice_placed_run (F := F)
    h_memcpy h_compress
    hpc hrun (by rw [hx2_len]; exact hkey_len) hiv_eq
    hread_iv (LibsignalSession.CryptoHmacSha256.disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk)
    (by rw [hx0]; exact hrw_out) hrw_stk
    (by rw [hx0]; exact hb_out.disjoint hb_stk (by decide) (by decide) hsep_out)
    (by rw [hx1, hx2_len]; exact hdisj_key)
    (by simpa [State.spAligned] using hsp)
  rw [hx1, hx2_len, hkey_eq] at hrunsTo
  refine hrunsTo.to_reaches_pc fun sf h5 _ _ htr hvregs => ?_
  rcases h5 with ⟨hpc_sf, hstat_sf, hcallee, hret_sf, hst_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_,
    LibsignalSession.CryptoHmacSha256.CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩
  dsimp only [newFromSliceSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr, ?_⟩
  rw [hx0] at hret_sf hst_sf hframe_sf
  have hpost := LibsignalSession.CryptoHmacSha256.Frame.update_two_blocks hb_out
    (isBlock_nfsResult F ret key) hb_stk hb_stk hsep_out hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStack, stackAt]
  ac_nf at hpost ⊢

theorem new_from_slice_placed_ok_withLsCodeLoaded_ro [LibsignalPlacement] (F : ShaCompress)
    {H : LibsignalHooks}
    (h_memcpy : H LibsignalSession.CryptoHmacSha256.lsMemcpySym =
      some LibsignalAesCbc.memcpyHook)
    (h_compress : H LibsignalSession.CryptoHmacSha256.lsCompress256Sym =
      some (LibsignalHmac.compress256Hook F)) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base H) (blkPl_114).base
      (withLsCodeLoaded lsmpl
        { newFromSliceSpec F with
          pre := fun x s0 => (newFromSliceSpec F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ }) :=
  subroutine_ok_withLsCodeLoaded_of_plain (new_from_slice_placed_ro_ok F h_memcpy h_compress)

end CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer

