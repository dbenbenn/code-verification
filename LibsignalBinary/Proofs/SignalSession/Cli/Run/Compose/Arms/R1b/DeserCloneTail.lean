/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.DeserCloneErr -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.M4Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.ReadKpk
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Compose.Arms.R1b.SliceHelpers

/-!
# Stage 4b (`opk` Stack Staging and Buffer Deallocations) of Arm `R1b` (`0x25f4 → 0x27bc`)

Proves `r1b_step_tail_25f4`, staging the optional `opk` into its final stack slots (`0x25f4 → 0x277c`)
and sequentially deallocating the heap buffers `kpkBs`, `spkBs`, and `regBs` (`0x277c → 0x27bc`).
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton

/-- Stage-3 `opk` and `spk` scratch layout entering `0x27bc` (`[0x220..0x260)` and `[0x2c0..0x4d0)` rejoined into `memRegion`s). -/
@[expose] def r1b_opkStage3At (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
    (w0e0 w0e4 c9 : BitVec 32) (c13 : BitVec 16) (w15 c23 : BitVec 64) (c31 : BitVec 8) :
    SepProp :=
  memRegion fsp 0x0e0 ∗
    ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗
    ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
    ((fsp + 0x0e8#64) ↦₆₄ w15) ∗
    ((fsp + 0x0f0#64) ↦₆₄ spkW8.zeroExtend 64) ∗
    ((fsp + 0x0f8#64) ↦₆₄ spkW24) ∗
    ((fsp + 0x100#64) ↦₆₄ spkW16) ∗
    ((fsp + 0x108#64) ↦₆₄ spkW0) ∗
    memRegion (fsp + 0x1d0#64) 0x18 ∗
    ((fsp + 0x1e8#64) ↦₆₄ c23) ∗
    ((fsp + 0x1f0#64) ↦₈ c31) ∗
    memRegion (fsp + 0x1f1#64) 7 ∗
    ((fsp + 0x1f8#64) ↦₃₂ c9) ∗
    ((fsp + 0x1fc#64) ↦₁₆ c13) ∗
    memRegion (fsp + 0x1fe#64) 2 ∗
    Wire.sevenBytesHeadAt (fsp + 0x200#64) c0 c1 c2 c3 c4 c5 c6 ∗
    memRegion (fsp + 0x207#64) 0x19 ∗
    memRegion (fsp + 0x220#64) 0x40 ∗
    memRegion (fsp + 0x2c0#64) 0x210

/-- Intermediate Stage-2 scratch layout at `0x2744` (merge point of `opkBs = []` and `opkBs ≠ []`). -/
private def r1b_opkStage2At (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 : BitVec 8)
    (c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
    (w0e0 w0e4 w9 s2_w9 c9 : BitVec 32)
    (w13 s2_w13 c13 : BitVec 16)
    (w15 w23 s2_w23 c23 : BitVec 64)
    (b31 s2_b31 c31 : BitVec 8) : SepProp :=
  memRegion fsp 0x0e0 ∗
    ((fsp + 0x0e0#64) ↦₃₂ w0e0) ∗
    ((fsp + 0x0e4#64) ↦₃₂ w0e4) ∗
    ((fsp + 0x0e8#64) ↦₆₄ w15) ∗
    ((fsp + 0x0f0#64) ↦₆₄ spkW8.zeroExtend 64) ∗
    ((fsp + 0x0f8#64) ↦₆₄ spkW24) ∗
    ((fsp + 0x100#64) ↦₆₄ spkW16) ∗
    ((fsp + 0x108#64) ↦₆₄ spkW0) ∗
    memRegion (fsp + 0x1d0#64) 0x18 ∗
    ((fsp + 0x1e8#64) ↦₆₄ c23) ∗
    ((fsp + 0x1f0#64) ↦₈ c31) ∗
    memRegion (fsp + 0x1f1#64) 7 ∗
    ((fsp + 0x1f8#64) ↦₃₂ c9) ∗
    ((fsp + 0x1fc#64) ↦₁₆ c13) ∗
    memRegion (fsp + 0x1fe#64) 2 ∗
    Wire.sevenBytesHeadAt (fsp + 0x200#64) c0 c1 c2 c3 c4 c5 c6 ∗
    memRegion (fsp + 0x207#64) 0x19 ∗
    ((fsp + 0x220#64) ↦₆₄ w23) ∗
    ((fsp + 0x228#64) ↦₈ b31) ∗
    memRegion (fsp + 0x229#64) 0x37 ∗
    memRegion (fsp + 0x2c0#64) 0x40 ∗
    ((fsp + 0x300#64) ↦₃₂ s2_w9) ∗
    ((fsp + 0x304#64) ↦₁₆ s2_w13) ∗
    memRegion (fsp + 0x306#64) 0x1a ∗
    ((fsp + 0x320#64) ↦₆₄ s2_w23) ∗
    ((fsp + 0x328#64) ↦₈ s2_b31) ∗
    memRegion (fsp + 0x329#64) 0x57 ∗
    Wire.sevenBytesHeadAt (fsp + 0x380#64) s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 ∗
    memRegion (fsp + 0x387#64) 0x31 ∗
    Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
    memRegion (fsp + 0x3bf#64) 0x19 ∗
    ((fsp + 0x3d8#64) ↦₃₂ w9) ∗
    ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
    memRegion (fsp + 0x3de#64) 0xf2

private theorem r1b_stage1Spk_open_stage2 (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (w0e0 w0e4 w9 : BitVec 32) (w13 : BitVec 16) (w15 w23 : BitVec 64) (b31 : BitVec 8) :
    r1b_opkStage1SpkAt fsp spkW0 spkW8 spkW16 spkW24
      b0 b1 b2 b3 b4 b5 b6 w0e0 w0e4 w9 w13 w15 w23 b31 ⊢
    ∃∗ s2_b0 : BitVec 8, ∃∗ s2_b1 : BitVec 8, ∃∗ s2_b2 : BitVec 8, ∃∗ s2_b3 : BitVec 8,
    ∃∗ s2_b4 : BitVec 8, ∃∗ s2_b5 : BitVec 8, ∃∗ s2_b6 : BitVec 8,
    ∃∗ c0 : BitVec 8, ∃∗ c1 : BitVec 8, ∃∗ c2 : BitVec 8, ∃∗ c3 : BitVec 8,
    ∃∗ c4 : BitVec 8, ∃∗ c5 : BitVec 8, ∃∗ c6 : BitVec 8,
    ∃∗ s2_w9 : BitVec 32, ∃∗ c9 : BitVec 32,
    ∃∗ s2_w13 : BitVec 16, ∃∗ c13 : BitVec 16,
    ∃∗ s2_w23 : BitVec 64, ∃∗ c23 : BitVec 64,
    ∃∗ s2_b31 : BitVec 8, ∃∗ c31 : BitVec 8,
      r1b_opkStage2At fsp spkW0 spkW8 spkW16 spkW24
        b0 b1 b2 b3 b4 b5 b6
        s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
        c0 c1 c2 c3 c4 c5 c6
        w0e0 w0e4 w9 s2_w9 c9 w13 s2_w13 c13 w15 w23 s2_w23 c23 b31 s2_b31 c31 := by
  dsimp only [r1b_opkStage1SpkAt]
  have h1d0 : memRegion (fsp + 0x1d0#64) 0x50 =
      memRegion (fsp + 0x1d0#64) 0x18 ∗
        memRegion (fsp + 0x1e8#64) 8 ∗ memRegion (fsp + 0x1f0#64) 1 ∗
        memRegion (fsp + 0x1f1#64) 7 ∗ memRegion (fsp + 0x1f8#64) 4 ∗
        memRegion (fsp + 0x1fc#64) 2 ∗ memRegion (fsp + 0x1fe#64) 2 ∗
        memRegion (fsp + 0x200#64) 7 ∗ memRegion (fsp + 0x207#64) 0x19 := by
    rw [r1b_split_region fsp 0x1d0 0x18 0x38,
      r1b_split_region fsp 0x1e8 8 0x30,
      r1b_split_region fsp 0x1f0 1 0x2f,
      r1b_split_region fsp 0x1f1 7 0x28,
      r1b_split_region fsp 0x1f8 4 0x24,
      r1b_split_region fsp 0x1fc 2 0x22,
      r1b_split_region fsp 0x1fe 2 0x20,
      r1b_split_region fsp 0x200 7 0x19]
  have h2c0 : memRegion (fsp + 0x2c0#64) 0xf8 =
      memRegion (fsp + 0x2c0#64) 0x40 ∗
        memRegion (fsp + 0x300#64) 4 ∗ memRegion (fsp + 0x304#64) 2 ∗
        memRegion (fsp + 0x306#64) 0x1a ∗ memRegion (fsp + 0x320#64) 8 ∗
        memRegion (fsp + 0x328#64) 1 ∗ memRegion (fsp + 0x329#64) 0x57 ∗
        memRegion (fsp + 0x380#64) 7 ∗ memRegion (fsp + 0x387#64) 0x31 := by
    rw [r1b_split_region fsp 0x2c0 0x40 0xb8,
      r1b_split_region fsp 0x300 4 0xb4,
      r1b_split_region fsp 0x304 2 0xb2,
      r1b_split_region fsp 0x306 0x1a 0x98,
      r1b_split_region fsp 0x320 8 0x90,
      r1b_split_region fsp 0x328 1 0x8f,
      r1b_split_region fsp 0x329 0x57 0x38,
      r1b_split_region fsp 0x380 7 0x31]
  rw [h1d0, h2c0,
    ProofLib.memRegion_eight (fsp + 0x1e8#64),
    ProofLib.memRegion_one (fsp + 0x1f0#64),
    ProofLib.memRegion_four (fsp + 0x1f8#64),
    ProofLib.memRegion_two (fsp + 0x1fc#64),
    ProofLib.memRegion_four (fsp + 0x300#64),
    ProofLib.memRegion_two (fsp + 0x304#64),
    ProofLib.memRegion_eight (fsp + 0x320#64),
    ProofLib.memRegion_one (fsp + 0x328#64)]
  refine Entails.trans
    (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (r1b_memRegion7_to_head7 (fsp + 0x200#64))
        (r1b_memRegion7_to_head7 (fsp + 0x380#64))) (by r1b_ac)) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun s2_b31 =>
    Entails.sepExists_elim fun s2_w23 =>
    Entails.sepExists_elim fun s2_w13 =>
    Entails.sepExists_elim fun s2_w9 =>
    Entails.sepExists_elim fun c13 =>
    Entails.sepExists_elim fun c9 =>
    Entails.sepExists_elim fun c31 =>
    Entails.sepExists_elim fun c23 =>
    Entails.sepExists_elim fun s2_b0 =>
    Entails.sepExists_elim fun s2_b1 =>
    Entails.sepExists_elim fun s2_b2 =>
    Entails.sepExists_elim fun s2_b3 =>
    Entails.sepExists_elim fun s2_b4 =>
    Entails.sepExists_elim fun s2_b5 =>
    Entails.sepExists_elim fun s2_b6 =>
    Entails.sepExists_elim fun c0 =>
    Entails.sepExists_elim fun c1 =>
    Entails.sepExists_elim fun c2 =>
    Entails.sepExists_elim fun c3 =>
    Entails.sepExists_elim fun c4 =>
    Entails.sepExists_elim fun c5 =>
    Entails.sepExists_elim fun c6 => ?_
  refine Entails.sepExists_right s2_b0 (Entails.sepExists_right s2_b1
    (Entails.sepExists_right s2_b2 (Entails.sepExists_right s2_b3
    (Entails.sepExists_right s2_b4 (Entails.sepExists_right s2_b5
    (Entails.sepExists_right s2_b6 (Entails.sepExists_right c0
    (Entails.sepExists_right c1 (Entails.sepExists_right c2
    (Entails.sepExists_right c3 (Entails.sepExists_right c4
    (Entails.sepExists_right c5 (Entails.sepExists_right c6
    (Entails.sepExists_right s2_w9 (Entails.sepExists_right c9
    (Entails.sepExists_right s2_w13 (Entails.sepExists_right c13
    (Entails.sepExists_right s2_w23 (Entails.sepExists_right c23
    (Entails.sepExists_right s2_b31 (Entails.sepExists_right c31 ?_)))))))))))))))))))))
  dsimp only [r1b_opkStage2At]
  exact Entails.of_eq (by r1b_ac)

private theorem r1b_stage2_close_stage3 (fsp : BitVec 64)
    (spkW0 : BitVec 64) (spkW8 : BitVec 32) (spkW16 spkW24 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 : BitVec 8)
    (c0 c1 c2 c3 c4 c5 c6 : BitVec 8)
    (w0e0 w0e4 w9 s2_w9 c9 : BitVec 32)
    (w13 s2_w13 c13 : BitVec 16)
    (w15 w23 s2_w23 c23 : BitVec 64)
    (b31 s2_b31 c31 : BitVec 8) :
    r1b_opkStage2At fsp spkW0 spkW8 spkW16 spkW24
      b0 b1 b2 b3 b4 b5 b6
      s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6
      c0 c1 c2 c3 c4 c5 c6
      w0e0 w0e4 w9 s2_w9 c9 w13 s2_w13 c13 w15 w23 s2_w23 c23 b31 s2_b31 c31 ⊢
    r1b_opkStage3At fsp spkW0 spkW8 spkW16 spkW24
      c0 c1 c2 c3 c4 c5 c6 w0e0 w0e4 c9 c13 w15 c23 c31 := by
  dsimp only [r1b_opkStage2At, r1b_opkStage3At]
  have h220 :
      ((fsp + 0x220#64) ↦₆₄ w23) ∗ ((fsp + 0x228#64) ↦₈ b31) ∗
        memRegion (fsp + 0x229#64) 0x37 ⊢
        memRegion (fsp + 0x220#64) 0x40 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (r1b_cell8_to_region _ _)) (by r1b_ac)) ?_
    simp only [sepConj_assoc]
    rw [r1b_join_region fsp 0x228 1 0x37, r1b_join_region fsp 0x220 8 0x38]
    exact Entails.of_eq (by r1b_ac)
  have h2c0 :
      memRegion (fsp + 0x2c0#64) 0x40 ∗
        ((fsp + 0x300#64) ↦₃₂ s2_w9) ∗ ((fsp + 0x304#64) ↦₁₆ s2_w13) ∗
        memRegion (fsp + 0x306#64) 0x1a ∗
        ((fsp + 0x320#64) ↦₆₄ s2_w23) ∗ ((fsp + 0x328#64) ↦₈ s2_b31) ∗
        memRegion (fsp + 0x329#64) 0x57 ∗
        Wire.sevenBytesHeadAt (fsp + 0x380#64) s2_b0 s2_b1 s2_b2 s2_b3 s2_b4 s2_b5 s2_b6 ∗
        memRegion (fsp + 0x387#64) 0x31 ∗
        Wire.sevenBytesHeadAt (fsp + 0x3b8#64) b0 b1 b2 b3 b4 b5 b6 ∗
        memRegion (fsp + 0x3bf#64) 0x19 ∗
        ((fsp + 0x3d8#64) ↦₃₂ w9) ∗ ((fsp + 0x3dc#64) ↦₁₆ w13) ∗
        memRegion (fsp + 0x3de#64) 0xf2 ⊢
        memRegion (fsp + 0x2c0#64) 0x210 := by
    refine Entails.trans (r1b_entails_frame (by r1b_ac)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo16_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (r1b_cell8_to_region _ _)
              (sepConj_mono (r1b_head7_to_region _ _ _ _ _ _ _ _)
                (sepConj_mono (r1b_head7_to_region _ _ _ _ _ _ _ _)
                  (sepConj_mono (pointsTo32_entails_memRegion _ _)
                    (pointsTo16_entails_memRegion _ _)))))))) (by r1b_ac)) ?_
    refine Entails.trans (Entails.of_eq (show _ =
      memRegion (fsp + 0x2c0#64) 0x40 ∗
        memRegion (fsp + 0x300#64) 4 ∗ memRegion (fsp + 0x304#64) 2 ∗
        memRegion (fsp + 0x306#64) 0x1a ∗
        memRegion (fsp + 0x320#64) 8 ∗ memRegion (fsp + 0x328#64) 1 ∗
        memRegion (fsp + 0x329#64) 0x57 ∗
        memRegion (fsp + 0x380#64) 7 ∗ memRegion (fsp + 0x387#64) 0x31 ∗
        memRegion (fsp + 0x3b8#64) 7 ∗ memRegion (fsp + 0x3bf#64) 0x19 ∗
        memRegion (fsp + 0x3d8#64) 4 ∗ memRegion (fsp + 0x3dc#64) 2 ∗
        memRegion (fsp + 0x3de#64) 0xf2 by r1b_ac)) ?_
    rw [r1b_join_region fsp 0x3dc 2 0xf2,
      r1b_join_region fsp 0x3d8 4 0xf4,
      r1b_join_region fsp 0x3bf 0x19 0xf8,
      r1b_join_region fsp 0x3b8 7 0x111,
      r1b_join_region fsp 0x387 0x31 0x118,
      r1b_join_region fsp 0x380 7 0x149,
      r1b_join_region fsp 0x329 0x57 0x150,
      r1b_join_region fsp 0x328 1 0x1a7,
      r1b_join_region fsp 0x320 8 0x1a8,
      r1b_join_region fsp 0x306 0x1a 0x1b0,
      r1b_join_region fsp 0x304 2 0x1ca,
      r1b_join_region fsp 0x300 4 0x1cc,
      r1b_join_region fsp 0x2c0 0x40 0x1d0]
    exact Entails.refl _
  exact r1b_entails_frame (by r1b_ac) (sepConj_mono h220 h2c0) (by r1b_ac)

end CryptoVerification.SignalSession.Cli.RunCompose
