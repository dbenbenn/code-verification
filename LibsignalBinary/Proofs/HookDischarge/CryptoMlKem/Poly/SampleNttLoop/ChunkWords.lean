/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.GenPlacedFetches
public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs -- proof-setup: allow-public-import

/-!
# 193-Word Inner Loop Tables and `WordTree` Fetch Bridge (`SampleNttLoop.ChunkWords`)

32-bit machine words (`[11..203]`, `pcBase + 0x2c .. pcBase + 0x32c`), `rfl` decode theorems,
`O(1)` sub-block `FetchesInstrsAt.slice` extraction, and `O(log N)` `WordTree` fetch discharge
for the three `rej_sample` variants (`A`, `B`, `C`) across `B03`–`B07`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection ProofLib.GenPlacedFetches
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkInstrs (
  FetchesInstrsAt pcAt rejHeadLatchInstrs rejOutPre24Instrs rejOutPre57Instrs
  rejSpine14Instrs rejSpine56Instrs rejSpine7Instrs rejStore14Instrs rejStore56Instrs
  rejStore7Instrs rejTriple0ABInstrs rejTriple0CFastInstrs rejTriple0CSlowInstrs)

/-! ## 1. Variants (`A`, `B`, `C`) & Complete 193-Instruction Assemblies -/

/-- The 3 compiled 193-instruction inner-loop variants across all 10 `B03`–`B07` `rej_sample` sites:
    - `varA`: `B03_0`, `B03_1`, `B04_0`, `B04_1` (`isVarA = true`, `spShift = 0`)
    - `varB`: `B05_0`, `B05_1`, `B06_0`, `B07_0`, `B07_1` (`isVarA = false`, `spShift = 0`)
    - `varC`: `B06_1` (`isVarA = false`, `spShift = 7`) -/
inductive RejVariant where
  | varA
  | varB
  | varC
  deriving DecidableEq, Repr

@[expose] def RejVariant.isVarA : RejVariant → Bool
  | .varA => true
  | .varB => false
  | .varC => false

@[expose] def RejVariant.spShift : RejVariant → Nat
  | .varA => 0
  | .varB => 0
  | .varC => 7

@[expose] def rejSpineAllInstrs (isVarA : Bool) (spShift : Nat) : List Instr :=
  rejSpine14Instrs isVarA spShift 1 ++
  rejSpine14Instrs isVarA spShift 2 ++
  rejSpine14Instrs isVarA spShift 3 ++
  rejSpine14Instrs isVarA spShift 4 ++
  rejSpine56Instrs isVarA spShift 5 ++
  rejSpine56Instrs isVarA spShift 6 ++
  rejSpine7Instrs isVarA spShift

@[expose] def rejTailStoreInstrs (isVarA : Bool) (spShift : Nat) : List Instr :=
  rejStore14Instrs isVarA spShift 1 ++
  rejOutPre24Instrs isVarA spShift 2 ++ rejStore14Instrs isVarA spShift 2 ++
  rejOutPre24Instrs isVarA spShift 3 ++ rejStore14Instrs isVarA spShift 3 ++
  rejOutPre24Instrs isVarA spShift 4 ++ rejStore14Instrs isVarA spShift 4 ++
  rejOutPre57Instrs isVarA spShift 5 ++ rejStore56Instrs isVarA spShift 5 ++
  rejOutPre57Instrs isVarA spShift 6 ++ rejStore56Instrs isVarA spShift 6 ++
  rejOutPre57Instrs isVarA spShift 7 ++ rejStore7Instrs isVarA

@[expose] def rejInnerInstrs : RejVariant → List Instr
  | .varA =>
    rejHeadLatchInstrs true ++ rejTriple0ABInstrs true ++
    rejSpineAllInstrs true 0 ++ rejTailStoreInstrs true 0
  | .varB =>
    rejHeadLatchInstrs false ++ rejTriple0ABInstrs false ++
    rejSpineAllInstrs false 0 ++ rejTailStoreInstrs false 0
  | .varC =>
    rejHeadLatchInstrs false ++ rejTriple0CFastInstrs ++
    rejSpineAllInstrs false 7 ++ rejTriple0CSlowInstrs ++ rejTailStoreInstrs false 7

/-! ## 2. Exact 193-Word Machine Code Tables & Kernel `rfl` Decode Proofs -/

@[expose] def rejInnerWordsA : List (BitVec 32) :=
  [0x8b0c022c#32, 0xf10005ef#32, 0x910061ce#32, 0x54fffe40#32, 0xf104019f#32, 0x54ffff82#32,
   0x385f51d1#32, 0x385f61d2#32, 0x8b0c05b0#32, 0x33180e51#32, 0x7134063f#32, 0x54000122#32,
   0x79000211#32, 0x52800031#32, 0x385f71c0#32, 0x53047e52#32, 0x2a001252#32, 0x7134065f#32,
   0x54000103#32, 0x14000009#32, 0xaa1f03f1#32, 0x385f71c0#32, 0x53047e52#32, 0x2a001252#32,
   0x7134065f#32, 0x54000062#32, 0x78317a12#32, 0x91000631#32, 0x385f81c0#32, 0x385f91d2#32,
   0x33180e40#32, 0x7134001f#32, 0x54000869#32, 0x385fa1c0#32, 0x53047e52#32, 0x2a001252#32,
   0x7134025f#32, 0x540008a9#32, 0x385fb1c0#32, 0x385fc1d2#32, 0x33180e40#32, 0x7134001f#32,
   0x540008e9#32, 0x385fd1c0#32, 0x53047e52#32, 0x2a001252#32, 0x7134025f#32, 0x54000929#32,
   0x385fe1c0#32, 0x385ff1d2#32, 0x33180e40#32, 0x7134001f#32, 0x54000969#32, 0x394001c0#32,
   0x53047e52#32, 0x2a001252#32, 0x7134025f#32, 0x540009a9#32, 0x394005c0#32, 0x394009d2#32,
   0x33180e40#32, 0x7134001f#32, 0x540009e9#32, 0x39400dc0#32, 0x53047e52#32, 0x2a001252#32,
   0x7134025f#32, 0x54000a29#32, 0x394011c1#32, 0x394015d2#32, 0x394019c0#32, 0x33180e41#32,
   0x7134003f#32, 0x54000a69#32, 0x53047e52#32, 0x2a001252#32, 0x7134025f#32, 0x54000aa9#32,
   0x39401dc1#32, 0x394021d2#32, 0x394025c0#32, 0x33180e41#32, 0x7134003f#32, 0x54000ae9#32,
   0x53047e52#32, 0x2a001252#32, 0x7134025f#32, 0x54000b29#32, 0x394029c1#32, 0x39402dd2#32,
   0x394031c0#32, 0x33180e41#32, 0x7134003f#32, 0x54000b69#32, 0x53047e52#32, 0x2a001252#32,
   0x7134025f#32, 0x54fff3e8#32, 0x1400005c#32, 0x78317a00#32, 0x91000631#32, 0x385fa1c0#32,
   0x53047e52#32, 0x2a001252#32, 0x7134025f#32, 0x54fff7a8#32, 0x78317a12#32, 0x91000631#32,
   0x385fb1c0#32, 0x385fc1d2#32, 0x33180e40#32, 0x7134001f#32, 0x54fff768#32, 0x78317a00#32,
   0x91000631#32, 0x385fd1c0#32, 0x53047e52#32, 0x2a001252#32, 0x7134025f#32, 0x54fff728#32,
   0x78317a12#32, 0x91000631#32, 0x385fe1c0#32, 0x385ff1d2#32, 0x33180e40#32, 0x7134001f#32,
   0x54fff6e8#32, 0x78317a00#32, 0x91000631#32, 0x394001c0#32, 0x53047e52#32, 0x2a001252#32,
   0x7134025f#32, 0x54fff6a8#32, 0x78317a12#32, 0x91000631#32, 0x394005c0#32, 0x394009d2#32,
   0x33180e40#32, 0x7134001f#32, 0x54fff668#32, 0x78317a00#32, 0x91000631#32, 0x39400dc0#32,
   0x53047e52#32, 0x2a001252#32, 0x7134025f#32, 0x54fff628#32, 0x78317a12#32, 0x91000631#32,
   0x394011c1#32, 0x394015d2#32, 0x394019c0#32, 0x33180e41#32, 0x7134003f#32, 0x54fff5e8#32,
   0x78317a01#32, 0x91000631#32, 0x53047e52#32, 0x2a001252#32, 0x7134025f#32, 0x54fff5a8#32,
   0x78317a12#32, 0x91000631#32, 0x39401dc1#32, 0x394021d2#32, 0x394025c0#32, 0x33180e41#32,
   0x7134003f#32, 0x54fff568#32, 0x78317a01#32, 0x91000631#32, 0x53047e52#32, 0x2a001252#32,
   0x7134025f#32, 0x54fff528#32, 0x78317a12#32, 0x91000631#32, 0x394029c1#32, 0x39402dd2#32,
   0x394031c0#32, 0x33180e41#32, 0x7134003f#32, 0x54fff4e8#32, 0x78317a01#32, 0x91000631#32,
   0x53047e52#32, 0x2a001252#32, 0x7134025f#32, 0x54ffe868#32, 0x78317a12#32, 0x91000631#32,
   0x17ffff40#32]

@[expose] def rejInnerWordsB : List (BitVec 32) :=
  [0x8b0b020b#32, 0xf10005ce#32, 0x910061ad#32, 0x54fffe40#32, 0xf104017f#32, 0x54ffff82#32,
   0x385f51b0#32, 0x385f61b1#32, 0x8b0b058f#32, 0x33180e30#32, 0x7134061f#32, 0x54000122#32,
   0x790001f0#32, 0x52800030#32, 0x385f71b2#32, 0x53047e31#32, 0x2a121231#32, 0x7134063f#32,
   0x54000103#32, 0x14000009#32, 0xaa1f03f0#32, 0x385f71b2#32, 0x53047e31#32, 0x2a121231#32,
   0x7134063f#32, 0x54000062#32, 0x783079f1#32, 0x91000610#32, 0x385f81b2#32, 0x385f91b1#32,
   0x33180e32#32, 0x7134025f#32, 0x54000869#32, 0x385fa1b2#32, 0x53047e31#32, 0x2a121231#32,
   0x7134023f#32, 0x540008a9#32, 0x385fb1b2#32, 0x385fc1b1#32, 0x33180e32#32, 0x7134025f#32,
   0x540008e9#32, 0x385fd1b2#32, 0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54000929#32,
   0x385fe1b2#32, 0x385ff1b1#32, 0x33180e32#32, 0x7134025f#32, 0x54000969#32, 0x394001b2#32,
   0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x540009a9#32, 0x394005b2#32, 0x394009b1#32,
   0x33180e32#32, 0x7134025f#32, 0x540009e9#32, 0x39400db2#32, 0x53047e31#32, 0x2a121231#32,
   0x7134023f#32, 0x54000a29#32, 0x394011a0#32, 0x394015b1#32, 0x394019b2#32, 0x33180e20#32,
   0x7134001f#32, 0x54000a69#32, 0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54000aa9#32,
   0x39401da0#32, 0x394021b1#32, 0x394025b2#32, 0x33180e20#32, 0x7134001f#32, 0x54000ae9#32,
   0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54000b29#32, 0x394029a0#32, 0x39402db1#32,
   0x394031b2#32, 0x33180e20#32, 0x7134001f#32, 0x54000b69#32, 0x53047e31#32, 0x2a121231#32,
   0x7134023f#32, 0x54fff3e8#32, 0x1400005c#32, 0x783079f2#32, 0x91000610#32, 0x385fa1b2#32,
   0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54fff7a8#32, 0x783079f1#32, 0x91000610#32,
   0x385fb1b2#32, 0x385fc1b1#32, 0x33180e32#32, 0x7134025f#32, 0x54fff768#32, 0x783079f2#32,
   0x91000610#32, 0x385fd1b2#32, 0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54fff728#32,
   0x783079f1#32, 0x91000610#32, 0x385fe1b2#32, 0x385ff1b1#32, 0x33180e32#32, 0x7134025f#32,
   0x54fff6e8#32, 0x783079f2#32, 0x91000610#32, 0x394001b2#32, 0x53047e31#32, 0x2a121231#32,
   0x7134023f#32, 0x54fff6a8#32, 0x783079f1#32, 0x91000610#32, 0x394005b2#32, 0x394009b1#32,
   0x33180e32#32, 0x7134025f#32, 0x54fff668#32, 0x783079f2#32, 0x91000610#32, 0x39400db2#32,
   0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54fff628#32, 0x783079f1#32, 0x91000610#32,
   0x394011a0#32, 0x394015b1#32, 0x394019b2#32, 0x33180e20#32, 0x7134001f#32, 0x54fff5e8#32,
   0x783079e0#32, 0x91000610#32, 0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54fff5a8#32,
   0x783079f1#32, 0x91000610#32, 0x39401da0#32, 0x394021b1#32, 0x394025b2#32, 0x33180e20#32,
   0x7134001f#32, 0x54fff568#32, 0x783079e0#32, 0x91000610#32, 0x53047e31#32, 0x2a121231#32,
   0x7134023f#32, 0x54fff528#32, 0x783079f1#32, 0x91000610#32, 0x394029a0#32, 0x39402db1#32,
   0x394031b2#32, 0x33180e20#32, 0x7134001f#32, 0x54fff4e8#32, 0x783079e0#32, 0x91000610#32,
   0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54ffe868#32, 0x783079f1#32, 0x91000610#32,
   0x17ffff40#32]

@[expose] def rejInnerWordsC : List (BitVec 32) :=
  [0x8b0b020b#32, 0xf10005ce#32, 0x910061ad#32, 0x54fffe40#32, 0xf104017f#32, 0x54ffff82#32,
   0x385f51b0#32, 0x385f61b1#32, 0x8b0b058f#32, 0x33180e30#32, 0x7134061f#32, 0x54000a22#32,
   0x790001f0#32, 0x52800030#32, 0x385f71b2#32, 0x53047e31#32, 0x2a121231#32, 0x7134063f#32,
   0x54000062#32, 0x783079f1#32, 0x91000610#32, 0x385f81b2#32, 0x385f91b1#32, 0x33180e32#32,
   0x7134025f#32, 0x54000949#32, 0x385fa1b2#32, 0x53047e31#32, 0x2a121231#32, 0x7134023f#32,
   0x54000989#32, 0x385fb1b2#32, 0x385fc1b1#32, 0x33180e32#32, 0x7134025f#32, 0x540009c9#32,
   0x385fd1b2#32, 0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54000a09#32, 0x385fe1b2#32,
   0x385ff1b1#32, 0x33180e32#32, 0x7134025f#32, 0x54000a49#32, 0x394001b2#32, 0x53047e31#32,
   0x2a121231#32, 0x7134023f#32, 0x54000a89#32, 0x394005b2#32, 0x394009b1#32, 0x33180e32#32,
   0x7134025f#32, 0x54000ac9#32, 0x39400db2#32, 0x53047e31#32, 0x2a121231#32, 0x7134023f#32,
   0x54000b09#32, 0x394011a0#32, 0x394015b1#32, 0x394019b2#32, 0x33180e20#32, 0x7134001f#32,
   0x54000b49#32, 0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54000b89#32, 0x39401da0#32,
   0x394021b1#32, 0x394025b2#32, 0x33180e20#32, 0x7134001f#32, 0x54000bc9#32, 0x53047e31#32,
   0x2a121231#32, 0x7134023f#32, 0x54000c09#32, 0x394029a0#32, 0x39402db1#32, 0x394031b2#32,
   0x33180e20#32, 0x7134001f#32, 0x54000c49#32, 0x53047e31#32, 0x2a121231#32, 0x7134023f#32,
   0x54fff4c8#32, 0x14000063#32, 0xaa1f03f0#32, 0x385f71b2#32, 0x53047e31#32, 0x2a121231#32,
   0x7134063f#32, 0x54fff643#32, 0x17ffffb3#32, 0x783079f2#32, 0x91000610#32, 0x385fa1b2#32,
   0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54fff6c8#32, 0x783079f1#32, 0x91000610#32,
   0x385fb1b2#32, 0x385fc1b1#32, 0x33180e32#32, 0x7134025f#32, 0x54fff688#32, 0x783079f2#32,
   0x91000610#32, 0x385fd1b2#32, 0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54fff648#32,
   0x783079f1#32, 0x91000610#32, 0x385fe1b2#32, 0x385ff1b1#32, 0x33180e32#32, 0x7134025f#32,
   0x54fff608#32, 0x783079f2#32, 0x91000610#32, 0x394001b2#32, 0x53047e31#32, 0x2a121231#32,
   0x7134023f#32, 0x54fff5c8#32, 0x783079f1#32, 0x91000610#32, 0x394005b2#32, 0x394009b1#32,
   0x33180e32#32, 0x7134025f#32, 0x54fff588#32, 0x783079f2#32, 0x91000610#32, 0x39400db2#32,
   0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54fff548#32, 0x783079f1#32, 0x91000610#32,
   0x394011a0#32, 0x394015b1#32, 0x394019b2#32, 0x33180e20#32, 0x7134001f#32, 0x54fff508#32,
   0x783079e0#32, 0x91000610#32, 0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54fff4c8#32,
   0x783079f1#32, 0x91000610#32, 0x39401da0#32, 0x394021b1#32, 0x394025b2#32, 0x33180e20#32,
   0x7134001f#32, 0x54fff488#32, 0x783079e0#32, 0x91000610#32, 0x53047e31#32, 0x2a121231#32,
   0x7134023f#32, 0x54fff448#32, 0x783079f1#32, 0x91000610#32, 0x394029a0#32, 0x39402db1#32,
   0x394031b2#32, 0x33180e20#32, 0x7134001f#32, 0x54fff408#32, 0x783079e0#32, 0x91000610#32,
   0x53047e31#32, 0x2a121231#32, 0x7134023f#32, 0x54ffe868#32, 0x783079f1#32, 0x91000610#32,
   0x17ffff40#32]

@[expose] def rejInnerWords : RejVariant → List (BitVec 32)
  | .varA => rejInnerWordsA
  | .varB => rejInnerWordsB
  | .varC => rejInnerWordsC

section
set_option maxRecDepth 4096

theorem rejInnerWordsA_decode : rejInnerWordsA.map decode = (rejInnerInstrs .varA).map some := rfl
theorem rejInnerWordsB_decode : rejInnerWordsB.map decode = (rejInnerInstrs .varB).map some := rfl
theorem rejInnerWordsC_decode : rejInnerWordsC.map decode = (rejInnerInstrs .varC).map some := rfl

end

theorem rejInnerWords_decode (v : RejVariant) :
    (rejInnerWords v).map decode = (rejInnerInstrs v).map some := by
  cases v
  · exact rejInnerWordsA_decode
  · exact rejInnerWordsB_decode
  · exact rejInnerWordsC_decode

@[simp] theorem rejInnerWords_length (v : RejVariant) : (rejInnerWords v).length = 193 := by
  cases v <;> rfl

/-! ## 3. Sub-Block `FetchesInstrsAt.slice` & `O(log N)` `WordTree` Fetch Bridge -/

theorem FetchesInstrsAt.slice {prog : Program} {pcBase : BitVec 64}
    {baseIdx subIdx : Nat} {full sub : List Instr}
    (hf : FetchesInstrsAt prog pcBase baseIdx full)
    (hle : baseIdx ≤ subIdx)
    (hsub : (full.drop (subIdx - baseIdx)).take sub.length = sub) :
    FetchesInstrsAt prog pcBase subIdx sub := by
  intro k inst hk
  have hlt : k < sub.length := by
    by_contra hge; simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hk
  have hk' : ((full.drop (subIdx - baseIdx)).take sub.length)[k]? = some inst := by
    rwa [hsub]
  rw [List.getElem?_take_of_lt hlt, List.getElem?_drop] at hk'
  have hfetch := hf ((subIdx - baseIdx) + k) inst hk'
  rwa [show baseIdx + ((subIdx - baseIdx) + k) = subIdx + k by omega] at hfetch

/-- Lift word-level fetches `[11..203]` to `FetchesInstrsAt prog pcBase 11 (rejInnerInstrs v)`. -/
theorem fetchesInstrsAt_of_words {prog : Program} {pcBase : BitVec 64} {v : RejVariant}
    (hw : ∀ k w, (rejInnerWords v)[k]? = some w → prog.fetch (pcAt pcBase (11 + k)) = decode w) :
    FetchesInstrsAt prog pcBase 11 (rejInnerInstrs v) := by
  intro k inst hk
  have hmap : ((rejInnerInstrs v).map some)[k]? = some (some inst) := by simp [hk]
  rw [← rejInnerWords_decode v, List.getElem?_map] at hmap
  cases hwk : (rejInnerWords v)[k]? with
  | none => simp [hwk] at hmap
  | some w =>
    simp only [hwk, Option.map_some, Option.some.injEq] at hmap
    exact (hw k w hwk).trans hmap

/-- Boolean `WordTree` + no-relocation range check for any instruction sequence starting at `off`. -/
@[expose] def checkWordsAtTree (t : WordTree) (lib : PlacedLib) (off : Nat) :
    List (BitVec 32) → Bool
  | [] => true
  | w :: ws =>
    match t.getQuad? (off / 4) with
    | some (b0, b1, b2, b3) =>
      (wordOfBytesLE [b0, b1, b2, b3] 0 == w) &&
      (lib.text.relocAt? off).isNone &&
      checkWordsAtTree t lib (off + 4) ws
    | none => false

private theorem fetch_of_checkWordsAtTree {lib : PlacedLib} {t : WordTree} {n : Nat}
    {pl : Placement} {b : BitVec 64} {X : String → Option (State → State)}
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    (hP : lib.Placeable pl)
    {off : Nat} {ws : List (BitVec 32)}
    (hal : off % 4 = 0) (hlen : off + 4 * ws.length ≤ 4 * n) (hlt : off + 4 * ws.length < 2 ^ 64)
    (hchk : checkWordsAtTree t lib off ws = true) :
    ∀ k w, ws[k]? = some w →
      ((lib.program pl).rebase b X).fetch (b + BitVec.ofNat 64 (off + 4 * k)) = decode w := by
  induction ws generalizing off with
  | nil => intro k w hk; simp at hk
  | cons w0 rest ih =>
    simp only [checkWordsAtTree] at hchk
    cases hq : t.getQuad? (off / 4) with
    | none => simp [hq] at hchk
    | some q =>
      rcases q with ⟨b0, b1, b2, b3⟩
      simp only [hq, Bool.and_eq_true, beq_iff_eq] at hchk
      rcases hchk with ⟨⟨hw0, hnr0⟩, hrest⟩
      intro k w hk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        simp only [Nat.mul_zero, Nat.add_zero]
        have hmul : 4 * (off / 4) = off := by omega
        have hword : lib.text.wordAt off = w0 := by
          rw [← hmul, wordAt_of_getQuad? hcode hsize hq, hw0]
        have hpatch : lib.text.patchedWord pl off = w0 := by
          rw [CodeBlock.patchedWord_of_relocAt_none (Option.isNone_iff_eq_none.mp hnr0), hword]
        have hnh : ((lib.program pl).rebase b X).hookAtOff? off = none :=
          hookAtOff?_rebase_of_placeable hcode hsize hP (by simp at hlen; omega)
        exact fetch_rebase_of_patchedWord hnh hal
          (by rw [length_text_of_tree hcode hsize]; simp at hlen; omega)
          (by simp at hlt; omega) hpatch
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        have hstep := ih (off := off + 4) (by omega)
          (by simp only [List.length_cons] at hlen; omega)
          (by simp only [List.length_cons] at hlt; omega) hrest k' w hk
        rwa [show (off + 4) + 4 * k' = off + 4 * (k' + 1) by omega] at hstep

/-- One-shot `rfl`-checkable `FetchesInstrsAt` constructor for any `B03`–`B07` `rej_sample` site
    at byte offset `siteOff` (`pcBase = b + BitVec.ofNat 64 siteOff`). -/
theorem fetchesInstrsAt_of_wordTree {lib : PlacedLib} {t : WordTree} {n siteOff : Nat}
    {pl : Placement} {b : BitVec 64} {X : String → Option (State → State)} {v : RejVariant}
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n) (hP : lib.Placeable pl)
    (hal : siteOff % 4 = 0) (hlen : siteOff + 816 ≤ 4 * n) (hlt : siteOff + 816 < 2 ^ 64)
    (hchk : checkWordsAtTree t lib (siteOff + 44) (rejInnerWords v) = true) :
    FetchesInstrsAt ((lib.program pl).rebase b X) (b + BitVec.ofNat 64 siteOff) 11
      (rejInnerInstrs v) := by
  refine fetchesInstrsAt_of_words fun k w hwk => ?_
  have hklt : k < 193 := by
    have hlt' : k < (rejInnerWords v).length := by
      by_contra hge; simp [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hwk
    simpa using hlt'
  have hf := fetch_of_checkWordsAtTree (pl := pl) (b := b) (X := X) hcode hsize hP
    (off := siteOff + 44) (ws := rejInnerWords v)
    (by omega) (by simp; omega) (by simp; omega) hchk k w hwk
  have hpc : pcAt (b + BitVec.ofNat 64 siteOff) (11 + k) =
      b + BitVec.ofNat 64 ((siteOff + 44) + 4 * k) := by
    unfold pcAt; bv_omega
  rwa [hpc]

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Poly.SampleNttLoop.ChunkWords
