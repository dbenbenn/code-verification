/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
import LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast
import ProofLib

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1InitSym

open Arm64 ProofLib
open scoped ProofLib.ProgramReflection
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymDefs
  (SExpr SymCfg SymState runSymRange)
open LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.PolySymFast
  (runSymRange_of_fast)

@[expose] def cfgDot1Init : SymCfg := ⟨2096, 21, .spOff 28368, false⟩

@[expose] def symDot1InitStart : SymState :=
  { vregs := ⟨.const 0x0000#16, .vreg0 1, .vreg0 2, .vreg0 3,
     .vreg0 4, .vreg0 5, .vreg0 6, .vreg0 7,
     .vreg0 8, .vreg0 9, .vreg0 10, .vreg0 11,
     .vreg0 12, .vreg0 13, .vreg0 14, .vreg0 15,
     .vreg0 16, .vreg0 17, .vreg0 18, .vreg0 19,
     .vreg0 20, .vreg0 21, .vreg0 22, .vreg0 23,
     .vreg0 24, .vreg0 25, .vreg0 26, .vreg0 27,
     .vreg0 28, .vreg0 29, .vreg0 30, .vreg0 31⟩
    spill := ⟨.spill0 0, .spill0 1, .spill0 2, .spill0 3,
     .spill0 4, .spill0 5, .spill0 6, .spill0 7,
     .spill0 8, .spill0 9, .spill0 10, .spill0 11,
     .spill0 12, .spill0 13, .spill0 14, .spill0 15,
     .spill0 16, .spill0 17, .spill0 18, .spill0 19,
     .spill0 20, .spill0 21, .spill0 22, .spill0 23,
     .spill0 24, .spill0 25, .spill0 26, .spill0 27,
     .spill0 28, .spill0 29, .spill0 30, .spill0 31,
     .spill0 32, .spill0 33, .spill0 34, .spill0 35,
     .spill0 36, .spill0 37, .spill0 38, .spill0 39⟩
    poly  := ⟨.poly 0, .poly 1, .poly 2, .poly 3,
     .poly 4, .poly 5, .poly 6, .poly 7,
     .poly 8, .poly 9, .poly 10, .poly 11,
     .poly 12, .poly 13, .poly 14, .poly 15,
     .poly 16, .poly 17, .poly 18, .poly 19,
     .poly 20, .poly 21, .poly 22, .poly 23,
     .poly 24, .poly 25, .poly 26, .poly 27,
     .poly 28, .poly 29, .poly 30, .poly 31⟩
    gprs  := ⟨.gpr0 0#5 0#64, .gpr0 1#5 0#64, .gpr0 2#5 0#64, .gpr0 3#5 0#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 6#5 0#64, .gpr0 7#5 0#64,
     .gpr0 8#5 0#64, .gpr0 9#5 0#64, .gpr0 10#5 0#64, .gpr0 11#5 0#64,
     .gpr0 12#5 0#64, .gpr0 13#5 0#64, .gpr0 14#5 0#64, .gpr0 15#5 0#64,
     .gpr0 16#5 0#64, .gpr0 17#5 0#64, .gpr0 18#5 0#64, .gpr0 19#5 0#64,
     .gpr0 20#5 0#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .gpr0 27#5 0#64,
     .gpr0 28#5 0#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

@[expose] def symDot1InitEnd : SymState :=
  { vregs := ⟨.const 0x0000#16, .const 0x0000#16, .vreg0 2, .vreg0 3,
     .vreg0 4, .vreg0 5, .vreg0 6, .vreg0 7,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .vreg0 16, .vreg0 17, .vreg0 18, .vreg0 19,
     .vreg0 20, .vreg0 21, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16⟩
    spill := ⟨.spill0 0, .spill0 1, .spill0 2, .spill0 3,
     .spill0 4, .spill0 5, .spill0 6, .spill0 7,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .spill0 21, .spill0 22, .spill0 23,
     .spill0 24, .spill0 25, .spill0 26, .spill0 27,
     .spill0 28, .spill0 29, .spill0 30, .spill0 31,
     .spill0 32, .spill0 33, .spill0 34, .spill0 35,
     .spill0 36, .spill0 37, .spill0 38, .spill0 39⟩
    poly  := ⟨.const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16,
     .const 0x0000#16, .const 0x0000#16, .const 0x0000#16, .const 0x0000#16⟩
    gprs  := ⟨.gpr0 0#5 0#64, .gpr0 1#5 0#64, .gpr0 2#5 0#64, .gpr0 3#5 0#64,
     .gpr0 4#5 0#64, .gpr0 5#5 0#64, .gpr0 6#5 0#64, .gpr0 7#5 0#64,
     .gpr0 8#5 0#64, .gpr0 9#5 0#64, .gpr0 10#5 0#64, .gpr0 11#5 64#64,
     .const64 62209#64, .const64 3329#64, .gpr0 14#5 2144#64, .gpr0 15#5 0#64,
     .gpr0 16#5 0#64, .gpr0 17#5 0#64, .gpr0 18#5 0#64, .gpr0 19#5 0#64,
     .gpr0 20#5 0#64, .gpr0 21#5 0#64, .gpr0 22#5 0#64, .gpr0 23#5 0#64,
     .gpr0 24#5 0#64, .gpr0 25#5 0#64, .gpr0 26#5 0#64, .gpr0 27#5 0#64,
     .gpr0 28#5 0#64, .gpr0 29#5 0#64, .gpr0 30#5 0#64⟩ }

theorem run_dot1_init : runSymRange cfgDot1Init 1636 81 symDot1InitStart = some symDot1InitEnd :=
  runSymRange_of_fast (by rfl_kernel)

end LibsignalBinary.Proofs.HookDischarge.CryptoMlKem.Mlkem1024.Decaps.Dot1InitSym
