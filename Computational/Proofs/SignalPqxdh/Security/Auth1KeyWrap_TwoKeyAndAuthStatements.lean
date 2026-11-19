/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
import Computational.Proofs.SignalPqxdh.TwoKeyAndAuthStatements
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-key `Auth` game experiment

One-key (`pqxdhAuthImpl1KeyG`) counterparts `pqxdhAuthExpCore1Key` and `pqxdhAuthExp1Key` of the
Game 2 authentication experiment in `TwoKeyAndAuthStatements`.
-/

public section

set_option autoImplicit false

namespace SignalPqxdh

open OracleComp OracleSpec ENNReal

end SignalPqxdh

namespace SignalPqxdh.Costed

open _root_.ReductionDsl OracleSpec OracleComp

end SignalPqxdh.Costed

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.ReductionDsl (Ty CostedReduction TwoStageCostedReduction Mid)
open SignalPqxdh.Costed

end SignalPqxdh.Security

namespace SignalPqxdh

end SignalPqxdh

namespace SignalPqxdh.Costed

end SignalPqxdh.Costed

namespace SignalPqxdh.Security.Costed

end SignalPqxdh.Security.Costed
