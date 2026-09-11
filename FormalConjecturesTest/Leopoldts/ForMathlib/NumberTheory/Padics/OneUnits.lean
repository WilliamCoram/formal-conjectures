/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import FormalConjecturesForMathlib.NumberTheory.Padics.OneUnits

/-!
# `p`-adic powers of principal units: two additions

Two facts about the `ℤ_[p]`-module `Additive (oneUnits K)` of
`FormalConjecturesForMathlib/NumberTheory/Padics/OneUnits.lean` that the equivalence proofs use
and that file does not state:

* `OneUnits.intCast_smul`: integer `p`-adic powers are ordinary powers;
* the `T2Space` instance on `Additive (oneUnits K)`, which makes limits in
  `U₁ = ∏_{𝔭 ∣ p} U_{1, 𝔭}` unique.
-/

@[expose] public section

namespace OneUnits

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [Fact (‖((p : ℕ) : K)‖ < 1)]

theorem intCast_smul (n : ℤ) (u : Additive (oneUnits K)) : (n : ℤ_[p]) • u = n • u := by
  refine ext_of_coe ?_
  rw [coe_smul, zpPow_intCast (mem_oneUnits_iff.1 u.toMul.2), toMul_zsmul]
  push_cast
  ring

instance : T2Space (Additive (oneUnits K)) := inferInstanceAs (T2Space (oneUnits K))

end OneUnits
