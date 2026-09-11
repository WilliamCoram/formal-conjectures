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

import FormalConjecturesTest.Leopoldts.Mihailescu

/-!
# Mihăilescu's form and the `p`-adic-relation form

**Deprecated.** `Leopoldt.Mihailescu.defect_eq_zero_iff_forall_isPadicRelation`, split off
`FormalConjecturesTest/Leopoldts/Mihailescu.lean`: a corollary that `leopoldt_conjecture_tfae`
subsumes and that nothing uses.
-/

open NumberField NumberField.Units

open scoped NumberField

namespace Leopoldt.Mihailescu

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/-- Mihăilescu's formulation is also equivalent to the `p`-adic-relation form, by
`zpRank_iff`. -/
@[category API, AMS 11]
theorem defect_eq_zero_iff_forall_isPadicRelation :
    defect K p = 0 ↔
      ∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
        ∀ a : Fin (rank K) → ℤ_[p], IsPadicRelation K p ε a → a = 0 :=
  (defect_eq_zero_iff_finrank K p).trans (zpRank_iff K p)

end Leopoldt.Mihailescu
