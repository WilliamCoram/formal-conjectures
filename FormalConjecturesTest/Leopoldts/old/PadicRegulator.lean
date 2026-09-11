/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjecturesTest.Leopoldts.PadicRegulator

/-!
# The `p`-adic-relation form and the Iwasawa-logarithm matrix

**Deprecated.** `Leopoldt.forall_isPadicRelation_iff_rank`, split off
`FormalConjecturesTest/Leopoldts/PadicRegulator.lean`: a corollary that
`leopoldt_conjecture_tfae` subsumes and that nothing uses.
-/

open NumberField NumberField.Units

open scoped NumberField

namespace Leopoldt

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/--
The statement of `leopoldt_conjecture.variants.padicRelation` is equivalent to full rank of the
matrix `iwasawaLogMatrix K p` of Iwasawa logarithms of the fundamental system.
-/
@[category API, AMS 11]
theorem forall_isPadicRelation_iff_rank :
    (∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
        ∀ a : Fin (rank K) → ℤ_[p], IsPadicRelation K p ε a → a = 0) ↔
      (iwasawaLogMatrix K p).rank = rank K :=
  (leopoldtConjecture_iff K p).symm.trans (leopoldtConjecture_iff_rank K p)

end Leopoldt
