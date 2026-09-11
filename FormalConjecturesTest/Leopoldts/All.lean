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
import FormalConjecturesTest.Leopoldts.PadicRegulator

/-!
# All formulations of Leopoldt's conjecture agree

`FormalConjectures/Wikipedia/LeopoldtConjecture.lean` states Leopoldt's conjecture for a number
field `K` and a prime `p` in five ways. This file proves them equivalent
(`leopoldt_conjecture_tfae`):

1. `leopoldt_conjecture`, Wikipedia's form:
   $\operatorname{rank}_{\mathbb{Z}_p} \overline{E_1} = r_1 + r_2 - 1$;
2. `leopoldt_conjecture.variants.padicRegulator`: the matrix `logMatrix K p ε` of $p$-adic
   logarithms of any family `ε` of units of maximal rank lying in $E_1$ has full rank;
3. `leopoldt_conjecture.variants.padicRelation`: every $p$-adic relation among such a family is
   trivial;
4. `leopoldt_conjecture.variants.elementary`, for every `N`: congruences modulo
   $p^M \mathcal{O}_K$ force divisibility of the exponents;
5. `leopoldt_conjecture.variants.mihailescu`: Mihăilescu's Leopoldt defect vanishes.

`leopoldt_conjecture.variants.abelian` is `leopoldt_conjecture` under the extra hypothesis that
`K / ℚ` is abelian, so there is nothing to prove for it. The `example`s at the end check that the
items of `leopoldt_conjecture_tfae` are the statements of the conjecture file.

None of this needs `p` odd, although [Mihăilescu, §1.1] assumes it: the equivalence of the
formulations is unconditional, and it is only the *proof* of the conjecture for CM fields that
uses oddness.

Where each equivalence is proved:

| Equivalence | File | Result |
| --- | --- | --- |
| (1) ↔ (3) | `ZpRank` | `zpRank_iff`, `rank_closureE₁_eq_iff_finrank` |
| (3) ↔ (4) | `Elementary` | `leopoldtConjecture_iff` |
| (2) ↔ (4) | `PadicRegulator` | `forall_rank_logMatrix_iff` |
| (5) ↔ (1) | `Mihailescu` | `Mihailescu.defect_eq_zero_iff` |

The supporting mathematics is in `FormalConjecturesTest/Leopoldts/ForMathlib`. Code that these
proofs no longer use is kept in `FormalConjecturesTest/Leopoldts/old`, to be deprecated.
-/

open NumberField NumberField.Units

open scoped NumberField

namespace Leopoldt

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/-- Wikipedia's form and the `p`-adic-relation form agree. -/
@[category API, AMS 11]
theorem leopoldt_conjecture_iff_padicRelation :
    Module.rank ℤ_[p] (closureE₁ K p) = rank K ↔
      ∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
        ∀ a : Fin (rank K) → ℤ_[p], IsPadicRelation K p ε a → a = 0 :=
  (rank_closureE₁_eq_iff_finrank K p).trans (zpRank_iff K p)

/-- Wikipedia's form and the elementary form agree. -/
@[category API, AMS 11]
theorem leopoldt_conjecture_iff_elementary :
    Module.rank ℤ_[p] (closureE₁ K p) = rank K ↔
      ∀ N : ℕ, ∃ M : ℕ, ∀ n : Fin (rank K) → ℤ,
        (p : 𝓞 K) ^ M ∣ ((∏ i, fundSystem K i ^ n i : (𝓞 K)ˣ) : 𝓞 K) - 1 →
        ∀ i, (p : ℤ) ^ N ∣ n i :=
  (leopoldt_conjecture_iff_padicRelation K p).trans (leopoldtConjecture_iff K p).symm

/-- Wikipedia's form and the $p$-adic regulator form agree. -/
@[category API, AMS 11]
theorem leopoldt_conjecture_iff_padicRegulator :
    Module.rank ℤ_[p] (closureE₁ K p) = rank K ↔
      ∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
        (logMatrix K p ε).rank = rank K :=
  (leopoldt_conjecture_iff_elementary K p).trans (forall_rank_logMatrix_iff K p).symm

/-- Wikipedia's form and Mihăilescu's form agree. -/
@[category API, AMS 11]
theorem leopoldt_conjecture_iff_mihailescu :
    Module.rank ℤ_[p] (closureE₁ K p) = rank K ↔ Mihailescu.defect K p = 0 :=
  (Mihailescu.defect_eq_zero_iff K p).symm

/--
**The five formulations of Leopoldt's conjecture in
`FormalConjectures/Wikipedia/LeopoldtConjecture.lean` are equivalent**: Wikipedia's
$\mathbb{Z}_p$-rank of the closure of $E_1$, the full rank of the matrix of $p$-adic logarithms,
the triviality of every $p$-adic relation among units, the elementary form, and the vanishing of
Mihăilescu's Leopoldt defect.
-/
@[category API, AMS 11]
theorem leopoldt_conjecture_tfae :
    List.TFAE
      [Module.rank ℤ_[p] (closureE₁ K p) = rank K,
       ∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
         (logMatrix K p ε).rank = rank K,
       ∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
         ∀ a : Fin (rank K) → ℤ_[p], IsPadicRelation K p ε a → a = 0,
       ∀ N : ℕ, ∃ M : ℕ, ∀ n : Fin (rank K) → ℤ,
         (p : 𝓞 K) ^ M ∣ ((∏ i, fundSystem K i ^ n i : (𝓞 K)ˣ) : 𝓞 K) - 1 →
         ∀ i, (p : ℤ) ^ N ∣ n i,
       Mihailescu.defect K p = 0] := by
  tfae_have 1 ↔ 2 := leopoldt_conjecture_iff_padicRegulator K p
  tfae_have 1 ↔ 3 := leopoldt_conjecture_iff_padicRelation K p
  tfae_have 1 ↔ 4 := leopoldt_conjecture_iff_elementary K p
  tfae_have 1 ↔ 5 := leopoldt_conjecture_iff_mihailescu K p
  tfae_finish

/- ## The items above are the statements of the conjecture file

Each `example` below type-checks only because its type is, up to unfolding, the statement of the
corresponding theorem of `FormalConjectures/Wikipedia/LeopoldtConjecture.lean`. They pin the list
in `leopoldt_conjecture_tfae` to that file: if a statement there changes, this file stops
compiling. -/

example : Module.rank ℤ_[p] (closureE₁ K p) = rank K := leopoldt_conjecture K p

example [IsAbelianGalois ℚ K] : Module.rank ℤ_[p] (closureE₁ K p) = rank K :=
  leopoldt_conjecture.variants.abelian K p

example : ∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
    (logMatrix K p ε).rank = rank K :=
  leopoldt_conjecture.variants.padicRegulator K p

example : ∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
    ∀ a : Fin (rank K) → ℤ_[p], IsPadicRelation K p ε a → a = 0 :=
  fun ε hmax hone _ ha ↦ leopoldt_conjecture.variants.padicRelation K p ε hmax hone ha

example : ∀ N : ℕ, ∃ M : ℕ, ∀ n : Fin (rank K) → ℤ,
    (p : 𝓞 K) ^ M ∣ ((∏ i, fundSystem K i ^ n i : (𝓞 K)ˣ) : 𝓞 K) - 1 →
    ∀ i, (p : ℤ) ^ N ∣ n i :=
  leopoldt_conjecture.variants.elementary K p

example : Mihailescu.defect K p = 0 := leopoldt_conjecture.variants.mihailescu K p

end Leopoldt
