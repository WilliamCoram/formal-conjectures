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

import FormalConjecturesTest.Leopoldts.All
import FormalConjecturesTest.Leopoldts.old.ForMathlib.LinearAlgebra.Matrix.Determinant

/-!
# The regulator form for totally real fields

**Deprecated.** Nothing in `FormalConjecturesTest/Leopoldts` uses this file. It keeps Leopoldt's
original form $R_p(K) \neq 0$ for totally real $K$, together with its proof of equivalence with
the other forms, from before FC#5497: the totally real regulator form is not among the statements
of `FormalConjectures/Wikipedia/LeopoldtConjecture.lean`.

For totally real $K$ the matrix `Leopoldt.iwasawaLogMatrix` has $r + 1 = [K : \mathbb{Q}]$
columns and its rows sum to zero (`sum_iwasawaLogMatrix`), so deleting any one column gives a
square matrix whose determinant is Washington's $p$-adic regulator `Leopoldt.padicRegulator`,
well defined up to sign (`padicRegulator_eq_or_eq_neg`).

This file proves $R_p(K) \neq 0$ equivalent to the full-rank form (`padicRegulator_ne_zero_iff`),
to the elementary form (`leopoldtConjecture_iff_padicRegulator_ne_zero`), to
`leopoldt_conjecture` (`leopoldt_conjecture_iff_padicRegulator_ne_zero`) and to Mihăilescu's form
(`Mihailescu.defect_eq_zero_iff_padicRegulator_ne_zero`).
-/

open Filter IsDedekindDomain NumberField NumberField.Units

open scoped NumberField

namespace PadicIwasawaLog

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [CharZero K]

/-- Roots of unity have Iwasawa logarithm `0`. -/
theorem iwasawaLog_of_pow_eq_one (h3 : ‖((p : ℕ) : K)‖ < 1) {ζ : K} {N : ℕ} (hN : 0 < N)
    (hζ : ζ ^ N = 1) : iwasawaLog p ζ = 0 := by
  have h : ‖ζ ^ N / ((p : ℕ) : K) ^ (0 : ℤ) - 1‖ < 1 := by simp [hζ]
  rw [iwasawaLog_eq_div h3 hN h]
  simp [hζ]

end PadicIwasawaLog

namespace Leopoldt

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/--
For totally real $K$ the embeddings $K \to \mathbb{C}_p$ other than a given one $\sigma_0$ are
$[K : \mathbb{Q}] - 1 = r_1 - 1 = r$ in number.
-/
@[category API, AMS 11]
theorem card_ne_eq_rank [IsTotallyReal K] (σ₀ : K →+* ℂ_[p]) :
    Nat.card {σ : K →+* ℂ_[p] // σ ≠ σ₀} = rank K := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Embeddings.card K ℂ_[p],
    IsTotallyReal.finrank, rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]

/-- For totally real `K`, the embeddings `K → ℂ_p` other than `σ₀` can be indexed by
`Fin (rank K)`. -/
@[category API, AMS 11]
theorem nonempty_equiv_fin_rank [IsTotallyReal K] (σ₀ : K →+* ℂ_[p]) :
    Nonempty (Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) := by
  classical
  exact ⟨(Fintype.equivFinOfCardEq
    (by rw [← Nat.card_eq_fintype_card, card_ne_eq_rank K p σ₀])).symm⟩

/--
The **$p$-adic regulator** of a totally real number field $K$ (Washington, §5.5). Let
$\varepsilon_1, \dots, \varepsilon_r$ be the fundamental system of units `fundSystem K` and let
$\sigma_0$ be one of the $r + 1 = [K : \mathbb{Q}]$ embeddings $K \to \mathbb{C}_p$. Then
$$R_p(K) = \det\big(\log_p \sigma(\varepsilon_i)\big)_{i,\, \sigma \neq \sigma_0},$$
where the columns $\sigma \neq \sigma_0$ are indexed by `Fin (rank K)` through `e`. Up to sign
the value depends neither on $\sigma_0$ nor on `e` (`padicRegulator_eq_or_eq_neg`), because the
rows of `iwasawaLogMatrix K p` sum to zero (`sum_iwasawaLogMatrix`). The definition makes sense
for any `K`, but an equivalence `e` exists only when `K` is totally real
(`nonempty_equiv_fin_rank`).
-/
noncomputable def padicRegulator (σ₀ : K →+* ℂ_[p])
    (e : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) : ℂ_[p] :=
  ((iwasawaLogMatrix K p).submatrix id fun j ↦ (e j : K →+* ℂ_[p])).det

/--
**Leopoldt's conjecture for totally real fields, regulator form** [Washington, §5.5]: the
$p$-adic regulator $R_p(K)$ of a totally real number field $K$ does not vanish.

By `padicRegulator_eq_or_eq_neg` the statement does not depend on the choice of the omitted
embedding $\sigma_0$ or of the ordering `e`, and by `leopoldt_conjecture_iff_padicRegulator_ne_zero`
it is equivalent to `leopoldt_conjecture` for totally real `K`.
-/
@[category research open, AMS 11]
theorem leopoldt_conjecture.variants.padicRegulator_ne_zero [IsTotallyReal K]
    (σ₀ : K →+* ℂ_[p]) (e : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) :
    Leopoldt.padicRegulator K p σ₀ e ≠ 0 := by
  sorry

/--
Each row of `iwasawaLogMatrix K p` sums to zero:
$\sum_\sigma \log_p \sigma(\varepsilon_i) = \log_p N_{K/\mathbb{Q}}(\varepsilon_i)
= \log_p(\pm 1) = 0$.
-/
@[category API, AMS 11]
theorem sum_iwasawaLogMatrix (i : Fin (rank K)) : ∑ σ, iwasawaLogMatrix K p i σ = 0 := by
  have hlog : ∀ σ : K →+* ℂ_[p], PadicIwasawaLog.HasIwasawaLog p (σ (fundSystem K i : K)) := fun σ ↦
    PadicIwasawaLog.PadicComplex.hasIwasawaLog ((map_ne_zero σ).2 (coe_ne_zero _))
  have hprod : ∏ σ : K →+* ℂ_[p], σ (fundSystem K i : K) =
      algebraMap ℚ ℂ_[p] (Algebra.norm ℚ (fundSystem K i : K)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ_[p]]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ_[p]) _ _ fun σ ↦ rfl
  have hnorm : |Algebra.norm ℚ (fundSystem K i : K)| = 1 := NumberField.Units.norm K _
  have hsq : (∏ σ : K →+* ℂ_[p], σ (fundSystem K i : K)) ^ 2 = 1 := by
    rw [hprod, ← map_pow, ← sq_abs, hnorm, one_pow, map_one]
  calc ∑ σ, iwasawaLogMatrix K p i σ
      = PadicIwasawaLog.iwasawaLog p (∏ σ : K →+* ℂ_[p], σ (fundSystem K i : K)) :=
        (PadicIwasawaLog.iwasawaLog_prod PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one
          fun σ _ ↦ hlog σ).symm
    _ = 0 := PadicIwasawaLog.iwasawaLog_of_pow_eq_one
          PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one two_pos hsq

/-- The $p$-adic regulator is well defined up to sign. -/
@[category API, AMS 11]
theorem padicRegulator_eq_or_eq_neg (σ₀ σ₁ : K →+* ℂ_[p])
    (e₀ : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀})
    (e₁ : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₁}) :
    padicRegulator K p σ₀ e₀ = padicRegulator K p σ₁ e₁ ∨
      padicRegulator K p σ₀ e₀ = -padicRegulator K p σ₁ e₁ :=
  Matrix.det_submatrix_ne_eq_or_eq_neg (iwasawaLogMatrix K p) (sum_iwasawaLogMatrix K p) e₀ e₁

/-- The $p$-adic regulator is nonzero if and only if `iwasawaLogMatrix K p` has full rank $r$. -/
@[category API, AMS 11]
theorem padicRegulator_ne_zero_iff (σ₀ : K →+* ℂ_[p])
    (e : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) :
    padicRegulator K p σ₀ e ≠ 0 ↔ (iwasawaLogMatrix K p).rank = rank K := by
  rw [padicRegulator, Matrix.det_submatrix_ne_ne_zero_iff (iwasawaLogMatrix K p)
    (sum_iwasawaLogMatrix K p) e, Fintype.card_fin]

/--
For totally real $K$, the elementary form of Leopoldt's conjecture holds if and only if the
$p$-adic regulator does not vanish. This is `leopoldtConjecture_iff_rank` composed with
`padicRegulator_ne_zero_iff`.
-/
@[category API, AMS 11]
theorem leopoldtConjecture_iff_padicRegulator_ne_zero [IsTotallyReal K] (σ₀ : K →+* ℂ_[p])
    (e : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) :
    LeopoldtConjecture K p ↔ padicRegulator K p σ₀ e ≠ 0 :=
  (leopoldtConjecture_iff_rank K p).trans (padicRegulator_ne_zero_iff K p σ₀ e).symm

/-- For totally real `K`, the statement of `leopoldt_conjecture` holds iff $R_p(K) \neq 0$. -/
@[category API, AMS 11]
theorem leopoldt_conjecture_iff_padicRegulator_ne_zero [IsTotallyReal K] (σ₀ : K →+* ℂ_[p])
    (e : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) :
    Module.rank ℤ_[p] (closureE₁ K p) = rank K ↔ padicRegulator K p σ₀ e ≠ 0 :=
  (leopoldt_conjecture_iff_elementary K p).trans
    (leopoldtConjecture_iff_padicRegulator_ne_zero K p σ₀ e)

end Leopoldt

namespace Leopoldt.Mihailescu

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/--
For totally real `K`, Mihăilescu's Leopoldt defect vanishes exactly when Washington's $p$-adic
regulator $R_p(K)$ is nonzero. This is the form in which [Mihăilescu, Theorem 1] states the
conjecture ("the $p$-adic regulator of a number field does not vanish").
-/
@[category API, AMS 11]
theorem defect_eq_zero_iff_padicRegulator_ne_zero [IsTotallyReal K] (σ₀ : K →+* ℂ_[p])
    (e : Fin (rank K) ≃ {σ : K →+* ℂ_[p] // σ ≠ σ₀}) :
    defect K p = 0 ↔ padicRegulator K p σ₀ e ≠ 0 :=
  (defect_eq_zero_iff K p).trans (leopoldt_conjecture_iff_padicRegulator_ne_zero K p σ₀ e)

end Leopoldt.Mihailescu
