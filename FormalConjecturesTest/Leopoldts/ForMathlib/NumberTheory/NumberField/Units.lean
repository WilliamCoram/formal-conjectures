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
module
public import Mathlib
public import FormalConjecturesTest.Leopoldts.ForMathlib.Algebra.Group.Zpow

/-!
# Congruences and rank for the units of a number field

Facts about `(𝓞 K)ˣ` used by the Leopoldt equivalence proofs: powers of a unit that is `1`
modulo `p`, coercions of products of powers, and the passage between a family of units of maximal
rank (`NumberField.Units.IsMaxRank`) and the fundamental system `fundSystem K`.

Reduction of units modulo an element (`Leopoldt.redUnits`), the fact that a fixed power of every
unit is `1` modulo `p` (`Leopoldt.exists_pow_sub_one_dvd`) and `Leopoldt.isMaxRank_pow` are part
of `FormalConjectures/Wikipedia/LeopoldtConjecture.lean` itself.

Staging area: these are stated in the generality the Leopoldt files need and are kept in the
`Leopoldt` namespace. Narrow the imports and pick final namespaces before upstreaming.
-/

@[expose] public section

open Filter IsDedekindDomain NumberField NumberField.Units

open scoped NumberField

namespace Leopoldt

variable {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

omit [NumberField K] [Fact p.Prime] in
/-- A unit which is `1` modulo `p` is `1` modulo `p ^ (n + 1)` after raising to the `p ^ n`-th
power. -/
lemma pow_pow_sub_one_dvd {u : (𝓞 K)ˣ} (hu : (p : 𝓞 K) ∣ (u : 𝓞 K) - 1) (n : ℕ) :
    (p : 𝓞 K) ^ (n + 1) ∣ ((u ^ p ^ n : (𝓞 K)ˣ) : 𝓞 K) - 1 := by
  simpa using dvd_sub_pow_of_dvd_sub hu n

lemma coe_prod_pow (ε : Fin (rank K) → (𝓞 K)ˣ) (k : Fin (rank K) → ℕ) :
    (∏ i, (ε i : K) ^ k i : K) = (((∏ i, ε i ^ k i : (𝓞 K)ˣ) : 𝓞 K) : K) := by
  simp [map_prod]

omit [NumberField K] in
lemma coe_units_zpow (u : (𝓞 K)ˣ) (n : ℤ) : ((u ^ n : (𝓞 K)ˣ) : K) = (u : K) ^ n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩ <;> simp

/-- If a family of units of maximal rank is expressed in terms of the fundamental system by an
integer matrix `C`, then `C` is invertible over `ℚ`. -/
lemma det_ne_zero_of_isMaxRank {ε : Fin (rank K) → (𝓞 K)ˣ} (hε : IsMaxRank ε)
    (C : Matrix (Fin (rank K)) (Fin (rank K)) ℤ) (hC : ∀ i, ε i = ∏ j, fundSystem K j ^ C i j) :
    C.det ≠ 0 := by
  classical
  set B := basisOfIsMaxRank (isMaxRank_fundSystem K) with hB
  have h1 : ∀ i, logEmbedding K (Additive.ofMul (ε i)) = ∑ j, (C i j : ℝ) • B j := by
    intro i
    rw [hC, ofMul_prod, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [ofMul_zpow, map_zsmul, ← Int.cast_smul_eq_zsmul ℝ, hB, basisOfIsMaxRank_apply]
  have h2 : LinearIndependent ℝ ((Int.castRingHom ℝ).mapMatrix C).row := by
    have := hε.map' B.equivFun.toLinearMap (LinearEquiv.ker _)
    have hfun : (⇑B.equivFun.toLinearMap ∘ fun i ↦ logEmbedding K (Additive.ofMul (ε i))) =
        ((Int.castRingHom ℝ).mapMatrix C).row := by
      ext i j
      rw [Function.comp_apply, h1, LinearEquiv.coe_coe, Module.Basis.equivFun_apply,
        Module.Basis.repr_sum_self]
      simp
    rwa [hfun] at this
  have h4 : ((Int.castRingHom ℝ).mapMatrix C).det ≠ 0 := isUnit_iff_ne_zero.1
    ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 h2))
  intro h
  rw [← RingHom.map_det, h, map_zero] at h4
  exact h4 rfl

lemma prod_pow_eq_prod_fundSystem (ε : Fin (rank K) → (𝓞 K)ˣ)
    (C : Matrix (Fin (rank K)) (Fin (rank K)) ℤ) (hC : ∀ i, ε i = ∏ j, fundSystem K j ^ C i j)
    (k : Fin (rank K) → ℕ) :
    ∏ i, ε i ^ k i = ∏ j, fundSystem K j ^ Matrix.vecMul (fun i ↦ (k i : ℤ)) C j := by
  simp_rw [hC, ← Finset.prod_pow, Matrix.vecMul, dotProduct, zpow_sum_eq_prod]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ ↦ Finset.prod_congr rfl fun i _ ↦ ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm]

end Leopoldt
