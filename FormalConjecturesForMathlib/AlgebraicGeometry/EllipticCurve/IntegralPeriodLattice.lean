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

public import FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.InvariantDifferential
public import FormalConjecturesForMathlib.MeasureTheory.Integral.CurveIntegral.Periods
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.Analysis.Complex.Polynomial.Basic

@[expose] public noncomputable section

/-!
# The period lattice of an elliptic curve over ℂ as integrals

Let $W$ be a Weierstrass curve over $\mathbb{C}$ with invariant differential
$\omega = \frac{dx}{2y + a_1 x + a_3}$. Its *periods* are the integrals $\int_\gamma \omega$ over
the closed loops $\gamma$ on $W(\mathbb{C})$; they form the period lattice of $W$. This file
defines the set of periods, `WeierstrassCurve.integralPeriodLattice`, as the integrals of
$\omega$ along the $C^1$ loops in the affine plane which lie on $W$ and avoid the points of order
two, where $x$ fails to be a local coordinate (`curveIntegralPeriods`). Loops through the point at
infinity and through the points of order two are not needed: every period is already the integral
along such a loop (`WeierstrassCurve.integralPeriodLattice_eq` in
`FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.ComplexPeriod`).

The set of periods contains $0$, is stable under negation, and is invariant under the change of
variables to the short model (`WeierstrassCurve.integralPeriodLattice_shortModel`), which preserves
$\omega$.

*References:*
- [LMFDB](https://www.lmfdb.org/knowledge/show/ec.q.period_lattice), knowl `ec.q.period_lattice`
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, Chapter VI §1,
    https://link.springer.com/book/10.1007/978-0-387-09494-6
-/

open MeasureTheory Set
open scoped unitInterval

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℂ)

/-- **The period lattice as integrals**: the set of integrals of the invariant differential
$dx / (2y + a_1 x + a_3)$ along the $C^1$ loops on the affine curve avoiding the points of order
two. -/
def integralPeriodLattice : Set ℂ :=
  curveIntegralPeriods W.invariantDifferential W.affineNonTwoTorsion

/-- A complex number is a period of `W` exactly when it is the integral of the invariant
differential along some $C^1$ loop on the affine curve which avoids the points of order two. -/
lemma mem_integralPeriodLattice_iff {w : ℂ} : w ∈ W.integralPeriodLattice ↔
    ∃ (p : ℂ × ℂ) (γ : Path p p), ContDiffOn ℝ 1 γ.extend I ∧
      range γ ⊆ W.affineNonTwoTorsion ∧ ∫ᶜ x in γ, W.invariantDifferential x = w :=
  Iff.rfl

/-- Over `ℂ` every Weierstrass curve has an affine point which is not of order two. -/
lemma affineNonTwoTorsion_nonempty : W.affineNonTwoTorsion.Nonempty := by
  obtain ⟨x, hx⟩ : ∃ x : ℂ, ¬ W.Ψ₂Sq.IsRoot x :=
    (Polynomial.finite_setOfPred_isRoot (W.Ψ₂Sq_ne_zero (by norm_num))).infinite_compl.nonempty
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (W.Ψ₂Sq.eval x) two_pos
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hx (by simpa [Polynomial.IsRoot] using hs.symm)
  refine ⟨(x, (s - W.a₁ * x - W.a₃) / 2), ?_, ?_⟩
  · rw [Affine.equation_iff]
    simp only [Ψ₂Sq, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, b₂, b₄, b₆] at hs
    simp only [toAffine]
    linear_combination hs / 4
  · rwa [show 2 * ((s - W.a₁ * x - W.a₃) / 2) + W.a₁ * x + W.a₃ = s by ring]

/-- Zero is a period of `W`. -/
lemma zero_mem_integralPeriodLattice : 0 ∈ W.integralPeriodLattice :=
  zero_mem_curveIntegralPeriods W.affineNonTwoTorsion_nonempty

/-- The periods of `W` are stable under negation. -/
lemma neg_mem_integralPeriodLattice {w : ℂ} (hw : w ∈ W.integralPeriodLattice) :
    -w ∈ W.integralPeriodLattice :=
  neg_mem_curveIntegralPeriods hw

/-- The change of variables to the short model preserves the periods. -/
theorem integralPeriodLattice_shortModel :
    W.shortModel.integralPeriodLattice = W.integralPeriodLattice := by
  have himg : W.shortModel.affineNonTwoTorsion =
      (fun p ↦ W.toShortModelLinear p + (W.b₂ / 12, W.a₃ / 2)) '' W.affineNonTwoTorsion := by
    rw [← W.image_toShortModel_affineNonTwoTorsion]
    exact image_congr fun p _ ↦ W.toShortModel_eq p
  simp only [integralPeriodLattice, himg, curveIntegralPeriods_image_add_const]
  congr 1
  funext p
  rw [← W.toShortModel_eq p]
  exact W.invariantDifferential_shortModel_comp p

end WeierstrassCurve

end
