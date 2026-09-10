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

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Topology.Algebra.Module.Equiv

@[expose] public noncomputable section

/-!
# The invariant differential of a Weierstrass curve as a 1-form on the plane

Let $W$ be a Weierstrass curve $y^2 + a_1 xy + a_3 y = x^3 + a_2 x^2 + a_4 x + a_6$ over a field
$F$. Its invariant differential is $\omega = \frac{dx}{2y + a_1 x + a_3}$. This file records the
data needed to integrate $\omega$ along paths in the affine plane:

* `WeierstrassCurve.affineNonTwoTorsion`: the affine points $(x, y)$ of $W$ with
  $2y + a_1 x + a_3 \neq 0$, that is, the affine points that are not of order two. On this set
  $x$ is a local coordinate and $\omega$ is given by the formula above.
* `WeierstrassCurve.invariantDifferential`: the 1-form $\omega$ on $F \times F$, as the map
  $(x, y) \mapsto \frac{1}{2y + a_1 x + a_3} \, dx$ into the continuous linear maps
  $F \times F \to F$ (junk where the denominator vanishes).
* `WeierstrassCurve.shortModel` and `WeierstrassCurve.toShortModel`: the short model
  $Y^2 = X^3 - \frac{c_4}{48} X - \frac{c_6}{864}$ of $W$ and the change of variables
  $(x, y) \mapsto (x + \frac{b_2}{12}, y + \frac{a_1 x + a_3}{2})$ onto it, an affine bijection
  of the plane which preserves the invariant differential
  (`WeierstrassCurve.invariantDifferential_shortModel_comp`): $dX = dx$ and
  $2Y = 2y + a_1 x + a_3$.

Completing the square, $(2y + a_1 x + a_3)^2 = 4x^3 + b_2 x^2 + 2 b_4 x + b_6$ is the 2-division
polynomial `WeierstrassCurve.Ψ₂Sq` (`WeierstrassCurve.eval_Ψ₂Sq_eq_sq_of_equation`), and the
substitution $x = X - b_2 / 12$ turns it into $4X^3 - \frac{c_4}{12} X - \frac{c_6}{216}$
(`WeierstrassCurve.eval_Ψ₂Sq_sub`).

*References:*
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, Chapter III
    §1, https://link.springer.com/book/10.1007/978-0-387-09494-6
- [LMFDB](https://www.lmfdb.org/knowledge/show/ec.q.period_lattice), knowl `ec.q.period_lattice`
-/

open Polynomial Set

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Completing the square: at an affine point of `W`, $(2y + a_1 x + a_3)^2 = \Psi_2^2(x)$. -/
lemma eval_Ψ₂Sq_eq_sq_of_equation {x y : R} (h : W.toAffine.Equation x y) :
    W.Ψ₂Sq.eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X, b₂, b₄, b₆]
  linear_combination (-4 : R) * h

/-- The affine points of `W` which are not of order two: those with $2y + a_1 x + a_3 \neq 0$.
On this set the invariant differential is $dx / (2y + a_1 x + a_3)$. -/
def affineNonTwoTorsion : Set (R × R) :=
  {p | W.toAffine.Equation p.1 p.2 ∧ 2 * p.2 + W.a₁ * p.1 + W.a₃ ≠ 0}

lemma mem_affineNonTwoTorsion {p : R × R} : p ∈ W.affineNonTwoTorsion ↔
    W.toAffine.Equation p.1 p.2 ∧ 2 * p.2 + W.a₁ * p.1 + W.a₃ ≠ 0 :=
  Iff.rfl

end CommRing

section Field

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/-- The short Weierstrass model $Y^2 = X^3 - \frac{c_4}{48} X - \frac{c_6}{864}$ of `W`. -/
def shortModel : WeierstrassCurve F where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -W.c₄ / 48
  a₆ := -W.c₆ / 864

/-- The change of variables $(x, y) \mapsto (x + \frac{b_2}{12}, y + \frac{a_1 x + a_3}{2})$ from
`W` onto its short model. -/
def toShortModel (p : F × F) : F × F :=
  (p.1 + W.b₂ / 12, p.2 + (W.a₁ * p.1 + W.a₃) / 2)

@[simp]
lemma toShortModel_apply (p : F × F) :
    W.toShortModel p = (p.1 + W.b₂ / 12, p.2 + (W.a₁ * p.1 + W.a₃) / 2) :=
  rfl

variable [NeZero (2 : F)] [NeZero (3 : F)]

/-- The substitution $x = X - b_2 / 12$ turns the 2-division polynomial into the depressed cubic
$4X^3 - g_2 X - g_3$ with $g_2 = c_4 / 12$ and $g_3 = c_6 / 216$. -/
lemma eval_Ψ₂Sq_sub (x : F) :
    W.Ψ₂Sq.eval (x - W.b₂ / 12) = 4 * x ^ 3 - W.c₄ / 12 * x - W.c₆ / 216 := by
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have h3 : (3 : F) ≠ 0 := NeZero.ne 3
  have h12 : (12 : F) ≠ 0 := by
    rw [show (12 : F) = 2 * 2 * 3 by norm_num]
    exact mul_ne_zero (mul_ne_zero h2 h2) h3
  have h216 : (216 : F) ≠ 0 := by
    rw [show (216 : F) = 2 * 2 * 2 * 3 * 3 * 3 by norm_num]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h3) h3) h3
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X, c₄, c₆, b₄]
  field_simp
  ring

lemma toShortModel_mem_affineNonTwoTorsion_iff {p : F × F} :
    W.toShortModel p ∈ W.shortModel.affineNonTwoTorsion ↔ p ∈ W.affineNonTwoTorsion := by
  have h2 : (2 : F) ≠ 0 := NeZero.ne 2
  have h3 : (3 : F) ≠ 0 := NeZero.ne 3
  have h12 : (12 : F) ≠ 0 := by
    rw [show (12 : F) = 2 * 2 * 3 by norm_num]; exact mul_ne_zero (mul_ne_zero h2 h2) h3
  have h48 : (48 : F) ≠ 0 := by
    rw [show (48 : F) = 2 * 2 * 2 * 2 * 3 by norm_num]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) h2) h2) h3
  have h864 : (864 : F) ≠ 0 := by
    rw [show (864 : F) = 2 * 2 * 2 * 2 * 2 * 3 * 3 * 3 by norm_num]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero h2 h2) h2) h2) h2) h3) h3) h3
  have hdiff : (p.2 + (W.a₁ * p.1 + W.a₃) / 2) ^ 2
        + W.shortModel.a₁ * (p.1 + W.b₂ / 12) * (p.2 + (W.a₁ * p.1 + W.a₃) / 2)
        + W.shortModel.a₃ * (p.2 + (W.a₁ * p.1 + W.a₃) / 2)
        - ((p.1 + W.b₂ / 12) ^ 3 + W.shortModel.a₂ * (p.1 + W.b₂ / 12) ^ 2
          + W.shortModel.a₄ * (p.1 + W.b₂ / 12) + W.shortModel.a₆)
      = p.2 ^ 2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2
        - (p.1 ^ 3 + W.a₂ * p.1 ^ 2 + W.a₄ * p.1 + W.a₆) := by
    simp only [shortModel, c₄, c₆, b₂, b₄, b₆]
    field_simp
    ring
  have hden : 2 * (p.2 + (W.a₁ * p.1 + W.a₃) / 2) + W.shortModel.a₁ * (p.1 + W.b₂ / 12)
      + W.shortModel.a₃ = 2 * p.2 + W.a₁ * p.1 + W.a₃ := by
    have hhalf : (2 : F) * ((W.a₁ * p.1 + W.a₃) / 2) = W.a₁ * p.1 + W.a₃ := by field_simp
    simp only [shortModel]
    linear_combination hhalf
  simp only [mem_affineNonTwoTorsion, toShortModel_apply, WeierstrassCurve.Affine.equation_iff,
    WeierstrassCurve.toAffine, hden]
  refine and_congr ?_ Iff.rfl
  rw [← sub_eq_zero, ← sub_eq_zero (a := p.2 ^ 2 + W.a₁ * p.1 * p.2 + W.a₃ * p.2), hdiff]


/-- The change of variables to the short model is a bijection from the non-2-torsion locus of `W`
onto that of its short model. -/
lemma image_toShortModel_affineNonTwoTorsion :
    W.toShortModel '' W.affineNonTwoTorsion = W.shortModel.affineNonTwoTorsion := by
  ext q
  refine ⟨?_, fun hq ↦ ?_⟩
  · rintro ⟨p, hp, rfl⟩
    exact W.toShortModel_mem_affineNonTwoTorsion_iff.mpr hp
  · have hqp : W.toShortModel (q.1 - W.b₂ / 12,
        q.2 - (W.a₁ * (q.1 - W.b₂ / 12) + W.a₃) / 2) = q := by
      ext <;> simp [toShortModel]
    exact ⟨_, W.toShortModel_mem_affineNonTwoTorsion_iff.mp (by rw [hqp]; exact hq), hqp⟩

end Field

section NormedField

variable {F : Type*} [NontriviallyNormedField F] (W : WeierstrassCurve F)

/-- The invariant differential $\omega = dx / (2y + a_1 x + a_3)$ of `W`, as a 1-form on the
plane $F \times F$; it is $0$ at points where $2y + a_1 x + a_3 = 0$. -/
def invariantDifferential (p : F × F) : (F × F) →L[F] F :=
  (2 * p.2 + W.a₁ * p.1 + W.a₃)⁻¹ • ContinuousLinearMap.fst F F F

@[simp]
lemma invariantDifferential_apply (p v : F × F) :
    W.invariantDifferential p v = v.1 / (2 * p.2 + W.a₁ * p.1 + W.a₃) := by
  simp [invariantDifferential, div_eq_inv_mul]

lemma continuousOn_invariantDifferential :
    ContinuousOn W.invariantDifferential W.affineNonTwoTorsion := by
  show ContinuousOn (fun p : F × F ↦ (2 * p.2 + W.a₁ * p.1 + W.a₃)⁻¹ •
    ContinuousLinearMap.fst F F F) _
  exact ContinuousOn.smul (ContinuousOn.inv₀ (by fun_prop)
    fun p hp ↦ (W.mem_affineNonTwoTorsion.mp hp).2) continuousOn_const

variable [NeZero (2 : F)]

/-- The linear part $(x, y) \mapsto (x, y + \frac{a_1}{2} x)$ of the change of variables
`WeierstrassCurve.toShortModel`. -/
def toShortModelLinear : (F × F) ≃L[F] (F × F) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst F F F).prod
      (ContinuousLinearMap.snd F F F + (W.a₁ / 2) • ContinuousLinearMap.fst F F F))
    ((ContinuousLinearMap.fst F F F).prod
      (ContinuousLinearMap.snd F F F - (W.a₁ / 2) • ContinuousLinearMap.fst F F F))
    (fun p ↦ by ext <;> simp) (fun p ↦ by ext <;> simp)

omit [NeZero (2 : F)] in
@[simp]
lemma toShortModelLinear_apply (p : F × F) :
    W.toShortModelLinear p = (p.1, p.2 + W.a₁ / 2 * p.1) := by
  ext <;> simp [toShortModelLinear]

omit [NeZero (2 : F)] in
lemma toShortModel_eq (p : F × F) :
    W.toShortModel p = W.toShortModelLinear p + (W.b₂ / 12, W.a₃ / 2) := by
  refine Prod.ext rfl ?_
  simp only [toShortModel, toShortModelLinear_apply, Prod.snd_add]
  ring

/-- The change of variables to the short model preserves the invariant differential: the pullback
of $dX / (2Y)$ along `toShortModel` is $dx / (2y + a_1 x + a_3)$. -/
lemma invariantDifferential_shortModel_comp (p : F × F) :
    (W.shortModel.invariantDifferential (W.toShortModel p)).comp
      (W.toShortModelLinear : (F × F) →L[F] (F × F)) = W.invariantDifferential p := by
  have hhalf : (2 : F) * ((W.a₁ * p.1 + W.a₃) / 2) = W.a₁ * p.1 + W.a₃ := by
    field_simp
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [ContinuousLinearMap.comp_apply, invariantDifferential_apply, toShortModel_apply,
    shortModel]
  congr 1
  linear_combination hhalf

end NormedField

end WeierstrassCurve

end
