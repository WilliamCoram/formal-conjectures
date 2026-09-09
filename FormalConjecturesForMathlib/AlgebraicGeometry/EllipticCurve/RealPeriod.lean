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

public import FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.PeriodIntegral
public import FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.PeriodLattice
public import FormalConjecturesForMathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.RealAxis
public import FormalConjecturesForMathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public noncomputable section

/-!
# The two definitions of the real period agree

There are two definitions of the real period of an elliptic curve $E$ over $\mathbb{R}$.

* *From the period lattice.* `WeierstrassCurve.leastRealPeriod` is the least positive element of
  $\Lambda \cap \mathbb{R}$, where $\Lambda$ is the period lattice, the lattice with
  $g_2 = c_4 / 12$ and $g_3 = c_6 / 216$; the real period `WeierstrassCurve.realPeriod` is
  $c_\infty$ times it, where $c_\infty$ is the number of connected components of $E(\mathbb{R})$,
  `WeierstrassCurve.nrRealComponents`.
* *From the invariant differential.* `WeierstrassCurve.leastRealPeriodIntegral` is
  $2 \int_{e_1}^{\infty} dx / \sqrt{4x^3 + b_2 x^2 + 2 b_4 x + b_6}$, the integral of $|\omega|$
  over the identity component of $E(\mathbb{R})$, and the real period
  `WeierstrassCurve.realPeriodIntegral` is $2 \int_{\mathbb{R}} dx / \sqrt{F(x)}$, the integral
  over all of $E(\mathbb{R})$.

This file proves that the two agree, both for the least positive real period
(`WeierstrassCurve.leastRealPeriodIntegral_eq_leastRealPeriod`) and for the real period
(`WeierstrassCurve.realPeriodIntegral_eq_realPeriod`). The latter needs no separate argument for
the two signs of the discriminant: the integral definition already knows that the bounded
component contributes as much as the identity component when $\Delta > 0$, and nothing when
$\Delta < 0$, by `WeierstrassCurve.realPeriodIntegral_of_pos` and
`WeierstrassCurve.realPeriodIntegral_of_neg`.

The bridge between the two is the substitution $x = X - b_2 / 12$, which turns the 2-division
polynomial into the depressed cubic $4X^3 - g_2 X - g_3$ of the period lattice
(`WeierstrassCurve.eval_Ψ₂Sq_sub`, `WeierstrassCurve.leastRealPeriodIntegral_eq_integral_depressed`)
and sends $e_1$ to the largest real root $\wp(\Omega / 2)$ of that cubic
(`WeierstrassCurve.e₁_add_b₂_div_twelve`). Then
`PeriodPair.IsReal.integral_inv_sqrt_eq_half` evaluates the integral as $\Omega / 2$.

*References:*
- [DLMF](https://dlmf.nist.gov/23.6.iv), equations 23.6.34 and 23.6.36
- [Cre1997] John E. Cremona. Algorithms for Modular Elliptic Curves, 2nd edition, Section 3.7,
    https://johncremona.github.io/book/fulltext/index.html
- [Pas2017] Georgios Pastras. Four Lectures on Weierstrass Elliptic Function and Applications in
    Classical and Quantum Mechanics, §3.1 and Appendix A, https://arxiv.org/abs/1706.07371
-/

open MeasureTheory Polynomial Set

namespace WeierstrassCurve

/- ## The depressed cubic -/

/-- The substitution $x = X - b_2 / 12$ turns the 2-division polynomial into the depressed cubic
$4X^3 - g_2 X - g_3$ with $g_2 = c_4 / 12$ and $g_3 = c_6 / 216$, the invariants of the period
lattice. -/
lemma eval_Ψ₂Sq_sub (W : WeierstrassCurve ℝ) (x : ℝ) :
    W.Ψ₂Sq.eval (x - W.b₂ / 12) = 4 * x ^ 3 - W.c₄ / 12 * x - W.c₆ / 216 := by
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X, c₄, c₆, b₄]
  ring

/-- The least positive real period as an integral, in terms of the depressed cubic
$4X^3 - g_2 X - g_3$. -/
lemma leastRealPeriodIntegral_eq_integral_depressed (W : WeierstrassCurve ℝ) :
    W.leastRealPeriodIntegral =
      2 * ∫ x in Ioi (W.e₁ + W.b₂ / 12), (√(4 * x ^ 3 - W.c₄ / 12 * x - W.c₆ / 216))⁻¹ := by
  rw [leastRealPeriodIntegral, ← integral_comp_add_right_Ioi]
  refine congrArg (2 * ·) (setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_)
  rw [realPeriodIntegrand, ← W.eval_Ψ₂Sq_sub (x + W.b₂ / 12), add_sub_cancel_right]

/- ## The invariants of the period lattice -/

/-- The period lattice of a Weierstrass curve has $g_2 = c_4 / 12$. -/
lemma periodPair_g₂ (W : WeierstrassCurve ℂ) [W.IsElliptic] : W.periodPair.g₂ = W.c₄ / 12 := by
  have h := (PeriodPair.exists_g₂_g₃ W.shortModel_discr_ne_zero).choose_spec.1
  rw [periodPair, PeriodPair.ofCoeffs, h]
  ring

/-- The period lattice of a Weierstrass curve has $g_3 = c_6 / 216$. -/
lemma periodPair_g₃ (W : WeierstrassCurve ℂ) [W.IsElliptic] : W.periodPair.g₃ = W.c₆ / 216 := by
  have h := (PeriodPair.exists_g₂_g₃ W.shortModel_discr_ne_zero).choose_spec.2
  rw [periodPair, PeriodPair.ofCoeffs, h]
  ring

variable (W : WeierstrassCurve ℝ) [W.IsElliptic]

lemma periodPair_map_g₂_re : (W.map Complex.ofRealHom).periodPair.g₂.re = W.c₄ / 12 := by
  rw [periodPair_g₂, map_c₄, Complex.ofRealHom_eq_coe,
    show ((W.c₄ : ℂ)) / 12 = ((W.c₄ / 12 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

lemma periodPair_map_g₃_re : (W.map Complex.ofRealHom).periodPair.g₃.re = W.c₆ / 216 := by
  rw [periodPair_g₃, map_c₆, Complex.ofRealHom_eq_coe,
    show ((W.c₆ : ℂ)) / 216 = ((W.c₆ / 216 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]

/- ## The largest root -/

/-- The substitution $x = X - b_2 / 12$ sends the largest real root $e_1$ of the 2-division
polynomial to the largest real root $\wp(\Omega / 2)$ of the depressed cubic
$4X^3 - g_2 X - g_3$. -/
lemma e₁_add_b₂_div_twelve : W.e₁ + W.b₂ / 12 =
    (W.map Complex.ofRealHom).periodPair.weierstrassPRe (W.leastRealPeriod / 2) := by
  set L := (W.map Complex.ofRealHom).periodPair with hLdef
  have hL : L.IsReal := W.periodPair_map_isReal
  have hΩ : IsLeast {x : ℝ | (x : ℂ) ∈ L.lattice ∧ 0 < x} W.leastRealPeriod :=
    L.isLeast_leastRealPeriod hL
  set e := L.weierstrassPRe (W.leastRealPeriod / 2) with he
  have hroot := hL.isRoot_weierstrassPRe_half hΩ
  have hmax : ∀ x : ℝ, 4 * x ^ 3 - L.g₂.re * x - L.g₃.re = 0 → x ≤ e := fun x hx ↦
    hL.le_weierstrassPRe_half_of_isRoot hΩ hx
  rw [W.periodPair_map_g₂_re, W.periodPair_map_g₃_re] at hroot hmax
  have key : W.e₁ = e - W.b₂ / 12 := by
    refine W.e₁_eq_of_isRoot ?_ fun x hx hroot' ↦ ?_
    · rw [Polynomial.IsRoot, W.eval_Ψ₂Sq_sub]
      linarith [hroot]
    · have := hmax (x + W.b₂ / 12) (by
        rw [← W.eval_Ψ₂Sq_sub, add_sub_cancel_right]
        exact hroot')
      linarith
  linarith [key]

/- ## The equivalence -/

/-- **The least positive real period as an integral**: the integral of the invariant differential
over the identity component of $E(\mathbb{R})$ is the least positive real element of the period
lattice. -/
theorem leastRealPeriodIntegral_eq_leastRealPeriod :
    W.leastRealPeriodIntegral = W.leastRealPeriod := by
  have hL : (W.map Complex.ofRealHom).periodPair.IsReal := W.periodPair_map_isReal
  have hΩ : IsLeast {x : ℝ | (x : ℂ) ∈ (W.map Complex.ofRealHom).periodPair.lattice ∧ 0 < x}
      W.leastRealPeriod := (W.map Complex.ofRealHom).periodPair.isLeast_leastRealPeriod hL
  rw [W.leastRealPeriodIntegral_eq_integral_depressed, W.e₁_add_b₂_div_twelve,
    ← W.periodPair_map_g₂_re, ← W.periodPair_map_g₃_re, hL.integral_inv_sqrt_eq_half hΩ]
  ring

/-- **The two definitions of the real period agree**: the integral of $|\omega|$ over
$E(\mathbb{R})$ is the least positive real period of the period lattice times the number of
connected components of $E(\mathbb{R})$. -/
theorem realPeriodIntegral_eq_realPeriod : W.realPeriodIntegral = W.realPeriod := by
  rcases lt_or_gt_of_ne (isUnit_iff_ne_zero.mp W.isUnit_Δ) with h | h
  · rw [W.realPeriodIntegral_of_neg h, W.leastRealPeriodIntegral_eq_leastRealPeriod,
      W.realPeriod_of_neg h]
  · rw [W.realPeriodIntegral_of_pos h, W.leastRealPeriodIntegral_eq_leastRealPeriod,
      W.realPeriod_of_pos h]

end WeierstrassCurve
