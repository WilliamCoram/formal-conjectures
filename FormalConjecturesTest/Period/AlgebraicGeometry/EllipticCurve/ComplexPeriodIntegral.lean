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

public import FormalConjecturesTest.Period.AlgebraicGeometry.EllipticCurve.PeriodLattice
public import FormalConjecturesTest.Period.AlgebraicGeometry.EllipticCurve.InvariantDifferential
public import FormalConjecturesTest.Period.Analysis.SpecialFunctions.Elliptic.Weierstrass.Area

@[expose] public noncomputable section

/-!
# The complex period of an elliptic curve over `ℂ`, as an integral

For an elliptic curve $E$ over $\mathbb{C}$ with invariant differential
$\omega = dx / (2y + a_1 x + a_3)$, the period at a complex place is
$$\Omega_{\mathbb{C}}(E) = \int_{E(\mathbb{C})} |\omega \wedge \bar\omega|.$$
Projecting to the $x$-line, on each of the two sheets $y = \pm\ldots$ one has
$|\omega \wedge \bar\omega| = |dx \wedge d\bar x| / |2y + a_1x + a_3|^2 = 2\,dA(x) / |\Psi_2^2(x)|$,
since $(2y + a_1 x + a_3)^2 = \Psi_2^2(x) = 4x^3 + b_2x^2 + 2b_4x + b_6$ on the curve
(`WeierstrassCurve.eval_Ψ₂Sq_eq_sq_of_equation`) and $|dx \wedge d\bar x| = 2\,dA$. Hence
$$\Omega_{\mathbb{C}}(E) = 4 \int_{\mathbb{C}} \frac{dA(x)}{|\Psi_2^2(x)|},$$
which is the definition adopted here (`WeierstrassCurve.complexPeriodIntegral`), the complex
counterpart of `WeierstrassCurve.leastRealPeriodIntegral`. The main theorem
`WeierstrassCurve.complexPeriodIntegral_eq_two_mul_covolume` identifies it with twice the covolume
of the period lattice, $2|\operatorname{Im}(\bar\omega_1 \omega_2)|$
(`WeierstrassCurve.complexPeriodIntegral_eq_two_mul_abs_im`).

## Source correspondence

LMFDB knowl `ec.period`: "For a complex place given by an embedding $v : K \to \mathbb{C}$, we
define $\Omega_v(E_v) = \int_{E_v(\mathbb{C})} \omega_E \wedge \overline{\omega_E}$. In terms of a
basis $[w_1, w_2]$ of the period lattice of $E_v$, where $\operatorname{Im}(w_2/w_1) > 0$, we have
$\Omega_v(E_v) = 2\operatorname{Im}(\overline{w_1} w_2)$, which is double the covolume of the period
lattice." The integral of the $2$-form is understood as the integral of the associated density
$|\omega \wedge \bar\omega|$, as the value $2\operatorname{Im}(\bar w_1 w_2)$ requires; our
`periodPair` carries no orientation, whence the absolute value.

*References:*
- [LMFDB](https://www.lmfdb.org/knowledge/show/ec.period), knowl `ec.period`
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, VI.3.6 and
    VI.5.1, https://link.springer.com/book/10.1007/978-0-387-09494-6
- [Mil2006] J. S. Milne. Elliptic Curves, Chapter III, Remark 3.11,
    https://www.jmilne.org/math/Books/ectext6.pdf
-/

open MeasureTheory

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℂ)

/-- The density of $\Omega_{\mathbb{C}}$ on the $x$-line: $1 / |\Psi_2^2(x)|$. -/
def complexPeriodIntegrand (x : ℂ) : ℝ := ‖W.Ψ₂Sq.eval x‖⁻¹

/-- The density of the complex period is nonnegative. -/
lemma complexPeriodIntegrand_nonneg (x : ℂ) : 0 ≤ W.complexPeriodIntegrand x :=
  inv_nonneg.mpr (norm_nonneg _)

/-- The density of the complex period is measurable, being the inverse norm of a polynomial. -/
lemma measurable_complexPeriodIntegrand : Measurable W.complexPeriodIntegrand :=
  W.Ψ₂Sq.continuous.norm.measurable.inv

/-- **The complex period as an integral**: $\Omega_{\mathbb{C}}(E) = \int_{E(\mathbb{C})}
|\omega \wedge \bar\omega| = 4 \int_{\mathbb{C}} dA(x) / |\Psi_2^2(x)|$. Source: LMFDB knowl
`ec.period`. -/
def complexPeriodIntegral : ℝ := 4 * ∫ x : ℂ, W.complexPeriodIntegrand x

/-- The substitution $x \mapsto x - b_2/12$ takes $\Psi_2^2$ to $4x^3 - g_2 x - g_3$
(`WeierstrassCurve.eval_Ψ₂Sq_sub`), and Lebesgue measure is translation invariant. -/
lemma integral_complexPeriodIntegrand [W.IsElliptic] :
    ∫ x : ℂ, W.complexPeriodIntegrand x
      = ∫ x : ℂ, ‖4 * x ^ 3 - W.periodPair.g₂ * x - W.periodPair.g₃‖⁻¹ := by
  rw [← integral_sub_right_eq_self W.complexPeriodIntegrand (W.b₂ / 12)]
  simp only [complexPeriodIntegrand, W.eval_Ψ₂Sq_sub, W.periodPair_g₂, W.periodPair_g₃]

/-- The density of the complex period is integrable on $\mathbb{C}$: it is a translate of
$1/|4x^3 - g_2 x - g_3|$ for the invariants of the period lattice
(`PeriodPair.integrable_inv_norm_cubic`). -/
theorem integrable_complexPeriodIntegrand [W.IsElliptic] : Integrable W.complexPeriodIntegrand := by
  refine (W.periodPair.integrable_inv_norm_cubic.comp_add_right (W.b₂ / 12)).congr
    (Filter.Eventually.of_forall fun x ↦ ?_)
  show ‖4 * (x + W.b₂ / 12) ^ 3 - W.periodPair.g₂ * (x + W.b₂ / 12) - W.periodPair.g₃‖⁻¹ =
    ‖W.Ψ₂Sq.eval x‖⁻¹
  rw [W.periodPair_g₂, W.periodPair_g₃, ← W.eval_Ψ₂Sq_sub, add_sub_cancel_right]

/-- **The complex period is twice the covolume of the period lattice.** Source: LMFDB knowl
`ec.period`. -/
theorem complexPeriodIntegral_eq_two_mul_covolume [W.IsElliptic] :
    W.complexPeriodIntegral = 2 * ZLattice.covolume W.periodPair.lattice := by
  rw [complexPeriodIntegral, W.integral_complexPeriodIntegrand,
    W.periodPair.integral_inv_norm_cubic]
  ring

/-- **The complex period is $2|\operatorname{Im}(\bar\omega_1 \omega_2)|$.** Source: LMFDB knowl
`ec.period`. -/
theorem complexPeriodIntegral_eq_two_mul_abs_im [W.IsElliptic] :
    W.complexPeriodIntegral = 2 * |((starRingEnd ℂ) W.periodPair.ω₁ * W.periodPair.ω₂).im| := by
  rw [W.complexPeriodIntegral_eq_two_mul_covolume, W.periodPair.covolume_lattice]

/-- The complex period is positive. -/
theorem complexPeriodIntegral_pos [W.IsElliptic] : 0 < W.complexPeriodIntegral := by
  rw [W.complexPeriodIntegral_eq_two_mul_covolume]
  exact mul_pos two_pos (ZLattice.covolume_pos _ _)

end WeierstrassCurve

end
