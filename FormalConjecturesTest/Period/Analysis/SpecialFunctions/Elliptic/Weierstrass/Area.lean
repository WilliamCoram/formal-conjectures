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

public import FormalConjecturesTest.Period.Analysis.SpecialFunctions.Elliptic.Weierstrass.HalfDomain
public import FormalConjecturesTest.Period.LinearAlgebra.Complex.Determinant

@[expose] public noncomputable section

/-!
# The area integral of the curve of a lattice

For a period lattice $\Lambda$ with invariants $g_2, g_3$,
$$\int_{\mathbb{C}} \frac{dA(x)}{|4x^3 - g_2 x - g_3|} = \frac{\operatorname{covol}(\Lambda)}{2}
  \qquad (\text{`PeriodPair.integral_inv_norm_cubic`}).$$
This is the change of variables $x = \wp(z)$ on the half domain $H$ of
`Weierstrass/HalfDomain.lean`, where $\wp$ is injective with image almost all of $\mathbb{C}$: the
real Jacobian of $\wp$ is $|\wp'(z)|^2$ (`Complex.det_restrictScalars_smulRight`), and
$4\wp^3 - g_2\wp - g_3 = \wp'^2$ (`PeriodPair.derivWeierstrassP_sq`), so the integrand pulls back to
the constant $1$ and the integral is the area of $H$, half the covolume.

## Source correspondence

[Mil2006, III Remark 3.11]: "Since $x = \wp(z)$ and $y = \wp'(z)$, $dx/y = \wp'(z)dz/\wp'(z) = dz$.
Thus the differential $dz$ on $\mathbb{C}$ corresponds to the differential $dx/y$ on
$E(\mathbb{C})$."
Taking absolute values squared, $|dx \wedge d\bar{x}|/|y|^2 = |dz \wedge d\bar{z}|$, which is the
statement that the density $dA(x)/|4x^3 - g_2x - g_3|$ pulls back to $dA(z)$; the integral over
$\mathbb{C}$ is the integral over a half fundamental domain because $\wp$ is two-to-one.
-/

open MeasureTheory Set

namespace PeriodPair

variable (L : PeriodPair)

/-- Source: [Mil2006, III Prop. 2.4] ($\wp' = d\wp/dz$), as `PeriodPair.hasDerivAt_weierstrassP`,
restricted to real scalars. -/
lemma hasFDerivWithinAt_weierstrassP_halfDomain {z : ℂ} (hz : z ∈ L.halfDomain) :
    HasFDerivWithinAt ℘[L]
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (℘'[L] z)).restrictScalars ℝ)
      L.halfDomain z :=
  ((hasDerivAt_iff_hasFDerivAt.mp (L.hasDerivAt_weierstrassP
    (L.notMem_lattice_of_mem_halfDomain hz))).restrictScalars ℝ).hasFDerivWithinAt

/-- On the half domain the pulled-back integrand is the constant `1`: the Jacobian $|\wp'|^2$
cancels $|4\wp^3 - g_2\wp - g_3| = |\wp'|^2$. -/
lemma abs_det_mul_inv_norm_cubic_weierstrassP {z : ℂ} (hz : z ∈ L.halfDomain) :
    |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (℘'[L] z)).restrictScalars ℝ).det| *
      ‖4 * ℘[L] z ^ 3 - L.g₂ * ℘[L] z - L.g₃‖⁻¹ = 1 := by
  have hz' := L.notMem_lattice_of_mem_halfDomain hz
  have h0 : ℘'[L] z ≠ 0 := fun h ↦
    L.two_mul_notMem_lattice_of_mem_halfDomain hz ((L.derivWeierstrassP_eq_zero_iff hz').mp h)
  rw [Complex.det_restrictScalars_smulRight, abs_of_nonneg (by positivity),
    ← L.derivWeierstrassP_sq z hz', norm_pow]
  exact mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr h0))

/-- Source: Mathlib's `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`; the pulled-back
integrand is the constant `1` on the bounded half domain. -/
lemma integrableOn_inv_norm_cubic_image :
    IntegrableOn (fun x : ℂ ↦ ‖4 * x ^ 3 - L.g₂ * x - L.g₃‖⁻¹) (℘[L] '' L.halfDomain) := by
  have hfin : volume L.halfDomain ≠ ⊤ :=
    ((measure_mono (L.halfDomain_subset_fundamentalDomain.trans subset_closure)).trans_lt
      (ZSpan.fundamentalDomain_isBounded L.basis).isCompact_closure.measure_lt_top).ne
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume L.measurableSet_halfDomain
    (fun z hz ↦ L.hasFDerivWithinAt_weierstrassP_halfDomain hz) L.injOn_weierstrassP_halfDomain]
  refine (integrableOn_const (C := (1 : ℝ)) hfin).congr_fun (fun z hz ↦ ?_)
    L.measurableSet_halfDomain
  simp only [smul_eq_mul]
  exact (L.abs_det_mul_inv_norm_cubic_weierstrassP hz).symm

/-- The density $1/|4x^3 - g_2 x - g_3|$ is integrable on $\mathbb{C}$: it is integrable on
$\wp(H)$ (`PeriodPair.integrableOn_inv_norm_cubic_image`), which is almost all of $\mathbb{C}$. -/
theorem integrable_inv_norm_cubic :
    Integrable (fun x : ℂ ↦ ‖4 * x ^ 3 - L.g₂ * x - L.g₃‖⁻¹) :=
  integrableOn_univ.mp (L.integrableOn_inv_norm_cubic_image.congr_set_ae
    L.image_weierstrassP_halfDomain_ae_eq_univ.symm)

/-- **The area integral of the curve of a lattice is half the covolume.** Source: [Mil2006, III
Remark 3.11] ($dx/y = dz$) with Mathlib's change of variables
`integral_image_eq_integral_abs_det_fderiv_smul` on the half domain. -/
theorem integral_inv_norm_cubic :
    ∫ x : ℂ, ‖4 * x ^ 3 - L.g₂ * x - L.g₃‖⁻¹ = ZLattice.covolume L.lattice / 2 := by
  rw [← setIntegral_univ, ← setIntegral_congr_set L.image_weierstrassP_halfDomain_ae_eq_univ,
    integral_image_eq_integral_abs_det_fderiv_smul volume L.measurableSet_halfDomain
      (fun z hz ↦ L.hasFDerivWithinAt_weierstrassP_halfDomain hz) L.injOn_weierstrassP_halfDomain,
    setIntegral_congr_fun L.measurableSet_halfDomain (g := fun _ ↦ (1 : ℝ))
      (fun z hz ↦ by simpa only [smul_eq_mul] using L.abs_det_mul_inv_norm_cubic_weierstrassP hz),
    setIntegral_const, smul_eq_mul, mul_one, L.volume_real_halfDomain]

end PeriodPair

end
