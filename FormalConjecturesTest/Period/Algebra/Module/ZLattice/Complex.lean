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

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public noncomputable section

/-!
# The covolume of a lattice in `ℂ`

For a $\mathbb{Z}$-lattice $\Lambda \subset \mathbb{C}$ with basis $(w_1, w_2)$, the covolume
(the Lebesgue area of a fundamental parallelogram) is
$$\operatorname{covol}(\Lambda) = |\operatorname{Im}(\bar w_1 w_2)|
  = |\operatorname{Re} w_1 \operatorname{Im} w_2 - \operatorname{Im} w_1 \operatorname{Re} w_2|,$$
the absolute value of the determinant of the basis in the coordinates $(1, i)$
(`ZLattice.covolume_eq_abs_im_conj_mul`). For the period lattice of a `PeriodPair` this is
`PeriodPair.covolume_lattice`.
-/

open MeasureTheory Module

namespace Complex

/-- Source: the unit square has area `1`; Mathlib's `OrthonormalBasis.volume_parallelepiped`
for `Complex.orthonormalBasisOneI`. -/
lemma volume_fundamentalDomain_basisOneI :
    volume (ZSpan.fundamentalDomain Complex.basisOneI) = 1 := by
  rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped Complex.basisOneI volume),
    ← Complex.toBasis_orthonormalBasisOneI, OrthonormalBasis.coe_toBasis]
  exact Complex.orthonormalBasisOneI.volume_parallelepiped

end Complex

namespace ZLattice

/-- Source: LMFDB knowl `ec.period` ("In terms of a basis $[w_1, w_2]$ of the period lattice ...
$2\operatorname{Im}(\overline{w_1} w_2)$, which is double the covolume of the period lattice"). -/
theorem covolume_eq_abs_im_conj_mul (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin 2) ℤ L) :
    covolume L = |((starRingEnd ℂ) (b 0 : ℂ) * (b 1 : ℂ)).im| := by
  rw [covolume_eq_det_mul_measureReal L volume b Complex.basisOneI, measureReal_def,
    Complex.volume_fundamentalDomain_basisOneI, ENNReal.toReal_one, mul_one, Basis.det_apply,
    Matrix.det_fin_two]
  congr 1
  simp [Basis.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.mul_im]
  ring

end ZLattice

namespace PeriodPair

/-- Source: LMFDB knowl `ec.period`, the covolume of the period lattice with basis
$(\omega_1, \omega_2)$. -/
theorem covolume_lattice (L : PeriodPair) :
    ZLattice.covolume L.lattice = |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| := by
  rw [ZLattice.covolume_eq_abs_im_conj_mul L.lattice L.latticeBasis, latticeBasis_zero,
    latticeBasis_one]

end PeriodPair

end
