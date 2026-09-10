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

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.Topology.Algebra.Module.Determinant

@[expose] public noncomputable section

/-!
# The real Jacobian of multiplication by a complex number

Multiplication by $c \in \mathbb{C}$, regarded as an $\mathbb{R}$-linear map of $\mathbb{C}$, has
determinant $|c|^2$: in the basis $(1, i)$ it is the matrix
$\begin{pmatrix} a & -b \\ b & a \end{pmatrix}$ for $c = a + bi$. This is the Jacobian of a
holomorphic map $f$ at a point where $f' = c$, which is what the change of variables formula
needs (`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`).

The map is written in the form `HasDerivAt` produces, `(smulRight 1 c).restrictScalars ℝ`.
-/

namespace Complex

/-- Source: Wikipedia, *Complex number*, § Matrix representation ("this isomorphism associates the
square of the absolute value of a complex number with the determinant of the corresponding
matrix"). -/
lemma det_restrictScalars_smulRight (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  show LinearMap.det _ = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.sq_norm, Complex.normSq_apply]

end Complex

end
