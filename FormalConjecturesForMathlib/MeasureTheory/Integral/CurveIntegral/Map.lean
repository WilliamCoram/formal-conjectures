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

public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

@[expose] public noncomputable section

/-!
# Curve integrals along the image of a path under an affine map

If $\Phi(x) = A x + c$ with $A$ continuous linear, then the integral of a 1-form $\omega$ along
$\Phi \circ \gamma$ is the integral of the pullback $x \mapsto \omega(\Phi x) \circ A$ along
$\gamma$ (`curveIntegral_map_add_const`). This is the change of variables formula for curve
integrals under affine maps.
-/

open MeasureTheory Set
open scoped unitInterval

namespace Path

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {a b : X} {f : X → Y}

/-- The extension of the image of a path is the image of its extension. -/
lemma extend_map' (γ : Path a b) (h : ContinuousOn f (range γ)) (t : ℝ) :
    (γ.map' h).extend t = f (γ.extend t) := rfl

end Path

variable {𝕜 E E' F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedSpace ℝ E] [NormedSpace ℝ E'] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 E]
  [IsScalarTower ℝ 𝕜 E'] {a b : E}

omit [NormedSpace ℝ F] in
/-- The integrand of the curve integral of `ω` along `x ↦ A x + c` composed with `γ` is the
integrand of the pullback `x ↦ (ω (A x + c)).comp A` along `γ`, at points where `γ` is
differentiable. -/
lemma curveIntegralFun_map_add_const (ω : E' → E' →L[𝕜] F) (A : E →L[𝕜] E') (c : E')
    (γ : Path a b) (hγ : DifferentiableOn ℝ γ.extend I) {t : ℝ} (ht : t ∈ I) :
    curveIntegralFun ω (γ.map' (f := fun x ↦ A x + c) (by fun_prop)) t =
      curveIntegralFun (fun x ↦ (ω (A x + c)).comp A) γ t := by
  have hd : HasDerivWithinAt (γ.map' (f := fun x ↦ A x + c) (by fun_prop)).extend
      (A (derivWithin γ.extend I t)) I t :=
    ((A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t
      (hγ t ht).hasDerivWithinAt).add_const c
  rw [curveIntegralFun_def, curveIntegralFun_def,
    hd.derivWithin (uniqueDiffOn_Icc zero_lt_one t ht), Path.extend_map']
  rfl

/-- **Change of variables for curve integrals under an affine map**: for
$\Phi(x) = A x + c$, $\int_{\Phi \circ \gamma} \omega = \int_\gamma \Phi^* \omega$. -/
theorem curveIntegral_map_add_const (ω : E' → E' →L[𝕜] F) (A : E →L[𝕜] E') (c : E')
    (γ : Path a b) (hγ : DifferentiableOn ℝ γ.extend I) :
    ∫ᶜ x in γ.map' (f := fun x ↦ A x + c) (by fun_prop), ω x =
      ∫ᶜ x in γ, (ω (A x + c)).comp A := by
  rw [curveIntegral_def, curveIntegral_def]
  exact intervalIntegral.integral_congr fun t ht ↦ curveIntegralFun_map_add_const ω A c γ hγ
    (by rwa [Set.uIcc_of_le zero_le_one] at ht)

end
