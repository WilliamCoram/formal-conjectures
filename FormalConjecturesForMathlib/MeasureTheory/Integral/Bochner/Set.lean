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

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public noncomputable section

/-!
# Translating a set integral over a half-line

* `MeasureTheory.integral_comp_add_right_Ioi`: $\int_a^\infty g(x + c) \, dx =
  \int_{a + c}^\infty g(x) \, dx$, the counterpart for $(a, \infty)$ of
  `MeasureTheory.integral_comp_add_right` on the whole line.
-/

open Set

namespace MeasureTheory

/-- Translating a set integral over a half-line:
$\int_a^\infty g(x + c) \, dx = \int_{a + c}^\infty g(x) \, dx$. -/
theorem integral_comp_add_right_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → E) (a c : ℝ) : ∫ x in Ioi a, g (x + c) = ∫ x in Ioi (a + c), g x := by
  simpa using (measurePreserving_add_right volume c).setIntegral_preimage_emb
    (measurableEmbedding_addRight c) g (Ioi (a + c))

end MeasureTheory
