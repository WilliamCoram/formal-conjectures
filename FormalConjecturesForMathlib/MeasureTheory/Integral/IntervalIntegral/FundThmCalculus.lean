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

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public noncomputable section

/-!
# The fundamental theorem of calculus on a closed interval

`intervalIntegral.integral_hasDerivWithinAt_Icc`: for `f` continuous on $[a, b]$, the function
$u \mapsto \int_a^u f$ has derivative $f(t)$ at $t$ within $[a, b]$, for every $t \in [a, b]$.

Mathlib's `intervalIntegral.integral_hasDerivWithinAt_right` is stated through the
`intervalIntegral.FTCFilter` class, whose only instances are `pure`, `𝓝`, `𝓝[≤]` and `𝓝[≥]`;
there is none for a closed interval. Since `HasDerivWithinAt f c s t` depends on `s` only through
`𝓝[s] t`, the closed-interval statement follows by splitting on the position of `t`: at the
endpoints `Icc a b` agrees with `Ici a` resp. `Iic b` near the point, and in the interior
`Icc a b` is a neighbourhood of `t`.
-/

open Filter MeasureTheory Set Topology

namespace intervalIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f : ℝ → E} {a b : ℝ}

/-- **Fundamental theorem of calculus on a closed interval**: if `f` is continuous on `[a, b]`
then `u ↦ ∫ x in a..u, f x` has derivative `f t` at `t` within `[a, b]`. -/
theorem integral_hasDerivWithinAt_Icc (hab : a < b) (hf : ContinuousOn f (Icc a b)) {t : ℝ}
    (ht : t ∈ Icc a b) : HasDerivWithinAt (fun u ↦ ∫ x in a..u, f x) (f t) (Icc a b) t := by
  have hint : IntervalIntegrable f volume a t :=
    (hf.mono (uIcc_subset_Icc ⟨le_rfl, hab.le⟩ ht)).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter f (𝓝[Icc a b] t) volume :=
    hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t
  rcases ht.1.eq_or_lt with rfl | hat
  · have hmem : Icc a b ∈ 𝓝[>] a := Icc_mem_nhdsGT hab
    rw [← Ici_inter_Iic, hasDerivWithinAt_inter (Iic_mem_nhds hab)]
    exact integral_hasDerivWithinAt_right hint (hmeas.filter_mono (nhdsWithin_le_iff.mpr hmem))
      ((hf a ht).mono_of_mem_nhdsWithin hmem)
  rcases ht.2.eq_or_lt with rfl | htb
  · have hmem : Icc a t ∈ 𝓝[≤] t := Icc_mem_nhdsLE hat
    rw [← Ici_inter_Iic, inter_comm, hasDerivWithinAt_inter (Ici_mem_nhds hat)]
    exact integral_hasDerivWithinAt_right hint (hmeas.filter_mono (nhdsWithin_le_iff.mpr hmem))
      ((hf t ht).mono_of_mem_nhdsWithin hmem)
  · have hmem : Icc a b ∈ 𝓝 t := Icc_mem_nhds hat htb
    exact (integral_hasDerivAt_right hint (hmeas.filter_mono (nhdsWithin_eq_nhds.mpr hmem).ge)
      ((hf t ht).continuousAt hmem)).hasDerivWithinAt

end intervalIntegral

end
