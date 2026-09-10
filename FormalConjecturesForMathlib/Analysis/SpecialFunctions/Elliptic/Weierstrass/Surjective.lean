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

public import FormalConjecturesForMathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.Uniqueness
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public noncomputable section

/-!
# The Weierstrass function is surjective

For a period lattice $\Lambda$ the function $\wp$ takes every complex value off the lattice
(`PeriodPair.exists_weierstrassP_eq`), hence every point $(x, y)$ of the curve
$y^2 = 4x^3 - g_2 x - g_3$ is $(\wp(z), \wp'(z))$ for some $z \notin \Lambda$
(`PeriodPair.exists_weierstrassP_eq_and_derivWeierstrassP_eq`).

The proof is Liouville's: if $\wp - c$ had no zero then $1 / (\wp - c)$, extended by $0$ at the
lattice points where $\wp$ has poles, would be an entire doubly periodic function, hence bounded,
hence constant, which is absurd. The sign of $\wp'$ is then adjusted using that $\wp$ is even and
$\wp'$ is odd.

*References:*
- [Pas2017] Georgios Pastras. Four Lectures on Weierstrass Elliptic Function and Applications in
    Classical and Quantum Mechanics, Theorems 1.2 and 1.3, https://arxiv.org/abs/1706.07371
- [WW1927] E. T. Whittaker, G. N. Watson. A Course of Modern Analysis, 4th edition, §20.12 (IV)
    and §20.13
- [Mil2006] J. S. Milne. Elliptic Curves, Chapter III, Corollary 2.2 and Proposition 3.7,
    https://www.jmilne.org/math/Books/ectext6.pdf
-/

open Filter Set Topology

namespace PeriodPair

variable (L : PeriodPair)

/-- $\wp$ tends to infinity at the lattice points. -/
lemma tendsto_weierstrassP_cobounded {l : ℂ} (hl : l ∈ L.lattice) :
    Tendsto ℘[L] (𝓝[≠] l) (Bornology.cobounded ℂ) :=
  tendsto_cobounded_of_meromorphicOrderAt_neg (by rw [L.order_weierstrassP l hl]; decide)

/-- If $\wp$ omits the value $c$ off the lattice, then $1 / (\wp - c)$, extended by $0$ on the
lattice, is entire. -/
lemma differentiable_inv_weierstrassP_sub (c : ℂ) (hc : ∀ z, z ∉ L.lattice → ℘[L] z ≠ c) :
    Differentiable ℂ ((L.lattice : Set ℂ)ᶜ.indicator fun z ↦ (℘[L] z - c)⁻¹) := by
  have hoff : ∀ z ∉ L.lattice, DifferentiableAt ℂ
      ((L.lattice : Set ℂ)ᶜ.indicator fun z ↦ (℘[L] z - c)⁻¹) z := by
    intro z hz
    refine DifferentiableAt.congr_of_eventuallyEq
      (((L.analyticOnNhd_weierstrassP z hz).differentiableAt.sub_const c).inv
        (sub_ne_zero.mpr (hc z hz))) ?_
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact Set.indicator_of_mem hw _
  intro z
  by_cases hz : z ∈ L.lattice
  · have hpunct : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds z),
        self_mem_nhdsWithin] with w hw hw2 hmem
      exact hw ⟨hmem, hw2⟩
    have hcob : Tendsto (fun w ↦ ℘[L] w - c) (𝓝[≠] z) (Bornology.cobounded ℂ) := by
      rw [← tendsto_norm_atTop_iff_cobounded]
      refine tendsto_atTop_mono (fun w ↦ ?_)
        (tendsto_atTop_add_const_right _ (-‖c‖)
          (tendsto_norm_atTop_iff_cobounded.mpr (L.tendsto_weierstrassP_cobounded hz)))
      simpa [sub_eq_add_neg] using norm_sub_norm_le (℘[L] w) c
    have hgz : (L.lattice : Set ℂ)ᶜ.indicator (fun z ↦ (℘[L] z - c)⁻¹) z = 0 :=
      Set.indicator_of_notMem (by simpa using hz) _
    have htend : Tendsto ((L.lattice : Set ℂ)ᶜ.indicator fun z ↦ (℘[L] z - c)⁻¹)
        (𝓝[≠] z) (𝓝 0) := by
      refine (tendsto_inv₀_cobounded.comp hcob).congr' ?_
      filter_upwards [hpunct] with w hw
      exact (Set.indicator_of_mem (by simpa using hw) _).symm
    have hpure : Tendsto ((L.lattice : Set ℂ)ᶜ.indicator fun z ↦ (℘[L] z - c)⁻¹)
        (pure z) (𝓝 0) := by
      have := tendsto_pure_nhds ((L.lattice : Set ℂ)ᶜ.indicator fun z ↦ (℘[L] z - c)⁻¹) z
      rwa [hgz] at this
    have hcont : ContinuousAt ((L.lattice : Set ℂ)ᶜ.indicator fun z ↦ (℘[L] z - c)⁻¹) z := by
      rw [ContinuousAt, hgz, ← nhdsNE_sup_pure z, Filter.tendsto_sup]
      exact ⟨htend, hpure⟩
    exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (by filter_upwards [hpunct] with w hw using hoff w hw) hcont).differentiableAt
  · exact hoff z hz

/-- **$\wp$ is surjective**: every complex number is a value of $\wp$ off the lattice. -/
theorem exists_weierstrassP_eq (c : ℂ) : ∃ z, z ∉ L.lattice ∧ ℘[L] z = c := by
  by_contra! hc
  have hg : Differentiable ℂ ((L.lattice : Set ℂ)ᶜ.indicator fun z ↦ (℘[L] z - c)⁻¹) :=
    L.differentiable_inv_weierstrassP_sub c hc
  have hper : ∀ z w, w ∈ L.lattice →
      (L.lattice : Set ℂ)ᶜ.indicator (fun z ↦ (℘[L] z - c)⁻¹) (z + w)
        = (L.lattice : Set ℂ)ᶜ.indicator (fun z ↦ (℘[L] z - c)⁻¹) z := by
    intro z w hw
    by_cases hz : z ∈ L.lattice
    · rw [Set.indicator_of_notMem (by simpa using add_mem hz hw),
        Set.indicator_of_notMem (by simpa using hz)]
    · have hzw : z + w ∉ L.lattice := fun h ↦ hz (by simpa using sub_mem h hw)
      rw [Set.indicator_of_mem (by simpa using hzw), Set.indicator_of_mem (by simpa using hz),
        L.weierstrassP_add_coe z ⟨w, hw⟩]
  have hb := (IsZLattice.isCompact_range_of_periodic L.lattice _ hg.continuous hper).isBounded
  have h := hg.apply_eq_apply_of_bounded hb (L.ω₁ / 2) 0
  rw [Set.indicator_of_mem (by simpa using L.ω₁_div_two_notMem_lattice),
    Set.indicator_of_notMem (by simp)] at h
  exact inv_ne_zero (sub_ne_zero.mpr (hc _ L.ω₁_div_two_notMem_lattice)) h

/-- Every point of the curve $y^2 = 4x^3 - g_2 x - g_3$ is $(\wp(z), \wp'(z))$ for some
$z \notin \Lambda$. -/
theorem exists_weierstrassP_eq_and_derivWeierstrassP_eq {x y : ℂ}
    (h : y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃) :
    ∃ z, z ∉ L.lattice ∧ ℘[L] z = x ∧ ℘'[L] z = y := by
  obtain ⟨z, hz, hzx⟩ := L.exists_weierstrassP_eq x
  have hsq : ℘'[L] z ^ 2 = y ^ 2 := by rw [L.derivWeierstrassP_sq z hz, hzx, h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hy | hy
  · exact ⟨z, hz, hzx, hy⟩
  · refine ⟨-z, fun h' ↦ hz (by simpa using neg_mem h'), ?_, ?_⟩
    · rw [L.weierstrassP_neg, hzx]
    · rw [L.derivWeierstrassP_neg, hy, neg_neg]

end PeriodPair

end
