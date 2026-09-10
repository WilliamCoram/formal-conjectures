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

public import FormalConjecturesTest.Period.Analysis.SpecialFunctions.Elliptic.Weierstrass.Uniqueness
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
  tendsto_cobounded_of_meromorphicOrderAt_neg <| (L.order_weierstrassP l hl).trans_lt (by decide)

/-- If $\wp$ omits the value $c$ off the lattice, then $1 / (\wp - c)$, extended by $0$ on the
lattice, is entire. -/
lemma differentiable_inv_weierstrassP_sub (c : ℂ) (hc : ∀ z, z ∉ L.lattice → ℘[L] z ≠ c) :
    Differentiable ℂ ((L.lattice : Set ℂ)ᶜ.indicator fun z ↦ (℘[L] z - c)⁻¹) := by
  have hoff : ∀ z ∉ L.lattice, DifferentiableAt ℂ
      ((L.lattice : Set ℂ)ᶜ.indicator fun z ↦ (℘[L] z - c)⁻¹) z := fun z hz ↦
    (((L.analyticOnNhd_weierstrassP z hz).differentiableAt.sub_const c).inv
      (sub_ne_zero.mpr (hc z hz))).congr_of_eventuallyEq
      (Set.eqOn_indicator.eventuallyEq_of_mem <| L.isClosed_lattice.isOpen_compl.mem_nhds hz)
  intro z
  by_cases hz : z ∈ L.lattice
  · have hpunct : (L.lattice : Set ℂ)ᶜ ∈ 𝓝[≠] z :=
      mem_of_superset (inter_mem_nhdsWithin _ (L.compl_lattice_sdiff_singleton_mem_nhds z))
        fun w ⟨hne, hw⟩ hmem ↦ hw ⟨hmem, hne⟩
    refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      (eventually_of_mem hpunct hoff) <| continuousWithinAt_compl_self.mp ?_).differentiableAt
    rw [ContinuousWithinAt, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hz)]
    exact (tendsto_inv₀_cobounded.comp <| (tendsto_sub_const_cobounded c).comp
      (L.tendsto_weierstrassP_cobounded hz)).congr'
        (Set.eqOn_indicator.symm.eventuallyEq_of_mem hpunct)
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
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (add_mem hz hw)),
        Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hz)]
    · have hzw : z + w ∉ L.lattice := fun h ↦ hz (by simpa using sub_mem h hw)
      rw [Set.indicator_of_mem (by simpa using hzw), Set.indicator_of_mem (by simpa using hz),
        L.weierstrassP_add_coe z ⟨w, hw⟩]
  have hb := (IsZLattice.isCompact_range_of_periodic L.lattice _ hg.continuous hper).isBounded
  have h := hg.apply_eq_apply_of_bounded hb (L.ω₁ / 2) 0
  rw [Set.indicator_of_mem L.ω₁_div_two_notMem_lattice,
    Set.indicator_of_notMem (Set.notMem_compl_iff.mpr (zero_mem _))] at h
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
  · refine ⟨-z, fun h' ↦ hz (neg_mem_iff.mp h'), ?_, ?_⟩
    · rw [L.weierstrassP_neg, hzx]
    · rw [L.derivWeierstrassP_neg, hy, neg_neg]

end PeriodPair

end
