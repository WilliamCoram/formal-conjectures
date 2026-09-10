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

public import FormalConjecturesForMathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.HalfPeriods

@[expose] public noncomputable section

/-!
# The Weierstrass function is injective modulo the lattice

For a period lattice $\Lambda$, $\wp(a) = \wp(b)$ if and only if $a \equiv \pm b \pmod \Lambda$
(`PeriodPair.weierstrassP_eq_iff`), and $\wp(a) = \wp(b)$, $\wp'(a) = \wp'(b)$ together force
$a \equiv b \pmod \Lambda$
(`PeriodPair.sub_mem_lattice_of_weierstrassP_eq_of_derivWeierstrassP_eq`).
Classically this is because $\wp - \wp(b)$ is an elliptic function of order $2$, so it has exactly
two zeros in a cell, at $\pm b$; that count needs the argument principle for elliptic functions,
which is not in Mathlib. Instead the proof reuses the differential equation argument of
`FormalConjecturesForMathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.HalfPeriods`:

* $t \mapsto \wp(a + t)$ and $t \mapsto \wp(b + t)$ solve the same second-order equation
  $u'' = 6u^2 - g_2 / 2$ with the same initial data, so they agree near $t = 0$
  (`PeriodPair.eventually_weierstrassP_add_eq_add`), hence wherever both are defined, by the
  identity theorem (`PeriodPair.weierstrassP_add_eq_add_of_eq`);
* so $a - b$ is a period of $\wp$, and the periods of $\wp$ are exactly the lattice
  (`PeriodPair.mem_lattice_of_forall_weierstrassP_add_eq`), by comparing the pole of $\wp$ at $0$
  with its analyticity at $a - b$.

*References:*
- [WW1927] E. T. Whittaker, G. N. Watson. A Course of Modern Analysis, 4th edition, §20.13 and
    the footnote to §20.31
- [Pas2017] Georgios Pastras. Four Lectures on Weierstrass Elliptic Function and Applications in
    Classical and Quantum Mechanics, Theorem 1.3 and §1 "The Roots of the Cubic Polynomial",
    https://arxiv.org/abs/1706.07371
- [Mil2006] J. S. Milne. Elliptic Curves, Chapter III, Proposition 3.7,
    https://www.jmilne.org/math/Books/ectext6.pdf
-/

open Filter Set Topology

namespace PeriodPair

variable (L : PeriodPair)

/-- If $\wp(a) = \wp(b)$ and $\wp'(a) = \wp'(b)$ then $\wp(a + t) = \wp(b + t)$ for real $t$ near
$0$, by uniqueness for the system $(u, v)' = (v, 6u^2 - g_2 / 2)$. -/
lemma eventually_weierstrassP_add_eq_add {a b : ℂ} (ha : a ∉ L.lattice) (hb : b ∉ L.lattice)
    (h₁ : ℘[L] a = ℘[L] b) (h₂ : ℘'[L] a = ℘'[L] b) :
    ∀ᶠ t : ℝ in 𝓝 0, ℘[L] (a + t) = ℘[L] (b + t) := by
  set v : ℝ → ℂ × ℂ → ℂ × ℂ := fun _ p ↦ (p.2, 6 * p.1 ^ 2 - L.g₂ / 2)
  set f : ℝ → ℂ × ℂ := fun t ↦ (℘[L] (a + t), ℘'[L] (a + t)) with hf
  set g : ℝ → ℂ × ℂ := fun t ↦ (℘[L] (b + t), ℘'[L] (b + t)) with hg
  obtain ⟨K, S, hS, hK⟩ :
      ∃ K, ∃ S ∈ 𝓝 (℘[L] a, ℘'[L] a), LipschitzOnWith K (v 0) S := by
    have hv1 : ContDiff ℂ 1 (v 0) := by fun_prop
    exact hv1.contDiffAt.exists_lipschitzOnWith
  have hcont : ∀ᶠ t : ℝ in 𝓝 0, a + (t : ℂ) ∉ L.lattice ∧ b + (t : ℂ) ∉ L.lattice := by
    have hta : Filter.Tendsto (fun t : ℝ ↦ a + (t : ℂ)) (𝓝 0) (𝓝 a) := by
      have h : ContinuousAt (fun t : ℝ ↦ a + (t : ℂ)) 0 := by fun_prop
      simpa using h.tendsto
    have htb : Filter.Tendsto (fun t : ℝ ↦ b + (t : ℂ)) (𝓝 0) (𝓝 b) := by
      have h : ContinuousAt (fun t : ℝ ↦ b + (t : ℂ)) 0 := by fun_prop
      simpa using h.tendsto
    exact (hta.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds ha)).and
      (htb.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds hb))
  have hfd : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt f (v t (f t)) t := by
    filter_upwards [hcont] with t ht
    exact (((L.hasDerivAt_weierstrassP ht.1).comp_const_add a (t : ℂ)).comp_ofReal).prodMk
      (((L.hasDerivAt_derivWeierstrassP ht.1).comp_const_add a (t : ℂ)).comp_ofReal)
  have hgd : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt g (v t (g t)) t := by
    filter_upwards [hcont] with t ht
    exact (((L.hasDerivAt_weierstrassP ht.2).comp_const_add b (t : ℂ)).comp_ofReal).prodMk
      (((L.hasDerivAt_derivWeierstrassP ht.2).comp_const_add b (t : ℂ)).comp_ofReal)
  have hf0 : f 0 = (℘[L] a, ℘'[L] a) := by simp [hf]
  have hg0 : g 0 = (℘[L] a, ℘'[L] a) := by simp [hg, h₁, h₂]
  have hfS : ∀ᶠ t : ℝ in 𝓝 0, f t ∈ S :=
    hfd.self_of_nhds.continuousAt.eventually_mem (hf0 ▸ hS)
  have hgS : ∀ᶠ t : ℝ in 𝓝 0, g t ∈ S :=
    hgd.self_of_nhds.continuousAt.eventually_mem (hg0 ▸ hS)
  have key := ODE_solution_unique_of_eventually (v := v) (s := fun _ ↦ S) (K := K) (t₀ := 0)
    (f := f) (g := g) (Filter.Eventually.of_forall fun _ ↦ hK) (hfd.and hfS) (hgd.and hgS)
    (hf0.trans hg0.symm)
  filter_upwards [key] with t ht
  exact congrArg Prod.fst ht

/-- If $\wp(a) = \wp(b)$ and $\wp'(a) = \wp'(b)$ then $\wp(a + z) = \wp(b + z)$ whenever both
sides are defined, by the identity theorem on the connected set where they are. -/
lemma weierstrassP_add_eq_add_of_eq {a b : ℂ} (ha : a ∉ L.lattice) (hb : b ∉ L.lattice)
    (h₁ : ℘[L] a = ℘[L] b) (h₂ : ℘'[L] a = ℘'[L] b) {z : ℂ} (hz : a + z ∉ L.lattice)
    (hz' : b + z ∉ L.lattice) : ℘[L] (a + z) = ℘[L] (b + z) := by
  set U : Set ℂ := {w | a + w ∉ L.lattice ∧ b + w ∉ L.lattice} with hU
  have hUeq : U = ((fun l ↦ l - a) '' L.lattice ∪ (fun l ↦ l - b) '' L.lattice)ᶜ := by
    ext w
    simp only [hU, mem_ofPred_eq, mem_compl_iff, mem_union, mem_image, not_or, not_exists]
    constructor
    · exact fun hw ↦ ⟨fun l ⟨hl, hlw⟩ ↦ hw.1 (by rwa [show a + w = l by rw [← hlw]; ring]),
        fun l ⟨hl, hlw⟩ ↦ hw.2 (by rwa [show b + w = l by rw [← hlw]; ring])⟩
    · exact fun hw ↦ ⟨fun hmem ↦ hw.1 (a + w) ⟨hmem, by ring⟩,
        fun hmem ↦ hw.2 (b + w) ⟨hmem, by ring⟩⟩
  have hUconn : IsPreconnected U := by
    rw [hUeq]
    exact Complex.isPreconnected_compl_of_countable
      ((L.countable_lattice.image _).union (L.countable_lattice.image _))
  have hF : AnalyticOnNhd ℂ (fun w ↦ ℘[L] (a + w)) U := fun w hw ↦
    (L.analyticOnNhd_weierstrassP _ hw.1).comp (by fun_prop)
  have hG : AnalyticOnNhd ℂ (fun w ↦ ℘[L] (b + w)) U := fun w hw ↦
    (L.analyticOnNhd_weierstrassP _ hw.2).comp (by fun_prop)
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), ℘[L] (a + w) = ℘[L] (b + w) := by
    have hT : Filter.Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (by filter_upwards [self_mem_nhdsWithin] with t ht using
          by simpa using (Complex.ofReal_ne_zero.mpr ht))
    exact hT.frequently (((L.eventually_weierstrassP_add_eq_add ha hb h₁ h₂).filter_mono
      nhdsWithin_le_nhds).frequently)
  have h0 : (0 : ℂ) ∈ U := by
    simp only [hU, mem_ofPred_eq, add_zero]
    exact ⟨ha, hb⟩
  exact hF.eqOn_of_preconnected_of_frequently_eq hG hUconn h0 hfreq ⟨hz, hz'⟩

/-- **The periods of $\wp$ are the lattice**: if $\wp(z + c) = \wp(z)$ whenever both sides are
defined, then $c \in \Lambda$. -/
theorem mem_lattice_of_forall_weierstrassP_add_eq {c : ℂ}
    (h : ∀ z, z ∉ L.lattice → z + c ∉ L.lattice → ℘[L] (z + c) = ℘[L] z) : c ∈ L.lattice := by
  by_contra hc
  have hnear : {w : ℂ | c - w ∉ L.lattice} ∈ 𝓝 (0 : ℂ) := by
    have hca : ContinuousAt (fun w : ℂ ↦ c - w) 0 := by fun_prop
    exact hca.preimage_mem_nhds (by simpa using L.isClosed_lattice.isOpen_compl.mem_nhds hc)
  have hev : ℘[L] =ᶠ[𝓝[≠] (0 : ℂ)] fun w ↦ ℘[L] (c - w) := by
    filter_upwards [L.eventually_notMem_lattice, mem_nhdsWithin_of_mem_nhds hnear] with w hw hw2
    have hnw : -w ∉ L.lattice := fun hmem ↦ hw (by simpa using neg_mem hmem)
    have hnwc : -w + c ∉ L.lattice := by rwa [show -w + c = c - w by ring]
    have hh := h (-w) hnw hnwc
    rw [show -w + c = c - w by ring, L.weierstrassP_neg] at hh
    exact hh.symm
  have hord : meromorphicOrderAt ℘[L] 0 = -2 := L.order_weierstrassP 0 (zero_mem _)
  have hpos : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun w ↦ ℘[L] (c - w)) 0 :=
    AnalyticAt.meromorphicOrderAt_nonneg
      ((L.analyticOnNhd_weierstrassP _ (by simpa using hc)).comp (by fun_prop))
  rw [← meromorphicOrderAt_congr hev, hord] at hpos
  exact absurd hpos (by decide)

/-- **$(\wp, \wp')$ is injective modulo the lattice.** -/
theorem sub_mem_lattice_of_weierstrassP_eq_of_derivWeierstrassP_eq {a b : ℂ} (ha : a ∉ L.lattice)
    (hb : b ∉ L.lattice) (h₁ : ℘[L] a = ℘[L] b) (h₂ : ℘'[L] a = ℘'[L] b) :
    a - b ∈ L.lattice := by
  refine L.mem_lattice_of_forall_weierstrassP_add_eq fun z hz hz' ↦ ?_
  have key := L.weierstrassP_add_eq_add_of_eq ha hb h₁ h₂ (z := z - b)
    (by rwa [show a + (z - b) = z + (a - b) by ring]) (by rwa [show b + (z - b) = z by ring])
  rwa [show a + (z - b) = z + (a - b) by ring, show b + (z - b) = z by ring] at key

/-- **The fibres of $\wp$**: $\wp(a) = \wp(b)$ if and only if $a \equiv \pm b \pmod \Lambda$. -/
theorem weierstrassP_eq_iff {a b : ℂ} (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) :
    ℘[L] a = ℘[L] b ↔ a - b ∈ L.lattice ∨ a + b ∈ L.lattice := by
  constructor
  · intro h
    have hsq : ℘'[L] a ^ 2 = ℘'[L] b ^ 2 := by
      rw [L.derivWeierstrassP_sq a ha, L.derivWeierstrassP_sq b hb, h]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
    · exact Or.inl (L.sub_mem_lattice_of_weierstrassP_eq_of_derivWeierstrassP_eq ha hb h h')
    · have hnb : -b ∉ L.lattice := fun hmem ↦ hb (by simpa using neg_mem hmem)
      have h1 : ℘[L] a = ℘[L] (-b) := by rw [L.weierstrassP_neg, h]
      have h2 : ℘'[L] a = ℘'[L] (-b) := by rw [L.derivWeierstrassP_neg, h']
      exact Or.inr (by simpa [sub_neg_eq_add] using
        L.sub_mem_lattice_of_weierstrassP_eq_of_derivWeierstrassP_eq ha hnb h1 h2)
  · rintro (h | h)
    · have key := L.weierstrassP_add_coe b ⟨a - b, h⟩
      rwa [show ((⟨a - b, h⟩ : L.lattice) : ℂ) = a - b from rfl,
        show b + (a - b) = a by ring] at key
    · have key := L.weierstrassP_add_coe (-b) ⟨a + b, h⟩
      rwa [show ((⟨a + b, h⟩ : L.lattice) : ℂ) = a + b from rfl,
        show -b + (a + b) = a by ring, L.weierstrassP_neg] at key

end PeriodPair

end
