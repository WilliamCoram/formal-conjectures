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

public import FormalConjecturesForMathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.Injective
public import FormalConjecturesForMathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.Lift

@[expose] public noncomputable section

/-!
# The periods of the invariant differential of the curve of a lattice

Let $\Lambda$ be a period lattice with curve $E_\Lambda : Y^2 = X^3 - \frac{g_2}{4} X -
\frac{g_3}{4}$. The integrals of the invariant differential $dX / (2Y)$ along the $C^1$ loops on
$E_\Lambda$ avoiding the points of order two are exactly the elements of $\Lambda$
(`PeriodPair.integralPeriodLattice_weierstrassCurve`).

* Every $\lambda \in \Lambda$ is such an integral: choose $z_0$ so that the line
  $z_0 + \mathbb{R} \lambda$ avoids the half-lattice
  (`PeriodPair.exists_forall_two_mul_add_mul_notMem_lattice`); then
  $t \mapsto (\wp(z_0 + t\lambda), \frac12 \wp'(z_0 + t\lambda))$ is a loop
  (`PeriodPair.weierstrassLoop`) along which the invariant differential pulls back to
  $\lambda \, dt$ (`PeriodPair.curveIntegral_weierstrassLoop`).
* Every such integral is in $\Lambda$: lift the loop through a point $z_0$ over its base point,
  which exists since $(\wp, \wp')$ is surjective; the lift ends at a point over the same base
  point, so it differs from $z_0$ by a lattice element since $(\wp, \wp')$ is injective modulo
  $\Lambda$; and the difference is the integral.

*References:*
- [DLMF](https://dlmf.nist.gov/23.6.iv), equations 23.6.34–23.6.36
- [LMFDB](https://www.lmfdb.org/knowledge/show/ec.q.period_lattice), knowl `ec.q.period_lattice`
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, Chapter VI §1
    and Proposition 3.6, https://link.springer.com/book/10.1007/978-0-387-09494-6
-/

open Filter MeasureTheory Set Topology
open scoped unitInterval

namespace PeriodPair

variable (L : PeriodPair)

/- ## Lattice elements are periods -/

/-- For every $\lambda$ there is a line $z_0 + \mathbb{R} \lambda$ avoiding the half-lattice
$\frac12 \Lambda$, which is countable. -/
lemma exists_forall_two_mul_add_mul_notMem_lattice (l : ℂ) :
    ∃ z₀ : ℂ, ∀ t : ℝ, 2 * (z₀ + t * l) ∉ L.lattice := by
  set H : Set ℂ := (fun x : ℂ ↦ x / 2) '' (L.lattice : Set ℂ) with hH
  have hHc : H.Countable := L.countable_lattice.image _
  have hmem : ∀ z : ℂ, 2 * z ∈ L.lattice → z ∈ H := fun z hz ↦ ⟨2 * z, hz, by ring⟩
  rcases eq_or_ne l 0 with rfl | hl
  · obtain ⟨z₀, hz₀⟩ := (hHc.dense_compl ℂ).nonempty
    exact ⟨z₀, fun t hcon ↦ hz₀ (by simpa using hmem _ hcon)⟩
  · have hl' : (starRingEnd ℂ) l ≠ 0 := by simpa using hl
    have hll : (starRingEnd ℂ) l * l ≠ 0 := mul_ne_zero hl' hl
    have him : ((starRingEnd ℂ) l * l).im = 0 := by
      simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
    set φ : ℂ → ℝ := fun z ↦ ((starRingEnd ℂ) l * z).im with hφ
    obtain ⟨c, hc⟩ := ((hHc.image φ).dense_compl ℝ).nonempty
    set z₀ : ℂ := Complex.I * (c : ℂ) * l / ((starRingEnd ℂ) l * l) with hz₀def
    have hkey : ∀ t : ℝ, φ (z₀ + (t : ℂ) * l) = c := by
      intro t
      have h1 : (starRingEnd ℂ) l * (z₀ + (t : ℂ) * l)
          = Complex.I * (c : ℂ) + (t : ℂ) * ((starRingEnd ℂ) l * l) := by
        rw [hz₀def]; field_simp
      show ((starRingEnd ℂ) l * (z₀ + (t : ℂ) * l)).im = c
      rw [h1]
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, him]
      ring
    exact ⟨z₀, fun t hcon ↦ hc ⟨z₀ + (t : ℂ) * l, hmem _ hcon, hkey t⟩⟩

/-- The loop $t \mapsto (\wp(z_0 + t\lambda), \frac12 \wp'(z_0 + t\lambda))$, $t \in [0, 1]$, on
the curve of the lattice, for a period $\lambda$ and a line $z_0 + \mathbb{R}\lambda$ avoiding
the half-lattice. -/
def weierstrassLoop (z₀ l : ℂ) (h : ∀ t : ℝ, 2 * (z₀ + t * l) ∉ L.lattice) (hl : l ∈ L.lattice) :
    Path (L.weierstrassPoint z₀) (L.weierstrassPoint z₀) where
  toFun t := L.weierstrassPoint (z₀ + t * l)
  continuous_toFun := by
    have hz : ∀ t : ℝ, z₀ + (t : ℂ) * l ∉ L.lattice :=
      fun t hm ↦ h t (by rw [two_mul]; exact add_mem hm hm)
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    exact ContinuousAt.comp (f := fun s : I ↦ z₀ + ((s : ℝ) : ℂ) * l) (x := t)
      (L.hasDerivAt_weierstrassPoint (hz (t : ℝ))).continuousAt (by fun_prop)
  source' := by simp
  target' := by
    have := L.weierstrassPoint_add_coe z₀ ⟨l, hl⟩
    simpa using this

variable {z₀ l : ℂ} (h : ∀ t : ℝ, 2 * (z₀ + t * l) ∉ L.lattice) (hl : l ∈ L.lattice)

@[simp]
lemma weierstrassLoop_apply (t : I) :
    L.weierstrassLoop z₀ l h hl t = L.weierstrassPoint (z₀ + t * l) :=
  rfl

lemma weierstrassLoop_extend (t : ℝ) (ht : t ∈ I) :
    (L.weierstrassLoop z₀ l h hl).extend t = L.weierstrassPoint (z₀ + t * l) :=
  Path.extend_extends' _ ⟨t, ht⟩

lemma contDiffOn_weierstrassLoop_extend :
    ContDiffOn ℝ 1 (L.weierstrassLoop z₀ l h hl).extend I := by
  have hz : ∀ t : ℝ, z₀ + (t : ℂ) * l ∉ L.lattice :=
    fun t hm ↦ h t (by rw [two_mul]; exact add_mem hm hm)
  have hana : ContDiffOn ℂ 1 L.weierstrassPoint ((L.lattice : Set ℂ)ᶜ) := by
    have hud : UniqueDiffOn ℂ ((L.lattice : Set ℂ)ᶜ) :=
      L.isClosed_lattice.isOpen_compl.uniqueDiffOn
    refine ContDiffOn.prodMk (AnalyticOnNhd.contDiffOn L.analyticOnNhd_weierstrassP hud) ?_
    exact (AnalyticOnNhd.contDiffOn L.analyticOnNhd_derivWeierstrassP hud).div_const 2
  have h1 : ContDiff ℝ 1 (fun t : ℝ ↦ (t : ℂ)) := Complex.ofRealCLM.contDiff
  have hline : ContDiff ℝ 1 (fun t : ℝ ↦ z₀ + (t : ℂ) * l) :=
    ContDiff.add contDiff_const (h1.mul contDiff_const)
  refine ContDiffOn.congr ?_ (fun t ht ↦ L.weierstrassLoop_extend h hl t ht)
  exact (hana.restrict_scalars ℝ).comp hline.contDiffOn fun t _ ↦ hz t

lemma range_weierstrassLoop_subset :
    range (L.weierstrassLoop z₀ l h hl) ⊆ L.weierstrassCurve.affineNonTwoTorsion := by
  rintro _ ⟨t, rfl⟩
  exact L.weierstrassPoint_mem_affineNonTwoTorsion (h (t : ℝ))

/-- Along the loop $t \mapsto (\wp(z_0 + t\lambda), \frac12 \wp'(z_0 + t\lambda))$ the invariant
differential pulls back to $\lambda \, dt$, so its integral is $\lambda$. -/
lemma curveIntegral_weierstrassLoop :
    ∫ᶜ x in L.weierstrassLoop z₀ l h hl, L.weierstrassCurve.invariantDifferential x = l := by
  have hz : ∀ t : ℝ, z₀ + (t : ℂ) * l ∉ L.lattice :=
    fun t hm ↦ h t (by rw [two_mul]; exact add_mem hm hm)
  have hne : ∀ t : ℝ, ℘'[L] (z₀ + (t : ℂ) * l) ≠ 0 := fun t hcon ↦
    h t ((L.derivWeierstrassP_eq_zero_iff (hz t)).mp hcon)
  have key : Set.EqOn (fun t : ℝ ↦ L.weierstrassCurve.invariantDifferential
      ((L.weierstrassLoop z₀ l h hl).extend t)
      (deriv (L.weierstrassLoop z₀ l h hl).extend t)) (fun _ ↦ l) (Set.Ioo 0 1) := by
    intro t ht
    have hev : (L.weierstrassLoop z₀ l h hl).extend =ᶠ[𝓝 t]
        fun s : ℝ ↦ L.weierstrassPoint (z₀ + (s : ℂ) * l) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact L.weierstrassLoop_extend h hl s ⟨hs.1.le, hs.2.le⟩
    have hofR : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have hlin : HasDerivAt (fun s : ℝ ↦ z₀ + (s : ℂ) * l) l t := by
      simpa using ((hofR.mul_const l).const_add z₀)
    have hd : HasDerivAt (fun s : ℝ ↦ L.weierstrassPoint (z₀ + (s : ℂ) * l))
        (l • (℘'[L] (z₀ + (t : ℂ) * l),
          (6 * ℘[L] (z₀ + (t : ℂ) * l) ^ 2 - L.g₂ / 2) / 2)) t :=
      HasDerivAt.scomp t (L.hasDerivAt_weierstrassPoint (hz t)) hlin
    show L.weierstrassCurve.invariantDifferential ((L.weierstrassLoop z₀ l h hl).extend t)
      (deriv (L.weierstrassLoop z₀ l h hl).extend t) = l
    rw [hev.deriv_eq, hd.deriv, L.weierstrassLoop_extend h hl t ⟨ht.1.le, ht.2.le⟩,
      L.invariantDifferential_weierstrassPoint]
    simp only [Prod.smul_fst, smul_eq_mul]
    rw [mul_div_assoc, div_self (hne t), mul_one]
  rw [curveIntegral_eq_intervalIntegral_deriv, intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo key]
  simp

theorem mem_integralPeriodLattice_of_mem_lattice {l : ℂ} (hl : l ∈ L.lattice) :
    l ∈ L.weierstrassCurve.integralPeriodLattice := by
  obtain ⟨z₀, hz₀⟩ := L.exists_forall_two_mul_add_mul_notMem_lattice l
  rw [← L.curveIntegral_weierstrassLoop hz₀ hl]
  exact curveIntegral_mem_curveIntegralPeriods _ (L.contDiffOn_weierstrassLoop_extend hz₀ hl)
    (L.range_weierstrassLoop_subset hz₀ hl)

/- ## Periods are lattice elements -/

theorem mem_lattice_of_mem_integralPeriodLattice {w : ℂ}
    (hw : w ∈ L.weierstrassCurve.integralPeriodLattice) : w ∈ L.lattice := by
  obtain ⟨p, γ, hγ, hSγ, rfl⟩ := hw
  have hp : p ∈ L.weierstrassCurve.affineNonTwoTorsion := hSγ γ.source_mem_range
  have hcurve := hp.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  simp only [weierstrassCurve, WeierstrassCurve.toAffine] at hcurve
  have heq : (2 * p.2) ^ 2 = 4 * p.1 ^ 3 - L.g₂ * p.1 - L.g₃ := by linear_combination 4 * hcurve
  obtain ⟨z₀, hz₀, hx, hy⟩ := L.exists_weierstrassP_eq_and_derivWeierstrassP_eq heq
  have hpt : L.weierstrassPoint z₀ = p := Prod.ext hx (by
    show ℘'[L] z₀ / 2 = p.2
    rw [hy]; ring)
  have hone : (1 : ℝ) ∈ I := ⟨zero_le_one, le_rfl⟩
  have h1 := L.weierstrassPoint_lift γ hγ hSγ hz₀ hpt hone
  have h1' := L.lift_notMem_lattice γ hγ hSγ hz₀ hpt hone
  rw [Path.extend_one] at h1
  have h1p : L.weierstrassPoint (L.lift γ z₀ 1) = L.weierstrassPoint z₀ := h1.trans hpt.symm
  have hx1 : ℘[L] (L.lift γ z₀ 1) = ℘[L] z₀ := congrArg Prod.fst h1p
  have hy1 : ℘'[L] (L.lift γ z₀ 1) = ℘'[L] z₀ := by
    have h2 : ℘'[L] (L.lift γ z₀ 1) / 2 = ℘'[L] z₀ / 2 := congrArg Prod.snd h1p
    linear_combination 2 * h2
  have hsub := L.sub_mem_lattice_of_weierstrassP_eq_of_derivWeierstrassP_eq h1' hz₀ hx1 hy1
  rwa [L.lift_one, add_sub_cancel_left] at hsub

/-- **The periods of the curve of a lattice are the lattice.** -/
theorem integralPeriodLattice_weierstrassCurve :
    L.weierstrassCurve.integralPeriodLattice = (L.lattice : Set ℂ) :=
  Set.ext fun _ ↦ ⟨L.mem_lattice_of_mem_integralPeriodLattice,
    L.mem_integralPeriodLattice_of_mem_lattice⟩

end PeriodPair

end
