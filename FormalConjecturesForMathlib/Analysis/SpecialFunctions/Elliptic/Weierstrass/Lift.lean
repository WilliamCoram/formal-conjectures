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

public import FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.IntegralPeriodLattice
public import FormalConjecturesForMathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.Existence
public import FormalConjecturesForMathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.HalfPeriods
public import FormalConjecturesForMathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.Surjective
public import FormalConjecturesForMathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import FormalConjecturesForMathlib.Topology.Algebra.Field
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

@[expose] public noncomputable section

/-!
# The elliptic integral inverts the Weierstrass function along paths

Let $\Lambda$ be a period lattice with curve $E_\Lambda : Y^2 = X^3 - \frac{g_2}{4} X -
\frac{g_3}{4}$ (`PeriodPair.weierstrassCurve`), on which $z \mapsto (\wp(z), \frac12 \wp'(z))$ is
the uniformisation (`PeriodPair.weierstrassPoint`). The invariant differential
$\omega = dX / (2Y)$ pulls back to $dz$: $d\wp = \wp' \, dz$ and $2Y = \wp'$.

Conversely, given a $C^1$ path $\gamma$ on $E_\Lambda$ avoiding the points of order two and a
point $z_0$ with $(\wp(z_0), \frac12 \wp'(z_0)) = \gamma(0)$, the *lift*
$$z(t) = z_0 + \int_0^t \omega(\gamma(u))(\gamma'(u)) \, du$$
(`PeriodPair.lift`) satisfies $(\wp(z(t)), \frac12 \wp'(z(t))) = \gamma(t)$ for all $t \in [0, 1]$
(`PeriodPair.weierstrassPoint_lift`): the elliptic integral is the inverse of $\wp$, continued
along the path. The proof is by continuous induction on $t$: the set of good $t$ is closed because
$\wp$ has poles on the lattice, so the lift cannot reach a lattice point while $\wp$ stays bounded,
and it is open to the right because near a good $t$ the local inverse of $\wp$ (which exists since
$\wp' \neq 0$ off the half-lattice) composed with the $X$-coordinate of $\gamma$ solves the same
differential equation as the lift, with the sign of $\wp'$ locked by continuity.

*References:*
- [DLMF](https://dlmf.nist.gov/23.6.iv), equation 23.6.36
- [Pas2017] Georgios Pastras. Four Lectures on Weierstrass Elliptic Function and Applications in
    Classical and Quantum Mechanics, equations (1.30)–(1.32), https://arxiv.org/abs/1706.07371
- [Mil2006] J. S. Milne. Elliptic Curves, Chapter III, Proposition 3.7,
    https://www.jmilne.org/math/Books/ectext6.pdf
-/

open Filter MeasureTheory Set Topology
open scoped unitInterval

namespace PeriodPair

variable (L : PeriodPair)

/- ## The uniformisation on affine points -/

/-- The affine point $(\wp(z), \frac12 \wp'(z))$ of the curve $Y^2 = X^3 - \frac{g_2}{4} X -
\frac{g_3}{4}$ of the lattice. -/
def weierstrassPoint (z : ℂ) : ℂ × ℂ := (℘[L] z, ℘'[L] z / 2)

/-- The $X$-coordinate of $(\wp(z), \frac12 \wp'(z))$ is $\wp(z)$. -/
@[simp]
lemma weierstrassPoint_fst (z : ℂ) : (L.weierstrassPoint z).1 = ℘[L] z := rfl

/-- The $Y$-coordinate of $(\wp(z), \frac12 \wp'(z))$ is $\frac12 \wp'(z)$. -/
@[simp]
lemma weierstrassPoint_snd (z : ℂ) : (L.weierstrassPoint z).2 = ℘'[L] z / 2 := rfl

/-- The uniformisation $z \mapsto (\wp(z), \frac12 \wp'(z))$ is $\Lambda$-periodic, since both
$\wp$ and $\wp'$ are. -/
lemma weierstrassPoint_add_coe (z : ℂ) (l : L.lattice) :
    L.weierstrassPoint (z + l) = L.weierstrassPoint z := by
  simp [weierstrassPoint, L.weierstrassP_add_coe, L.derivWeierstrassP_add_coe]

/-- Off the half-lattice, $(\wp(z), \frac12 \wp'(z))$ is an affine point of the curve of the
lattice which is not of order two. -/
lemma weierstrassPoint_mem_affineNonTwoTorsion {z : ℂ} (hz : 2 * z ∉ L.lattice) :
    L.weierstrassPoint z ∈ L.weierstrassCurve.affineNonTwoTorsion := by
  have hz' : z ∉ L.lattice := fun h ↦ hz (two_mul z ▸ add_mem h h)
  refine ⟨?_, ?_⟩
  · simp only [WeierstrassCurve.Affine.equation_iff, weierstrassPoint, weierstrassCurve,
      WeierstrassCurve.toAffine]
    linear_combination (L.derivWeierstrassP_sq z hz') / 4
  · simp only [weierstrassPoint, weierstrassCurve]
    exact fun hcon ↦ hz ((L.derivWeierstrassP_eq_zero_iff hz').mp (by linear_combination hcon))

/-- Off the lattice the uniformisation is differentiable, with derivative
$(\wp'(z), \frac12 \wp''(z))$; here $\wp'' = 6 \wp^2 - \frac{g_2}{2}$. -/
lemma hasDerivAt_weierstrassPoint {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassPoint (℘'[L] z, (6 * ℘[L] z ^ 2 - L.g₂ / 2) / 2) z :=
  (L.hasDerivAt_weierstrassP hz).prodMk ((L.hasDerivAt_derivWeierstrassP hz).div_const 2)

/-- The invariant differential $dX / (2Y)$ at $(\wp(z), \frac12 \wp'(z))$ is $dX / \wp'(z)$. -/
lemma invariantDifferential_weierstrassPoint (z : ℂ) (v : ℂ × ℂ) :
    L.weierstrassCurve.invariantDifferential (L.weierstrassPoint z) v = v.1 / ℘'[L] z := by
  simp only [WeierstrassCurve.invariantDifferential_apply, weierstrassPoint, weierstrassCurve]
  ring

/-- Off the lattice $\wp$ is *strictly* differentiable with derivative $\wp'$. This is the form
required by the inverse function theorem, which supplies the local inverse of $\wp$ used in
`PeriodPair.exists_localLift`. -/
lemma hasStrictDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasStrictDerivAt ℘[L] (℘'[L] z) z :=
  (L.hasDerivAt_weierstrassP hz).deriv ▸ (L.analyticOnNhd_weierstrassP z hz).hasStrictDerivAt

/- ## The lift of a path -/

variable {p q : ℂ × ℂ} (γ : Path p q)

/-- The lift of a path $\gamma$ on the curve of the lattice through $z_0$:
$z(t) = z_0 + \int_0^t \omega(\gamma(u))(\gamma'(u)) \, du$. -/
def lift (z₀ : ℂ) (t : ℝ) : ℂ :=
  z₀ + ∫ u in (0 : ℝ)..t, curveIntegralFun L.weierstrassCurve.invariantDifferential γ u

/-- The lift of a path through $z_0$ starts at $z_0$. -/
@[simp]
lemma lift_zero (z₀ : ℂ) : L.lift γ z₀ 0 = z₀ := by simp [lift]

/-- The lift of a path changes by the integral of the invariant differential along the path. -/
lemma lift_one (z₀ : ℂ) :
    L.lift γ z₀ 1 = z₀ + ∫ᶜ x in γ, L.weierstrassCurve.invariantDifferential x := by
  rw [lift, curveIntegral_def]

variable (hγ : ContDiffOn ℝ 1 γ.extend I) (hS : range γ ⊆ L.weierstrassCurve.affineNonTwoTorsion)
include hγ hS

/-- The integrand $u \mapsto \omega(\gamma(u))(\gamma'(u))$ defining the lift is continuous on
$[0, 1]$: the path is $C^1$ and $\omega = dX / (2Y)$ has no pole away from the points of order
two, which $\gamma$ avoids. -/
lemma continuousOn_curveIntegralFun_invariantDifferential :
    ContinuousOn (curveIntegralFun L.weierstrassCurve.invariantDifferential γ) I := by
  simp only [funext (curveIntegralFun_def L.weierstrassCurve.invariantDifferential γ)]
  exact ContinuousOn.clm_apply
    (L.weierstrassCurve.continuousOn_invariantDifferential.comp (by fun_prop)
      fun t _ ↦ hS (γ.extend_range ▸ Set.mem_range_self t))
    (hγ.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl)

/-- The fundamental theorem of calculus for the lift: $z'(t) = \omega(\gamma(t))(\gamma'(t))$
on $[0, 1]$. -/
lemma hasDerivWithinAt_lift (z₀ : ℂ) {t : ℝ} (ht : t ∈ I) : HasDerivWithinAt (L.lift γ z₀)
    (curveIntegralFun L.weierstrassCurve.invariantDifferential γ t) I t :=
  (intervalIntegral.integral_hasDerivWithinAt_Icc zero_lt_one
    (L.continuousOn_curveIntegralFun_invariantDifferential γ hγ hS) ht).const_add z₀

/-- The lift of a path is continuous on $[0, 1]$. -/
lemma continuousOn_lift (z₀ : ℂ) : ContinuousOn (L.lift γ z₀) I :=
  fun _t ht ↦ (L.hasDerivWithinAt_lift γ hγ hS z₀ ht).continuousWithinAt

/-- The set of times at which the lift covers the path is closed: $\wp$ has poles on the lattice,
so a limit of lifts covering the (bounded) path cannot lie on the lattice. -/
lemma isClosed_setOf_weierstrassPoint_lift_eq (z₀ : ℂ) : IsClosed
    ({t | L.lift γ z₀ t ∉ L.lattice ∧ L.weierstrassPoint (L.lift γ z₀ t) = γ.extend t} ∩ I) := by
  set S := {t | L.lift γ z₀ t ∉ L.lattice ∧ L.weierstrassPoint (L.lift γ z₀ t) = γ.extend t} ∩ I
  refine isClosed_of_closure_subset fun t ht ↦ ?_
  have htI : t ∈ I := isClosed_Icc.closure_subset (closure_mono Set.inter_subset_right ht)
  have hnb : (𝓝[S] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp ht
  have hlift : Tendsto (L.lift γ z₀) (𝓝[S] t) (𝓝 (L.lift γ z₀ t)) :=
    (L.continuousOn_lift γ hγ hS z₀ t htI).mono Set.inter_subset_right
  have hwp : Tendsto (fun u ↦ L.weierstrassPoint (L.lift γ z₀ u)) (𝓝[S] t) (𝓝 (γ.extend t)) :=
    Tendsto.congr' (eventuallyEq_of_mem self_mem_nhdsWithin fun _u hu ↦ hu.1.2).symm
      γ.continuous_extend.continuousWithinAt
  have hnotmem : L.lift γ z₀ t ∉ L.lattice := fun hmem ↦
    hwp.fst_nhds.not_tendsto (Metric.disjoint_nhds_cobounded _) <|
      (L.tendsto_weierstrassP_cobounded hmem).comp <|
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hlift <|
          eventually_of_mem self_mem_nhdsWithin fun _u hu hcon ↦ hu.1.1 (hcon ▸ hmem)
  exact ⟨⟨hnotmem, tendsto_nhds_unique
    ((L.hasDerivAt_weierstrassPoint hnotmem).continuousAt.tendsto.comp hlift) hwp⟩, htI⟩

omit hγ hS in
/-- If $x \notin \Lambda$ and $\wp(x)$ is the $X$-coordinate of an affine point $P$ of $E_\Lambda$,
then $\wp'(x)^2 = (2 Y(P))^2$, both being the value of $4 X^3 - g_2 X - g_3$ at $X(P)$. -/
private lemma derivWeierstrassP_sq_eq_sq {x : ℂ} (hx : x ∉ L.lattice) {P : ℂ × ℂ}
    (hP : P ∈ L.weierstrassCurve.affineNonTwoTorsion) (hxP : ℘[L] x = P.1) :
    ℘'[L] x ^ 2 = (2 * P.2) ^ 2 := by
  have hcurve := hP.1
  simp only [WeierstrassCurve.Affine.equation_iff, weierstrassCurve, WeierstrassCurve.toAffine]
    at hcurve
  rw [L.derivWeierstrassP_sq _ hx, hxP]
  linear_combination (-4 : ℂ) * hcurve

omit hγ in
/-- If $f$ is continuous at $t$, stays off $\Lambda$ near $t$, satisfies $\wp \circ f = X \circ
\gamma$ near $t$ and $\wp'(f(t)) = 2 Y(\gamma(t))$, then $\wp'(f(u)) = 2 Y(\gamma(u))$ for every
$u$ near $t$, since both sides square to the same thing and agree at $t$. -/
private lemma eventually_derivWeierstrassP_eq_two_mul {t : ℝ} {f : ℝ → ℂ} (hf : ContinuousAt f t)
    (hlat : ∀ᶠ u in 𝓝 t, f u ∉ L.lattice) (hX : ∀ᶠ u in 𝓝 t, ℘[L] (f u) = (γ.extend u).1)
    (hft : ℘'[L] (f t) = 2 * (γ.extend t).2) :
    ∀ᶠ u in 𝓝 t, ℘'[L] (f u) = 2 * (γ.extend u).2 := by
  have hlocus : ∀ u : ℝ, γ.extend u ∈ L.weierstrassCurve.affineNonTwoTorsion :=
    fun u ↦ hS (γ.extend_range ▸ Set.mem_range_self u)
  have hpc : ContinuousAt (fun y : ℂ ↦ ℘'[L] y) (f t) :=
    (L.hasDerivAt_derivWeierstrassP hlat.self_of_nhds).continuousAt
  have hf0 : ℘'[L] (f t) ≠ 0 := by
    rw [hft]; simpa [weierstrassCurve] using (hlocus t).2
  have hsq : ∀ᶠ u in 𝓝 t, ℘'[L] (f u) ^ 2 = (2 * (γ.extend u).2) ^ 2 := by
    filter_upwards [hlat, hX] with u hu3 hu1
    exact L.derivWeierstrassP_sq_eq_sq hu3 (hlocus u) hu1
  exact eventually_eq_of_sq_eq_sq (ContinuousAt.comp (f := f) (x := t) hpc hf) (by fun_prop)
    hft hf0 hsq

/-- If $\psi$ is a local left inverse of $\wp$ at a point $x \notin \Lambda$ lying over
$\gamma(u)$, then $u \mapsto \psi(X(\gamma(u)))$ satisfies the differential equation
$z'(u) = \omega(\gamma(u))(\gamma'(u))$ of `PeriodPair.lift` at $u$. -/
private lemma hasDerivWithinAt_localInverse_comp {ψ : ℂ → ℂ} {x : ℂ} (hx : x ∉ L.lattice)
    (hleft : ∀ᶠ y in 𝓝 x, ψ (℘[L] y) = y) {u : ℝ} (hu : u ∈ I)
    (hxX : ℘[L] x = (γ.extend u).1) (hxY : ℘'[L] x = 2 * (γ.extend u).2) :
    HasDerivWithinAt (fun u : ℝ ↦ ψ ((γ.extend u).1))
      (curveIntegralFun L.weierstrassCurve.invariantDifferential γ u) I u := by
  have hne : ℘'[L] x ≠ 0 := by
    rw [hxY]; simpa [weierstrassCurve] using (hS (γ.extend_range ▸ Set.mem_range_self u)).2
  have hψu : HasStrictDerivAt ψ (℘'[L] x)⁻¹ ((γ.extend u).1) := by
    have hh := (L.hasStrictDerivAt_weierstrassP hx).to_local_left_inverse hne hleft
    rwa [hxX] at hh
  have hXd : HasDerivWithinAt (fun u : ℝ ↦ (γ.extend u).1) ((derivWithin γ.extend I u).1) I u :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivWithinAt u
      (hγ.differentiableOn one_ne_zero u hu).hasDerivWithinAt
  have hcomp : HasDerivWithinAt (fun u : ℝ ↦ ψ ((γ.extend u).1))
      ((℘'[L] x)⁻¹ * (derivWithin γ.extend I u).1) I u :=
    hψu.hasDerivAt.comp_hasDerivWithinAt u hXd
  rw [curveIntegralFun_def]
  refine hcomp.congr_deriv ?_
  simp only [WeierstrassCurve.invariantDifferential_apply, weierstrassCurve, hxY, div_eq_inv_mul,
    zero_mul, add_zero]

/-- **Local lifting**: through a point $w \notin \Lambda$ over $\gamma(t)$ there is a local lift of
$\gamma$ solving the same differential equation as `PeriodPair.lift`, obtained from the local
inverse of $\wp$ at $w$ composed with the $X$-coordinate of $\gamma$, with the sign of $\wp'$
locked by continuity. -/
lemma exists_localLift {t : ℝ} (_ht : t ∈ I) {w : ℂ} (hw : w ∉ L.lattice)
    (heq : L.weierstrassPoint w = γ.extend t) : ∃ v : ℝ → ℂ, v t = w ∧
      ∀ᶠ u in 𝓝 t, (v u ∉ L.lattice ∧ L.weierstrassPoint (v u) = γ.extend u) ∧
        ∀ _hu : u ∈ I, HasDerivWithinAt v
          (curveIntegralFun L.weierstrassCurve.invariantDifferential γ u) I u := by
  have hwX : ℘[L] w = (γ.extend t).1 := congrArg Prod.fst heq
  have hwY : ℘'[L] w / 2 = (γ.extend t).2 := congrArg Prod.snd heq
  have hw' : ℘'[L] w ≠ 0 := by
    rw [show ℘'[L] w = 2 * (γ.extend t).2 by rw [← hwY]; ring]
    simpa [weierstrassCurve] using (hS (γ.extend_range ▸ Set.mem_range_self t)).2
  have hs := L.hasStrictDerivAt_weierstrassP hw
  set ψ := HasStrictDerivAt.localInverse ℘[L] (℘'[L] w) w hs hw'
  obtain ⟨U, hUsub, hUopen, hwU⟩ := eventually_nhds_iff.mp (hs.eventually_left_inverse hw')
  have hψt : ψ ((γ.extend t).1) = w := by
    rw [← hwX]; exact (hs.eventually_left_inverse hw').self_of_nhds
  have hXcont : ContinuousAt (fun u : ℝ ↦ (γ.extend u).1) t :=
    (continuous_fst.comp γ.continuous_extend).continuousAt
  have hXt : Tendsto (fun u : ℝ ↦ (γ.extend u).1) (𝓝 t) (𝓝 (℘[L] w)) := by
    rw [hwX]; exact hXcont.tendsto
  have hψcont : ContinuousAt ψ ((γ.extend t).1) := by
    rw [← hwX]; exact (hs.to_localInverse hw').hasDerivAt.continuousAt
  have hvcont : ContinuousAt (fun u : ℝ ↦ ψ ((γ.extend u).1)) t :=
    ContinuousAt.comp (f := fun u : ℝ ↦ (γ.extend u).1) (x := t) hψcont hXcont
  refine ⟨fun u ↦ ψ ((γ.extend u).1), hψt, ?_⟩
  have e1 : ∀ᶠ u in 𝓝 t, ℘[L] (ψ ((γ.extend u).1)) = (γ.extend u).1 :=
    hXt.eventually (hs.eventually_right_inverse hw')
  have e2 : ∀ᶠ u in 𝓝 t, ψ ((γ.extend u).1) ∈ U := by
    refine hvcont.eventually ?_
    change ∀ᶠ y in 𝓝 (ψ ((γ.extend t).1)), y ∈ U
    rw [hψt]
    exact hUopen.mem_nhds hwU
  have e3 : ∀ᶠ u in 𝓝 t, ψ ((γ.extend u).1) ∈ (L.lattice : Set ℂ)ᶜ := by
    refine hvcont.eventually ?_
    change ∀ᶠ y in 𝓝 (ψ ((γ.extend t).1)), y ∈ (L.lattice : Set ℂ)ᶜ
    rw [hψt]
    exact L.isClosed_lattice.isOpen_compl.mem_nhds hw
  have hft : ℘'[L] (ψ ((γ.extend t).1)) = 2 * (γ.extend t).2 := by rw [hψt, ← hwY]; ring
  have e4 : ∀ᶠ u in 𝓝 t, ℘'[L] (ψ ((γ.extend u).1)) = 2 * (γ.extend u).2 :=
    L.eventually_derivWeierstrassP_eq_two_mul γ hS hvcont e3 e1 hft
  filter_upwards [e1, e2, e3, e4] with u hu1 hu2 hu3 hu4
  refine ⟨⟨hu3, Prod.ext hu1 ?_⟩, fun hu ↦ ?_⟩
  · change ℘'[L] (ψ ((γ.extend u).1)) / 2 = (γ.extend u).2
    rw [hu4]; ring
  exact L.hasDerivWithinAt_localInverse_comp γ hγ hS hu3
    (Filter.eventually_of_mem (hUopen.mem_nhds hu2) hUsub) hu hu1 hu4

/-- The set of times at which the lift covers the path is open to the right. -/
lemma eventually_weierstrassPoint_lift_eq (z₀ : ℂ) {t : ℝ} (ht : t ∈ I) (ht1 : t < 1)
    (hlift : L.lift γ z₀ t ∉ L.lattice) (heq : L.weierstrassPoint (L.lift γ z₀ t) = γ.extend t) :
    ∀ᶠ u in 𝓝[>] t, L.lift γ z₀ u ∉ L.lattice ∧
      L.weierstrassPoint (L.lift γ z₀ u) = γ.extend u := by
  obtain ⟨v, hvt, hv⟩ := L.exists_localLift γ hγ hS ht hlift heq
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hv
  obtain ⟨d, hd0, hdε, hd1⟩ : ∃ d : ℝ, 0 < d ∧ d < ε ∧ t + d ≤ 1 :=
    ⟨min (ε / 2) ((1 - t) / 2), by positivity, (min_le_left _ _).trans_lt (by linarith),
      by linarith [min_le_right (ε / 2) ((1 - t) / 2)]⟩
  have hsub : Set.Icc t (t + d) ⊆ I := fun u hu ↦ ⟨ht.1.trans hu.1, hu.2.trans hd1⟩
  have hballu : ∀ u ∈ Set.Icc t (t + d), dist u t < ε := fun u hu ↦ by
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
    linarith [hu.2]
  have hfd : ∀ u ∈ Set.Icc t (t + d), HasDerivWithinAt (L.lift γ z₀)
      (curveIntegralFun L.weierstrassCurve.invariantDifferential γ u) (Set.Icc t (t + d)) u :=
    fun u hu ↦ (L.hasDerivWithinAt_lift γ hγ hS z₀ (hsub hu)).mono hsub
  have hvd : ∀ u ∈ Set.Icc t (t + d), HasDerivWithinAt v
      (curveIntegralFun L.weierstrassCurve.invariantDifferential γ u) (Set.Icc t (t + d)) u :=
    fun u hu ↦ ((hball (hballu u hu)).2 (hsub hu)).mono hsub
  have hkey : ∀ y ∈ Set.Icc t (t + d), L.lift γ z₀ y = v y := by
    refine eq_of_derivWithin_eq (fun u hu ↦ (hfd u hu).differentiableWithinAt)
      (fun u hu ↦ (hvd u hu).differentiableWithinAt) (fun u hu ↦ ?_) hvt.symm
    have huc : u ∈ Set.Icc t (t + d) := Set.mem_Icc_of_Ico hu
    rw [(hfd u huc).derivWithin (uniqueDiffOn_Icc (by linarith) u huc),
      (hvd u huc).derivWithin (uniqueDiffOn_Icc (by linarith) u huc)]
  filter_upwards [Ioc_mem_nhdsGT (by linarith : t < t + d)] with u hu
  have hu' : u ∈ Set.Icc t (t + d) := ⟨hu.1.le, hu.2⟩
  exact hkey u hu' ▸ (hball (hballu u hu')).1

/-- The two conclusions of `PeriodPair.weierstrassPoint_lift` and
`PeriodPair.lift_notMem_lattice`, proved together because the continuous induction on $t$ needs
both: staying off the lattice is what keeps $\wp$ finite, and covering $\gamma$ is what keeps the
lift off the lattice. -/
private lemma lift_spec {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) (hp : L.weierstrassPoint z₀ = p)
    {t : ℝ} (ht : t ∈ I) : L.lift γ z₀ t ∉ L.lattice ∧
      L.weierstrassPoint (L.lift γ z₀ t) = γ.extend t :=
  IsClosed.Icc_subset_of_forall_mem_nhdsWithin
    (L.isClosed_setOf_weierstrassPoint_lift_eq γ hγ hS z₀) ⟨by simpa using hz₀, by simp [hp]⟩
    (fun x hx ↦ L.eventually_weierstrassPoint_lift_eq γ hγ hS z₀ ⟨hx.2.1, hx.2.2.le⟩ hx.2.2
      hx.1.1 hx.1.2) ht

/-- **The elliptic integral inverts $\wp$ along a path**: the lift of $\gamma$ through $z_0$
covers $\gamma$. -/
theorem weierstrassPoint_lift {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) (hp : L.weierstrassPoint z₀ = p)
    {t : ℝ} (ht : t ∈ I) : L.weierstrassPoint (L.lift γ z₀ t) = γ.extend t :=
  (L.lift_spec γ hγ hS hz₀ hp ht).2

/-- The lift of $\gamma$ through $z_0$ never meets the lattice, so $\wp$ and $\wp'$ stay finite
along it. -/
lemma lift_notMem_lattice {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) (hp : L.weierstrassPoint z₀ = p)
    {t : ℝ} (ht : t ∈ I) : L.lift γ z₀ t ∉ L.lattice :=
  (L.lift_spec γ hγ hS hz₀ hp ht).1

end PeriodPair

end
