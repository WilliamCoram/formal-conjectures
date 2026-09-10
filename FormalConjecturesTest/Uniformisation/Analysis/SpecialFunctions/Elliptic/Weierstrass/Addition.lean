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

public import FormalConjecturesTest.Period.Analysis.SpecialFunctions.Elliptic.Weierstrass.Injective
public import FormalConjecturesTest.Uniformisation.Analysis.SpecialFunctions.Elliptic.Weierstrass.Laurent

@[expose] public noncomputable section

/-!
# The addition theorem for the Weierstrass `℘`-function

For a period lattice $\Lambda$ and $z, w \notin \Lambda$ with $z + w \notin \Lambda$ and
$\wp(z) \ne \wp(w)$,
$$\wp(z + w) = \frac14\Big(\frac{\wp'(z) - \wp'(w)}{\wp(z) - \wp(w)}\Big)^2 - \wp(z) - \wp(w)$$
(`PeriodPair.weierstrassP_add`), together with the companion formula for $\wp'(z + w)$
(`PeriodPair.derivWeierstrassP_add`); and for $2z \notin \Lambda$ the duplication formulas
(`PeriodPair.weierstrassP_two_mul`, `PeriodPair.derivWeierstrassP_two_mul`). In the coordinates
$(x, y) = (\wp, \tfrac12 \wp')$ on the curve $y^2 = x^3 - \tfrac{g_2}{4}x - \tfrac{g_3}{4}$ these
say that $z \mapsto (\wp(z), \tfrac12 \wp'(z))$ turns addition of complex numbers into the
chord-and-tangent law: the addition formula is Mathlib's `WeierstrassCurve.Affine.addX` with the
chord slope $(y_1 - y_2)/(x_1 - x_2)$, the duplication formula is its tangent case. That translation
is made in `Weierstrass/Uniformization.lean`.

## The proof: Euler's route, without the argument principle

The textbook proof ([Sil2009, VI.3.6], [WW1927, §20.3]) locates the third zero of the elliptic
function $\wp' - a\wp - b$ through the residue theorem, the zeros of an elliptic function summing
to a lattice point. Mathlib has no argument principle, so we argue as Euler did for the addition
theorem of elliptic integrals ([WW1927, §22.7]). Fix $s = z + w \notin \Lambda$ and consider
$$G(z) = \frac14\Big(\frac{\wp'(z) - \wp'(s - z)}{\wp(z) - \wp(s - z)}\Big)^2
  - \wp(z) - \wp(s - z)$$
(`PeriodPair.eulerG`) on the open set where every term is defined (`PeriodPair.eulerDomain`).
Its derivative vanishes identically (`PeriodPair.hasDerivAt_eulerG`): after the quotient rule this
is a polynomial identity in $\wp, \wp'$ at $z$ and $s - z$ modulo $\wp'^2 = 4\wp^3 - g_2\wp - g_3$
and $\wp'' = 6\wp^2 - \tfrac12 g_2$. The domain is connected, its complement being countable, so
$G$ is constant; and letting $z \to 0$, where $\wp(z) = z^{-2} + O(z^2)$, the constant is seen to
be $\wp(s)$ (`PeriodPair.tendsto_eulerG_zero`). The formula for $\wp'(z + w)$ follows by
differentiating in $z$, and the duplication formulas are the limits $w \to z$ of the addition
formulas (`PeriodPair.tendsto_chordSlope_self`).

## Source correspondence

| here | in the sources |
|---|---|
| `weierstrassP_add` | the addition theorem, [Sil2009, VI.3.6(b)], [WW1927, §20.3] |
| `weierstrassP_two_mul` | the duplication formula, [WW1927, §20.311] |
| `eulerG`, `hasDerivAt_eulerG` | Euler's differential-equation argument, [WW1927, §22.7] |
| `tendsto_eulerG_zero` | the constant of integration, via the Laurent expansion [Sil2009, VI.3.5] |

*References:*
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, VI.3.5–3.6
- [WW1927] E. T. Whittaker, G. N. Watson. A Course of Modern Analysis, 4th edition, §§20.3, 20.311,
    22.7
-/

open Filter Topology Set

namespace PeriodPair

variable (L : PeriodPair)

/- ## Two polynomial identities -/

/-- If $(x_1, y_1)$ and $(x_2, y_2)$ satisfy $y^2 = 4x^3 - g_2 x - g_3$, then
$N'D - ND' = 2D^3$ for $N = y_1 - y_2$, $D = x_1 - x_2$ and the derivatives along the flow
$x_i' = \pm y_i$, $y_i' = \pm(6x_i^2 - g_2/2)$: the numerator of $\tfrac{d}{dz}\,\mathrm{eulerG}$
vanishes. -/
private lemma euler_slope_identity {x₁ x₂ y₁ y₂ g₂ g₃ : ℂ}
    (h₁ : y₁ ^ 2 = 4 * x₁ ^ 3 - g₂ * x₁ - g₃) (h₂ : y₂ ^ 2 = 4 * x₂ ^ 3 - g₂ * x₂ - g₃) :
    (6 * (x₁ ^ 2 + x₂ ^ 2) - g₂) * (x₁ - x₂) - (y₁ - y₂) * (y₁ + y₂) = 2 * (x₁ - x₂) ^ 3 := by
  linear_combination h₂ - h₁

/-- The companion identity for the derivative of the chord slope at fixed second point:
$\tfrac{d}{dz}\big(N/D\big) = -\tfrac12 (N/D)^2 + 4x_1 + 2x_2$. -/
private lemma euler_tangency_identity {x₁ x₂ y₁ y₂ g₂ g₃ : ℂ}
    (h₁ : y₁ ^ 2 = 4 * x₁ ^ 3 - g₂ * x₁ - g₃) (h₂ : y₂ ^ 2 = 4 * x₂ ^ 3 - g₂ * x₂ - g₃) :
    2 * ((6 * x₁ ^ 2 - g₂ / 2) * (x₁ - x₂) - (y₁ - y₂) * y₁)
      = -(y₁ - y₂) ^ 2 + 2 * (4 * x₁ + 2 * x₂) * (x₁ - x₂) ^ 2 := by
  linear_combination h₂ - h₁

/- ## Euler's function and its domain -/

/-- The chord slope between the points over `z` and `s - z`, as a function of `z`. -/
def eulerSlope (s z : ℂ) : ℂ := (℘'[L] z - ℘'[L] (s - z)) / (℘[L] z - ℘[L] (s - z))

/-- Euler's function: the candidate value for `℘ s`, as a function of the split point `z`. The
addition theorem is the statement that it is constant, equal to `℘ s`, on `eulerDomain s`. -/
def eulerG (s z : ℂ) : ℂ := L.eulerSlope s z ^ 2 / 4 - ℘[L] z - ℘[L] (s - z)

/-- The natural domain of `eulerG s`: both points off the lattice, with distinct `℘`-values. -/
def eulerDomain (s : ℂ) : Set ℂ :=
  {z | z ∉ L.lattice ∧ s - z ∉ L.lattice ∧ ℘[L] z ≠ ℘[L] (s - z)}

/-- `eulerDomain s` is open: its three defining conditions are open conditions. -/
lemma isOpen_eulerDomain (s : ℂ) : IsOpen (L.eulerDomain s) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz, hsz, hne⟩
  have hc : ContinuousAt (fun w : ℂ ↦ ℘[L] (s - w)) z :=
    ContinuousAt.comp (f := fun w : ℂ ↦ s - w) (x := z)
      (L.analyticOnNhd_weierstrassP (s - z) hsz).continuousAt
      (continuousAt_const.sub continuousAt_id)
  filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz,
    (continuousAt_const.sub continuousAt_id).eventually_mem
      (L.isClosed_lattice.isOpen_compl.mem_nhds hsz),
    ((L.analyticOnNhd_weierstrassP z hz).continuousAt.sub hc).eventually_ne
      (sub_ne_zero.mpr hne)] with w hw1 hw2 hw3
  exact ⟨hw1, hw2, sub_ne_zero.mp hw3⟩

/-- Off the lattice, the complement of `eulerDomain s` is countable: by `weierstrassP_eq_iff`,
`℘ z = ℘ (s - z)` forces `2 * z - s ∈ Λ`. -/
lemma countable_compl_eulerDomain {s : ℂ} (hs : s ∉ L.lattice) :
    (L.eulerDomain s)ᶜ.Countable := by
  have h2 : Function.Injective fun z : ℂ ↦ 2 * z - s :=
    fun a b h ↦ mul_left_cancel₀ two_ne_zero (sub_left_injective h)
  refine ((L.countable_lattice.union
    (L.countable_lattice.preimage
      (sub_right_injective : Function.Injective fun z : ℂ ↦ s - z))).union
    (L.countable_lattice.preimage h2)).mono fun z hz ↦ ?_
  by_contra hcon
  simp only [mem_union, mem_preimage, SetLike.mem_coe, not_or] at hcon
  obtain ⟨⟨hzΛ, hsz⟩, h2z⟩ := hcon
  refine hz ⟨hzΛ, hsz, fun heq ↦ ?_⟩
  rcases (L.weierstrassP_eq_iff hzΛ hsz).mp heq with h | h
  · exact h2z (by rwa [show 2 * z - s = z - (s - z) by ring])
  · exact hs (by rwa [show z + (s - z) = s by ring] at h)

/-- `eulerDomain s` is connected, being the complement of a countable set. -/
lemma isPreconnected_eulerDomain {s : ℂ} (hs : s ∉ L.lattice) :
    IsPreconnected (L.eulerDomain s) := by
  rw [← compl_compl (L.eulerDomain s)]
  exact Complex.isPreconnected_compl_of_countable (L.countable_compl_eulerDomain hs)

/-- `0` lies in the closure of `eulerDomain s`, which is dense. -/
lemma mem_closure_eulerDomain {s : ℂ} (hs : s ∉ L.lattice) :
    (0 : ℂ) ∈ closure (L.eulerDomain s) := by
  have h := (L.countable_compl_eulerDomain hs).dense_compl ℂ
  rw [compl_compl] at h
  exact h 0

/- ## `eulerG` is constant, and the constant is `℘ s` -/

/-- **Euler's function is locally constant**: its derivative vanishes on `eulerDomain s`. After
the quotient rule, this is `euler_slope_identity`. -/
lemma hasDerivAt_eulerG {s z : ℂ} (hz : z ∈ L.eulerDomain s) : HasDerivAt (L.eulerG s) 0 z := by
  obtain ⟨hz1, hsz, hne⟩ := hz
  have hD0 : ℘[L] z - ℘[L] (s - z) ≠ 0 := sub_ne_zero.mpr hne
  have haff : HasDerivAt (fun u : ℂ ↦ s - u) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub s
  have hPc : HasDerivAt (fun u : ℂ ↦ ℘[L] (s - u)) (-℘'[L] (s - z)) z :=
    ((L.hasDerivAt_weierstrassP hsz).comp z haff).congr_deriv (by ring)
  have hPc' : HasDerivAt (fun u : ℂ ↦ ℘'[L] (s - u)) (-(6 * ℘[L] (s - z) ^ 2 - L.g₂ / 2)) z :=
    ((L.hasDerivAt_derivWeierstrassP hsz).comp z haff).congr_deriv (by ring)
  have hN : HasDerivAt (fun u : ℂ ↦ ℘'[L] u - ℘'[L] (s - u))
      (6 * (℘[L] z ^ 2 + ℘[L] (s - z) ^ 2) - L.g₂) z :=
    ((L.hasDerivAt_derivWeierstrassP hz1).sub hPc').congr_deriv (by ring)
  have hD : HasDerivAt (fun u : ℂ ↦ ℘[L] u - ℘[L] (s - u)) (℘'[L] z + ℘'[L] (s - z)) z :=
    ((L.hasDerivAt_weierstrassP hz1).sub hPc).congr_deriv (by ring)
  have hkey := euler_slope_identity (L.derivWeierstrassP_sq z hz1)
    (L.derivWeierstrassP_sq (s - z) hsz)
  have hG := ((((hN.div hD hD0).pow 2).div_const 4).sub (L.hasDerivAt_weierstrassP hz1)).sub hPc
  refine hG.congr_deriv ?_
  simp only [Pi.div_apply]
  rw [hkey]
  field_simp
  linear_combination (4 * (℘'[L] z - ℘'[L] (s - z))) * mul_inv_cancel₀ hD0

/-- **The constant is `℘ s`**: as `z → 0` through the domain, `eulerG s z → ℘ s`. Substituting
the Laurent forms `℘ = z⁻² + g`, `℘' = -2z⁻³ + g'` with `g = ℘[L - 0]` and clearing the poles,
`eulerG s` agrees on the domain with an expression continuous at `0` whose value there is
`℘ s`, because `g 0 = 0`. -/
lemma tendsto_eulerG_zero {s : ℂ} (hs : s ∉ L.lattice) :
    Tendsto (L.eulerG s) (𝓝[L.eulerDomain s] 0) (𝓝 (℘[L] s)) := by
  have hg : AnalyticAt ℂ (L.weierstrassPExcept 0) 0 := L.analyticAt_weierstrassPExcept 0
  have hg0 : L.weierstrassPExcept 0 0 = 0 := L.weierstrassPExcept_zero_apply_zero
  have hP : ∀ z, ℘[L] z = (z ^ 2)⁻¹ + L.weierstrassPExcept 0 z := L.weierstrassP_eq_inv_sq_add
  have hP' : ∀ z, z ∉ L.lattice →
      ℘'[L] z = -2 * (z ^ 3)⁻¹ + deriv (L.weierstrassPExcept 0) z :=
    fun z hz ↦ L.derivWeierstrassP_eq_neg_two_inv_cube_add hz
  set E : ℂ → ℂ := fun z ↦
    (-4 * z * (deriv (L.weierstrassPExcept 0) z - ℘'[L] (s - z))
        + z ^ 4 * (deriv (L.weierstrassPExcept 0) z - ℘'[L] (s - z)) ^ 2
        - 8 * (L.weierstrassPExcept 0 z - ℘[L] (s - z))
        - 4 * z ^ 2 * (L.weierstrassPExcept 0 z - ℘[L] (s - z)) ^ 2)
      / (4 * (1 + z ^ 2 * (L.weierstrassPExcept 0 z - ℘[L] (s - z))) ^ 2)
      - L.weierstrassPExcept 0 z - ℘[L] (s - z) with hE
  have key : Tendsto E (𝓝 (0 : ℂ)) (𝓝 (℘[L] s)) := by
    have hgc : ContinuousAt (L.weierstrassPExcept 0) 0 := hg.continuousAt
    have hg' : ContinuousAt (deriv (L.weierstrassPExcept 0)) 0 := hg.deriv.continuousAt
    have hPs : ContinuousAt (fun z : ℂ ↦ ℘[L] (s - z)) 0 :=
      ContinuousAt.comp (f := fun z : ℂ ↦ s - z) (x := 0)
        (L.analyticOnNhd_weierstrassP (s - 0) (by simpa using hs)).continuousAt
        (continuousAt_const.sub continuousAt_id)
    have hPs' : ContinuousAt (fun z : ℂ ↦ ℘'[L] (s - z)) 0 :=
      ContinuousAt.comp (f := fun z : ℂ ↦ s - z) (x := 0)
        (L.analyticOnNhd_derivWeierstrassP (s - 0) (by simpa using hs)).continuousAt
        (continuousAt_const.sub continuousAt_id)
    have hA : ContinuousAt (fun z : ℂ ↦ deriv (L.weierstrassPExcept 0) z - ℘'[L] (s - z)) 0 :=
      hg'.sub hPs'
    have hB : ContinuousAt (fun z : ℂ ↦ L.weierstrassPExcept 0 z - ℘[L] (s - z)) 0 :=
      hgc.sub hPs
    have hnum : ContinuousAt (fun z : ℂ ↦
        -4 * z * (deriv (L.weierstrassPExcept 0) z - ℘'[L] (s - z))
          + z ^ 4 * (deriv (L.weierstrassPExcept 0) z - ℘'[L] (s - z)) ^ 2
          - 8 * (L.weierstrassPExcept 0 z - ℘[L] (s - z))
          - 4 * z ^ 2 * (L.weierstrassPExcept 0 z - ℘[L] (s - z)) ^ 2) 0 :=
      ((((continuousAt_const.mul continuousAt_id).mul hA).add
        ((continuousAt_id.pow 4).mul (hA.pow 2))).sub
        (continuousAt_const.mul hB)).sub
        ((continuousAt_const.mul (continuousAt_id.pow 2)).mul (hB.pow 2))
    have hden : ContinuousAt (fun z : ℂ ↦
        4 * (1 + z ^ 2 * (L.weierstrassPExcept 0 z - ℘[L] (s - z))) ^ 2) 0 :=
      continuousAt_const.mul ((continuousAt_const.add ((continuousAt_id.pow 2).mul hB)).pow 2)
    have hden0 :
        (4 : ℂ) * (1 + (0 : ℂ) ^ 2 * (L.weierstrassPExcept 0 0 - ℘[L] (s - 0))) ^ 2 ≠ 0 := by
      norm_num
    have hcont : ContinuousAt E 0 := ((hnum.div hden hden0).sub hgc).sub hPs
    have hval : E 0 = ℘[L] s := by
      simp only [hE, hg0, sub_zero]
      ring
    rw [← hval]
    exact hcont
  refine Tendsto.congr' ?_ (key.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with w hw
  obtain ⟨hw1, hws, hwne⟩ := hw
  have hw0 : w ≠ 0 := fun h ↦ hw1 (by rw [h]; exact zero_mem _)
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero _ hw0
  have hDl : (w ^ 2)⁻¹ + L.weierstrassPExcept 0 w - ℘[L] (s - w) ≠ 0 := by
    have hD : ℘[L] w - ℘[L] (s - w) ≠ 0 := sub_ne_zero.mpr hwne
    rwa [hP w] at hD
  have h1B : (1 : ℂ) + w ^ 2 * (L.weierstrassPExcept 0 w - ℘[L] (s - w)) ≠ 0 := by
    have heq : w ^ 2 * ((w ^ 2)⁻¹ + L.weierstrassPExcept 0 w - ℘[L] (s - w))
        = (1 : ℂ) + w ^ 2 * (L.weierstrassPExcept 0 w - ℘[L] (s - w)) := by
      rw [mul_sub, mul_add, mul_inv_cancel₀ hw2]
      ring
    rw [← heq]
    exact mul_ne_zero hw2 hDl
  simp only [hE, eulerG, eulerSlope]
  rw [hP w, hP' w hw1, sub_add_eq_sub_sub]
  congr 1
  congr 1
  have hwC : w * (1 + w ^ 2 * (L.weierstrassPExcept 0 w - ℘[L] (s - w))) ≠ 0 :=
    mul_ne_zero hw0 h1B
  have hslope : (-2 * (w ^ 3)⁻¹ + deriv (L.weierstrassPExcept 0) w - ℘'[L] (s - w))
      / ((w ^ 2)⁻¹ + L.weierstrassPExcept 0 w - ℘[L] (s - w))
      = (-2 + w ^ 3 * (deriv (L.weierstrassPExcept 0) w - ℘'[L] (s - w)))
        / (w * (1 + w ^ 2 * (L.weierstrassPExcept 0 w - ℘[L] (s - w)))) := by
    rw [div_eq_div_iff hDl hwC]
    field_simp
    ring
  have h4C : (4 : ℂ) * (1 + w ^ 2 * (L.weierstrassPExcept 0 w - ℘[L] (s - w))) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 h1B)
  have hbig : w ^ 2 * (1 + w ^ 2 * (L.weierstrassPExcept 0 w - ℘[L] (s - w))) ^ 2 * 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero hw2 (pow_ne_zero 2 h1B)) (by norm_num)
  rw [hslope, div_pow, mul_pow, div_div, inv_eq_one_div,
    div_sub_div _ _ hbig hw2, div_eq_div_iff h4C (mul_ne_zero hbig hw2)]
  ring

/-- **Euler's function is constant**, equal to `℘ s`, on `eulerDomain s`: it is differentiable
with zero derivative on that open connected set, and tends to `℘ s` at `0`, a point of its
closure. -/
lemma eulerG_eq_weierstrassP {s : ℂ} (hs : s ∉ L.lattice) {z : ℂ} (hz : z ∈ L.eulerDomain s) :
    L.eulerG s z = ℘[L] s := by
  have hconst : EqOn (L.eulerG s) (fun _ ↦ L.eulerG s z) (L.eulerDomain s) := by
    refine (L.isOpen_eulerDomain s).eqOn_of_deriv_eq (L.isPreconnected_eulerDomain hs)
      (fun x hx ↦ (L.hasDerivAt_eulerG hx).differentiableAt.differentiableWithinAt)
      (differentiableOn_const _) (fun x hx ↦ ?_) hz rfl
    rw [(L.hasDerivAt_eulerG hx).deriv, deriv_const]
  have : (𝓝[L.eulerDomain s] (0 : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (L.mem_closure_eulerDomain hs)
  have h1 : Tendsto (L.eulerG s) (𝓝[L.eulerDomain s] (0 : ℂ)) (𝓝 (L.eulerG s z)) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hconst hw).symm
  exact tendsto_nhds_unique h1 (L.tendsto_eulerG_zero hs)

/- ## The addition theorem -/

/-- **The addition theorem for `℘`**: for `z, w, z + w ∉ Λ` with `℘ z ≠ ℘ w`,
$\wp(z + w) = \big(\frac{\wp'(z) - \wp'(w)}{2(\wp(z) - \wp(w))}\big)^2 - \wp(z) - \wp(w)$. -/
theorem weierstrassP_add {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    ℘[L] (z + w)
      = ((℘'[L] z - ℘'[L] w) / (2 * (℘[L] z - ℘[L] w))) ^ 2 - ℘[L] z - ℘[L] w := by
  have hz' : z ∈ L.eulerDomain (z + w) :=
    ⟨hz, by rwa [add_sub_cancel_left], by rwa [add_sub_cancel_left]⟩
  have h := L.eulerG_eq_weierstrassP hzw hz'
  rw [eulerG, eulerSlope, add_sub_cancel_left] at h
  rw [← h]
  have hne : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring

/-- The chord slope between the points over `z` and `w`. -/
def chordSlope (z w : ℂ) : ℂ := (℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)

/-- The derivative of the chord slope in its first argument, by the quotient rule. -/
lemma hasDerivAt_chordSlope {z w : ℂ} (hz : z ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    HasDerivAt (fun u ↦ L.chordSlope u w)
      (((6 * ℘[L] z ^ 2 - L.g₂ / 2) * (℘[L] z - ℘[L] w) - (℘'[L] z - ℘'[L] w) * ℘'[L] z)
        / (℘[L] z - ℘[L] w) ^ 2) z := by
  simp only [chordSlope]
  exact ((L.hasDerivAt_derivWeierstrassP hz).sub_const _).div
    ((L.hasDerivAt_weierstrassP hz).sub_const _) (sub_ne_zero.mpr hx)

/-- **The addition theorem for `℘'`**: the derivative of the addition formula in `z`, simplified
with `euler_tangency_identity`. In the coordinates $(x, y) = (\wp, \tfrac12\wp')$ it says that
the third intersection of the chord with the curve is $-(P(z) + P(w))$. -/
theorem derivWeierstrassP_add {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hzw : z + w ∉ L.lattice) (hx : ℘[L] z ≠ ℘[L] w) :
    ℘'[L] (z + w)
      = -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z) := by
  have hD0 : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hx
  have hL : HasDerivAt (fun u : ℂ ↦ ℘[L] (u + w)) (℘'[L] (z + w)) z :=
    (L.hasDerivAt_weierstrassP hzw).comp_add_const z w
  have hR := ((((L.hasDerivAt_chordSlope hz hx).pow 2).div_const 4).sub
    (L.hasDerivAt_weierstrassP hz)).sub_const (℘[L] w)
  have hev : (fun u : ℂ ↦ ℘[L] (u + w)) =ᶠ[𝓝 z]
      fun u : ℂ ↦ L.chordSlope u w ^ 2 / 4 - ℘[L] u - ℘[L] w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz,
      (continuousAt_id.add continuousAt_const).eventually_mem
        (L.isClosed_lattice.isOpen_compl.mem_nhds hzw),
      (L.analyticOnNhd_weierstrassP z hz).continuousAt.eventually_ne hx] with u hu1 hu2 hu3
    rw [L.weierstrassP_add hu1 hw hu2 hu3, chordSlope]
    have : ℘[L] u - ℘[L] w ≠ 0 := sub_ne_zero.mpr hu3
    field_simp
    ring
  have huniq := (hL.congr_of_eventuallyEq hev.symm).unique hR
  rw [huniq, L.weierstrassP_add hz hw hzw hx]
  have hkey := euler_tangency_identity (L.derivWeierstrassP_sq z hz)
    (L.derivWeierstrassP_sq w hw)
  simp only [chordSlope, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  field_simp
  linear_combination 4 * (℘'[L] z - ℘'[L] w) * hkey

/- ## The duplication formulas, as limits of the addition formulas -/

/-- As `w → z`, the chord slope tends to the tangent slope `℘''(z) / ℘'(z)`. -/
lemma tendsto_chordSlope_self {z : ℂ} (hz : z ∉ L.lattice) (h0 : ℘'[L] z ≠ 0) :
    Tendsto (fun w ↦ L.chordSlope z w) (𝓝[≠] z)
      (𝓝 ((6 * ℘[L] z ^ 2 - L.g₂ / 2) / ℘'[L] z)) := by
  have hnum : Tendsto (slope ℘'[L] z) (𝓝[≠] z) (𝓝 (6 * ℘[L] z ^ 2 - L.g₂ / 2)) :=
    hasDerivAt_iff_tendsto_slope.mp (L.hasDerivAt_derivWeierstrassP hz)
  have hden : Tendsto (slope ℘[L] z) (𝓝[≠] z) (𝓝 (℘'[L] z)) :=
    hasDerivAt_iff_tendsto_slope.mp (L.hasDerivAt_weierstrassP hz)
  refine Tendsto.congr' ?_ (hnum.div hden h0)
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hwz : w - z ≠ 0 := sub_ne_zero.mpr hw
  simp only [Pi.div_apply]
  rw [slope_def_field, slope_def_field, chordSlope]
  by_cases hPw : ℘[L] w = ℘[L] z
  · rw [hPw]
    simp
  · have hB : ℘[L] w - ℘[L] z ≠ 0 := sub_ne_zero.mpr hPw
    have hB' : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr (Ne.symm hPw)
    field_simp
    ring

/-- On a punctured neighbourhood of a non-critical, non-2-torsion `z`, the hypotheses of the
addition formulas hold for the pair `(z, w)`. The clause `℘ z ≠ ℘ w` uses that `℘ - ℘ z` cannot
vanish on a neighbourhood of `z`, its derivative there being `℘' z ≠ 0`. -/
private lemma eventually_chord_conditions {z : ℂ} (hz : z ∉ L.lattice) (h0 : ℘'[L] z ≠ 0)
    (hzz : z + z ∉ L.lattice) :
    ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice ∧ z + w ∉ L.lattice ∧ ℘[L] z ≠ ℘[L] w := by
  have hne : ∀ᶠ w in 𝓝[≠] z, ℘[L] z ≠ ℘[L] w := by
    rcases ((L.analyticOnNhd_weierstrassP z hz).sub
      analyticAt_const).eventually_eq_zero_or_eventually_ne_zero with hcase | hcase
    · exfalso
      apply h0
      have hev : (fun w ↦ ℘[L] w - ℘[L] z) =ᶠ[𝓝 z] fun _ ↦ (0 : ℂ) := by
        filter_upwards [hcase] with u hu
        simpa using hu
      have hd := hev.deriv_eq
      rwa [((L.hasDerivAt_weierstrassP hz).sub_const (℘[L] z)).deriv, deriv_const] at hd
    · filter_upwards [hcase] with w hw
      exact fun heq ↦ hw (sub_eq_zero.mpr heq.symm)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (L.isClosed_lattice.isOpen_compl.mem_nhds hz),
    mem_nhdsWithin_of_mem_nhds ((continuousAt_const.add continuousAt_id).eventually_mem
      (L.isClosed_lattice.isOpen_compl.mem_nhds hzz)), hne] with w h1 h2 h3
  exact ⟨h1, h2, h3⟩

/-- **The duplication formula for `℘`**: for `z, 2z ∉ Λ`,
$\wp(2z) = \big(\frac{6\wp(z)^2 - g_2/2}{2\wp'(z)}\big)^2 - 2\wp(z)$, the limit `w → z` of the
addition formula. -/
theorem weierstrassP_two_mul {z : ℂ} (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    ℘[L] (2 * z) = ((6 * ℘[L] z ^ 2 - L.g₂ / 2) / (2 * ℘'[L] z)) ^ 2 - 2 * ℘[L] z := by
  have h0 : ℘'[L] z ≠ 0 :=
    fun h ↦ h2z (L.two_mul_mem_lattice_of_derivWeierstrassP_eq_zero hz h)
  have hzz : z + z ∉ L.lattice := fun h ↦ h2z (by rwa [two_mul])
  have hLHS : Tendsto (fun w : ℂ ↦ ℘[L] (z + w)) (𝓝[≠] z) (𝓝 (℘[L] (z + z))) :=
    (ContinuousAt.comp (f := fun w : ℂ ↦ z + w) (x := z)
      (L.analyticOnNhd_weierstrassP (z + z) hzz).continuousAt
      (continuousAt_const.add continuousAt_id)).tendsto.mono_left nhdsWithin_le_nhds
  have hRHS : Tendsto (fun w : ℂ ↦ L.chordSlope z w ^ 2 / 4 - ℘[L] z - ℘[L] w) (𝓝[≠] z)
      (𝓝 (((6 * ℘[L] z ^ 2 - L.g₂ / 2) / ℘'[L] z) ^ 2 / 4 - ℘[L] z - ℘[L] z)) :=
    ((((L.tendsto_chordSlope_self hz h0).pow 2).div_const 4).sub tendsto_const_nhds).sub
      ((L.analyticOnNhd_weierstrassP z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hev : (fun w : ℂ ↦ ℘[L] (z + w)) =ᶠ[𝓝[≠] z]
      fun w : ℂ ↦ L.chordSlope z w ^ 2 / 4 - ℘[L] z - ℘[L] w := by
    filter_upwards [L.eventually_chord_conditions hz h0 hzz] with w ⟨h1, h2, h3⟩
    rw [L.weierstrassP_add hz h1 h2 h3, chordSlope]
    have hD : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr h3
    field_simp
    ring
  rw [two_mul, tendsto_nhds_unique (hLHS.congr' hev) hRHS]
  field_simp
  ring

/-- **The duplication formula for `℘'`**: the limit `w → z` of `derivWeierstrassP_add`. -/
theorem derivWeierstrassP_two_mul {z : ℂ} (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    ℘'[L] (2 * z)
      = -((6 * ℘[L] z ^ 2 - L.g₂ / 2) / ℘'[L] z * (℘[L] (2 * z) - ℘[L] z) + ℘'[L] z) := by
  have h0 : ℘'[L] z ≠ 0 :=
    fun h ↦ h2z (L.two_mul_mem_lattice_of_derivWeierstrassP_eq_zero hz h)
  have hzz : z + z ∉ L.lattice := fun h ↦ h2z (by rwa [two_mul])
  have hLHS : Tendsto (fun w : ℂ ↦ ℘'[L] (z + w)) (𝓝[≠] z) (𝓝 (℘'[L] (z + z))) :=
    (ContinuousAt.comp (f := fun w : ℂ ↦ z + w) (x := z)
      (L.analyticOnNhd_derivWeierstrassP (z + z) hzz).continuousAt
      (continuousAt_const.add continuousAt_id)).tendsto.mono_left nhdsWithin_le_nhds
  have h℘c : Tendsto (fun w : ℂ ↦ ℘[L] (z + w)) (𝓝[≠] z) (𝓝 (℘[L] (z + z))) :=
    (ContinuousAt.comp (f := fun w : ℂ ↦ z + w) (x := z)
      (L.analyticOnNhd_weierstrassP (z + z) hzz).continuousAt
      (continuousAt_const.add continuousAt_id)).tendsto.mono_left nhdsWithin_le_nhds
  have hRHS : Tendsto
      (fun w : ℂ ↦ -(L.chordSlope z w * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z)) (𝓝[≠] z)
      (𝓝 (-((6 * ℘[L] z ^ 2 - L.g₂ / 2) / ℘'[L] z * (℘[L] (z + z) - ℘[L] z) + ℘'[L] z))) :=
    (((L.tendsto_chordSlope_self hz h0).mul (h℘c.sub tendsto_const_nhds)).add
      tendsto_const_nhds).neg
  have hev : (fun w : ℂ ↦ ℘'[L] (z + w)) =ᶠ[𝓝[≠] z]
      fun w : ℂ ↦ -(L.chordSlope z w * (℘[L] (z + w) - ℘[L] z) + ℘'[L] z) := by
    filter_upwards [L.eventually_chord_conditions hz h0 hzz] with w ⟨h1, h2, h3⟩
    rw [L.derivWeierstrassP_add hz h1 h2 h3, chordSlope]
  rw [two_mul]
  exact tendsto_nhds_unique (hLHS.congr' hev) hRHS

end PeriodPair

end
