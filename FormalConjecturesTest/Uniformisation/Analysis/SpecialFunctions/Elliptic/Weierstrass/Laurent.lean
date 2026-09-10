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

public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass

@[expose] public noncomputable section

/-!
# The Laurent expansion of `℘` at the origin

Mathlib's `weierstrassPExcept L 0`, written $\wp[L - 0]$ below, is the Weierstrass function
with its $l = 0$ term removed,
$$\wp(z) = \frac{1}{z^2} + \wp[L - 0](z), \qquad
  \wp[L - 0](z) = \sum_{l \in \Lambda \setminus 0} \Big(\frac{1}{(z - l)^2} - \frac{1}{l^2}\Big),$$
and it is analytic at $0$ (`PeriodPair.analyticAt_weierstrassPExcept`). This file records the two
facts about it that the addition theorem needs: it vanishes at $0$, and so does its derivative,
because it is even. In Laurent-series language, $\wp(z) = z^{-2} + 0 + 0 \cdot z + O(z^2)$ and
$\wp'(z) = -2 z^{-3} + 0 + O(z)$.

## Source correspondence

[Sil2009, VI.3.5] and [WW1927, §20.22] write
$\wp(z) = z^{-2} + \sum_{k \ge 1} (2k+1) G_{2k+2} z^{2k}$. We do not need the coefficients, only
the vanishing of the constant and linear terms: `PeriodPair.weierstrassPExcept_zero_apply_zero`
and `PeriodPair.deriv_weierstrassPExcept_zero_apply_zero`. The splittings
`PeriodPair.weierstrassP_eq_inv_sq_add` and
`PeriodPair.derivWeierstrassP_eq_neg_two_inv_cube_add` are Mathlib's
`weierstrassPExcept_add` and `derivWeierstrassPExcept_sub` at $l_0 = 0$.

*References:*
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, VI.3.5
- [WW1927] E. T. Whittaker, G. N. Watson. A Course of Modern Analysis, 4th edition, §20.22
-/

namespace PeriodPair

variable (L : PeriodPair)

/-- $\wp[L - 0]$ vanishes at $0$: every term $1/(0 - l)^2 - 1/l^2$ does. -/
lemma weierstrassPExcept_zero_apply_zero : L.weierstrassPExcept 0 0 = 0 := by
  simp [weierstrassPExcept]

/-- $\wp'[L - 0]$ vanishes at $0$: it is odd, by the symmetry $l \mapsto -l$ of the lattice. -/
lemma derivWeierstrassPExcept_zero_apply_zero : L.derivWeierstrassPExcept 0 0 = 0 := by
  have h := L.derivWeierstrassPExcept_neg 0 0
  rw [neg_zero] at h
  linear_combination h / 2

/-- The derivative of $\wp[L - 0]$ vanishes at $0$. -/
lemma deriv_weierstrassPExcept_zero_apply_zero : deriv (L.weierstrassPExcept 0) 0 = 0 := by
  rw [L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 (by simp)]
  exact L.derivWeierstrassPExcept_zero_apply_zero

/-- **Laurent expansion of $\wp$ at $0$**: $\wp(z) = z^{-2} + \wp[L - 0](z)$, with $\wp[L - 0]$
analytic at $0$ and vanishing there to second order. This holds for every $z$, the values at
lattice points being consistent. -/
lemma weierstrassP_eq_inv_sq_add (z : ℂ) : ℘[L] z = (z ^ 2)⁻¹ + L.weierstrassPExcept 0 z := by
  have h := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero, one_div] at h
  rw [← h]
  ring

/-- **Laurent expansion of $\wp'$ at $0$**: off the lattice,
$\wp'(z) = -2 z^{-3} + \wp[L - 0]'(z)$. -/
lemma derivWeierstrassP_eq_neg_two_inv_cube_add {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z = -2 * (z ^ 3)⁻¹ + deriv (L.weierstrassPExcept 0) z := by
  rw [L.eqOn_deriv_weierstrassPExcept_derivWeierstrassPExcept 0 (by simp [hz])]
  have h := L.derivWeierstrassPExcept_sub 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero] at h
  rw [← h]
  ring

end PeriodPair

end
