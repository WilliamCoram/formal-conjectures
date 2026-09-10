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

public import FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.PeriodLattice
public import FormalConjecturesForMathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.Periods

@[expose] public noncomputable section

/-!
# The period lattice of an elliptic curve over ℂ: integrals and uniformisation agree

There are two descriptions of the period lattice of an elliptic curve $E$ over $\mathbb{C}$.

* *From the invariant differential.* `WeierstrassCurve.integralPeriodLattice` is the set of
  integrals of $\omega = dx / (2y + a_1 x + a_3)$ along the $C^1$ loops on $E(\mathbb{C})$
  avoiding the point at infinity and the points of order two.
* *From the uniformisation.* `WeierstrassCurve.periodPair` is a period pair whose lattice has
  invariants $g_2 = c_4 / 12$ and $g_3 = c_6 / 216$; its lattice is well defined, since the
  invariants determine the lattice.

This file proves that they agree (`WeierstrassCurve.integralPeriodLattice_eq`): the change of
variables to the short model preserves $\omega$
(`WeierstrassCurve.integralPeriodLattice_shortModel`), the short model is the curve of the period
lattice (`WeierstrassCurve.periodPair_weierstrassCurve`), and for the curve of a lattice the periods
are the lattice (`PeriodPair.integralPeriodLattice_weierstrassCurve`).

The equality is one of sets. The *pair* `WeierstrassCurve.periodPair` is a choice of
$\mathbb{Z}$-basis of the lattice, well defined only up to $\mathrm{GL}_2(\mathbb{Z})$, and
nothing beyond its lattice
can be said about it; in particular every element of the lattice is the integral of $\omega$ along
some loop (`WeierstrassCurve.exists_curveIntegral_eq_of_mem_lattice`), and a $\mathbb{Z}$-basis of
the lattice is the pair of integrals along two loops. What enters the Birch and Swinnerton-Dyer
conjecture at a complex place is the covolume $2 \operatorname{Im}(\overline{\omega_1} \omega_2)$
of the lattice, which does not depend on the basis.

*References:*
- [LMFDB](https://www.lmfdb.org/knowledge/show/ec.q.period_lattice), knowls `ec.q.period_lattice`
  and `ec.period`
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, Chapter VI
    Proposition 3.6 and Theorem 5.1, https://link.springer.com/book/10.1007/978-0-387-09494-6
- [Mil2006] J. S. Milne. Elliptic Curves, Chapter III, Proposition 3.7 and Theorem 3.10,
    https://www.jmilne.org/math/Books/ectext6.pdf
-/

open MeasureTheory Set
open scoped unitInterval

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℂ) [W.IsElliptic]

/-- The curve of the period lattice of `W` is the short model of `W`. -/
lemma periodPair_weierstrassCurve : W.periodPair.weierstrassCurve = W.shortModel := by
  have h2 : W.periodPair.g₂ = W.c₄ / 12 := periodPair_g₂ W
  have h3 : W.periodPair.g₃ = W.c₆ / 216 := periodPair_g₃ W
  ext <;> simp only [PeriodPair.weierstrassCurve, WeierstrassCurve.shortModel, h2, h3] <;> ring

/-- **The period lattice as integrals is the period lattice**: the integrals of the invariant
differential along loops on $E(\mathbb{C})$ are exactly the elements of the lattice with
invariants $g_2 = c_4 / 12$ and $g_3 = c_6 / 216$. -/
theorem integralPeriodLattice_eq : W.integralPeriodLattice = (W.periodPair.lattice : Set ℂ) := by
  rw [← W.integralPeriodLattice_shortModel, ← W.periodPair_weierstrassCurve,
    W.periodPair.integralPeriodLattice_weierstrassCurve]

/-- Every element of the period lattice is the integral of the invariant differential along a
loop on the curve. -/
theorem exists_curveIntegral_eq_of_mem_lattice {l : ℂ} (hl : l ∈ W.periodPair.lattice) :
    ∃ (p : ℂ × ℂ) (γ : Path p p), ContDiffOn ℝ 1 γ.extend I ∧
      range γ ⊆ W.affineNonTwoTorsion ∧ ∫ᶜ x in γ, W.invariantDifferential x = l := by
  refine W.mem_integralPeriodLattice_iff.mp ?_
  rw [W.integralPeriodLattice_eq]
  exact hl

end WeierstrassCurve

end
