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

public import FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.Affine.VariableChange
public import FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.ComplexPeriod
public import FormalConjecturesForMathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.Uniformization

@[expose] public noncomputable section

/-!
# Uniformisation of an elliptic curve over `ℂ`

Every elliptic curve $E$ over $\mathbb{C}$ is a complex torus: for the period lattice
$\Lambda$ of $E$ (`WeierstrassCurve.periodPair`), the map
$$\mathbb{C}/\Lambda \longrightarrow E(\mathbb{C}), \qquad
  z \longmapsto \Big(\wp(z) - \tfrac{b_2}{12},\ \tfrac12 \wp'(z) - \tfrac{a_1}{2}\wp(z)
    + \tfrac{a_1 b_2}{24} - \tfrac{a_3}{2}\Big)$$
is an isomorphism of groups (`WeierstrassCurve.uniformizationAddEquiv`). It is the composite of
the uniformisation of the short model $y^2 = x^3 - \tfrac{g_2}{4}x - \tfrac{g_3}{4}$ by
$z \mapsto (\wp(z), \tfrac12\wp'(z))$ (`PeriodPair.uniformizationAddEquiv`, for the period pair of
$E$, whose curve is the short model by `WeierstrassCurve.periodPair_weierstrassCurve`) with the
change of variables back to the given Weierstrass equation
(`WeierstrassCurve.Affine.Point.variableChangeAddEquiv`).

## Source correspondence

This is the uniformisation theorem [Sil2009, VI.5.1(a)]: for every elliptic curve $E/\mathbb{C}$
there is a lattice $\Lambda$, unique up to homothety, and a complex analytic isomorphism
$\mathbb{C}/\Lambda \to E(\mathbb{C})$ of groups. The lattice is `W.periodPair.lattice`
(`ComplexPeriod.lean` identifies it with the periods of the invariant differential), and the
isomorphism of groups is `WeierstrassCurve.uniformizationAddEquiv`. Analyticity is not part of
the statement here.

*References:*
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, VI.5.1,
    https://link.springer.com/book/10.1007/978-0-387-09494-6
- [LMFDB](https://www.lmfdb.org/knowledge/show/ec.q.period_lattice), knowl `ec.q.period_lattice`
-/

open WeierstrassCurve.Affine
open scoped PeriodPair

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℂ)

/-- The change of variables from `W` to its short model, in Mathlib's convention that `C • W` is
the curve in the new coordinates: `shortModelChange • W = W.shortModel`, and the substitution
`(X, Y) ↦ (X - b₂/12, Y - (a₁/2) X + a₁ b₂/24 - a₃/2)` carries points of the short model to
points of `W`. It is the inverse of `WeierstrassCurve.toShortModel`. -/
def shortModelChange : VariableChange ℂ :=
  ⟨1, -W.b₂ / 12, -W.a₁ / 2, W.a₁ * W.b₂ / 24 - W.a₃ / 2⟩

/-- The short model is the image of `W` under `shortModelChange`. -/
lemma shortModel_eq_smul : W.shortModel = W.shortModelChange • W := by
  ext <;> simp only [variableChange_def, shortModel, shortModelChange, c₄, c₆, b₂, b₄, b₆,
    inv_one, Units.val_one, one_pow, one_mul] <;> ring

variable [W.IsElliptic]

/-- **Uniformisation of an elliptic curve over `ℂ`**: $\mathbb{C}/\Lambda \simeq E(\mathbb{C})$
as groups, for the period lattice $\Lambda$ of $E$. -/
def uniformizationAddEquiv : ℂ ⧸ W.periodPair.lattice.toAddSubgroup ≃+ W.toAffine.Point :=
  (W.periodPair.uniformizationAddEquiv.trans
    (Point.addEquivOfEq (W.periodPair_weierstrassCurve.trans W.shortModel_eq_smul))).trans
    (Point.variableChangeAddEquiv W.shortModelChange)

/-- Lattice points go to the point at infinity. -/
lemma uniformizationAddEquiv_mk_of_mem {z : ℂ} (hz : z ∈ W.periodPair.lattice) :
    W.uniformizationAddEquiv z = 0 := by
  simp only [uniformizationAddEquiv, AddEquiv.trans_apply, PeriodPair.uniformizationAddEquiv_apply,
    PeriodPair.uniformization_mk, W.periodPair.toPoint_of_mem hz, Point.addEquivOfEq_zero,
    Point.variableChangeAddEquiv_apply, Point.variableChange_zero]

/-- Off the lattice, `z` goes to the affine point with coordinates
$\big(\wp(z) - \tfrac{b_2}{12},\ \tfrac12 \wp'(z) - \tfrac{a_1}{2}\wp(z) + \tfrac{a_1 b_2}{24}
- \tfrac{a_3}{2}\big)$. -/
lemma uniformizationAddEquiv_mk_of_notMem {z : ℂ} (hz : z ∉ W.periodPair.lattice) :
    ∃ h, W.uniformizationAddEquiv z = .some (℘[W.periodPair] z - W.b₂ / 12)
      (℘'[W.periodPair] z / 2 - W.a₁ / 2 * ℘[W.periodPair] z
        + (W.a₁ * W.b₂ / 24 - W.a₃ / 2)) h := by
  simp only [uniformizationAddEquiv, AddEquiv.trans_apply, PeriodPair.uniformizationAddEquiv_apply,
    PeriodPair.uniformization_mk, W.periodPair.toPoint_of_notMem hz, Point.addEquivOfEq_some,
    Point.variableChangeAddEquiv_apply, Point.variableChange_some]
  have hx : ((W.shortModelChange.u : ℂ) ^ 2 * ℘[W.periodPair] z + W.shortModelChange.r)
      = ℘[W.periodPair] z - W.b₂ / 12 := by
    simp only [shortModelChange, Units.val_one, one_pow, one_mul]
    ring
  have hy : ((W.shortModelChange.u : ℂ) ^ 3 * (℘'[W.periodPair] z / 2)
        + (W.shortModelChange.u : ℂ) ^ 2 * W.shortModelChange.s * ℘[W.periodPair] z
        + W.shortModelChange.t)
      = ℘'[W.periodPair] z / 2 - W.a₁ / 2 * ℘[W.periodPair] z
        + (W.a₁ * W.b₂ / 24 - W.a₃ / 2) := by
    simp only [shortModelChange, Units.val_one, one_pow, one_mul]
    ring
  refine ⟨hx ▸ hy ▸ (nonsingular_variableChange_iff W.shortModelChange _ _).mp
    ((W.periodPair_weierstrassCurve.trans W.shortModel_eq_smul) ▸
      W.periodPair.weierstrassCurve_nonsingular hz), ?_⟩
  congr 1

end WeierstrassCurve

end
