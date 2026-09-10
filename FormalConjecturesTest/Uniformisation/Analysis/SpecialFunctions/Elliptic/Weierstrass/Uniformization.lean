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

public import FormalConjecturesTest.Uniformisation.Analysis.SpecialFunctions.Elliptic.Weierstrass.Addition
public import FormalConjecturesTest.Period.Analysis.SpecialFunctions.Elliptic.Weierstrass.Existence
public import FormalConjecturesTest.Period.Analysis.SpecialFunctions.Elliptic.Weierstrass.Surjective

@[expose] public noncomputable section

/-!
# Uniformisation of the curve of a lattice: `ℂ/Λ ≃+ E_Λ(ℂ)`

For a period lattice $\Lambda$ with invariants $g_2, g_3$, the map
$$z \longmapsto (\wp(z), \tfrac12 \wp'(z)), \qquad \Lambda \longmapsto O$$
is a group isomorphism from $\mathbb{C}/\Lambda$ onto the points of the elliptic curve
$E_\Lambda : y^2 = x^3 - \tfrac{g_2}{4} x - \tfrac{g_3}{4}$ (`PeriodPair.weierstrassCurve`). This
file constructs the lift `PeriodPair.toPoint`, descends it to `PeriodPair.uniformization` on
$\mathbb{C}/\Lambda$, and proves

* injectivity (`PeriodPair.uniformization_injective`), from
  `PeriodPair.sub_mem_lattice_of_weierstrassP_eq_of_derivWeierstrassP_eq` — $(\wp, \wp')$ is
  injective modulo $\Lambda$ — and the fact that only lattice points are sent to $O$;
* surjectivity (`PeriodPair.uniformization_surjective`), from
  `PeriodPair.exists_weierstrassP_eq_and_derivWeierstrassP_eq` — every affine point of $E_\Lambda$
  is $(\wp(z), \tfrac12 \wp'(z))$ for some $z \notin \Lambda$;
* additivity (`PeriodPair.toPoint_add`), from the addition and duplication theorems for $\wp$
  (`PeriodPair.weierstrassP_add`, `PeriodPair.weierstrassP_two_mul` and their companions for
  $\wp'$): in the coordinates $(\wp, \tfrac12\wp')$ these are exactly Mathlib's chord-and-tangent
  law `WeierstrassCurve.Affine.Point.add`.

The result is `PeriodPair.uniformizationAddEquiv : ℂ ⧸ Λ ≃+ E_Λ(ℂ)`.

## Source correspondence

[Sil2009, VI.3.6(b)] states that $\phi : \mathbb{C}/\Lambda \to E(\mathbb{C})$,
$z \mapsto [\wp(z), \wp'(z), 1]$, is an isomorphism of groups onto the curve
$y^2 = 4x^3 - g_2 x - g_3$. Mathlib's `WeierstrassCurve` is monic in $x^3$, so we use the
isomorphic model $y^2 = x^3 - \tfrac{g_2}{4}x - \tfrac{g_3}{4}$ and the point
$(\wp(z), \tfrac12 \wp'(z))$ (`PeriodPair.toPoint`); Silverman's $\phi$ is
`PeriodPair.uniformization`, and the point at infinity is `WeierstrassCurve.Affine.Point.zero`.
Silverman proves additivity through the residue theorem; the addition theorem is proved here by
Euler's method instead, see `Weierstrass/Addition.lean`.

*References:*
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, VI.3.6,
    https://link.springer.com/book/10.1007/978-0-387-09494-6
- [LMFDB](https://www.lmfdb.org/knowledge/show/ec.q.period_lattice), knowl `ec.q.period_lattice`
-/

open WeierstrassCurve.Affine

namespace PeriodPair

variable (L : PeriodPair)

/- ## The lift `ℂ → E_Λ(ℂ)` -/

/-- Off the lattice, $(\wp(z), \tfrac12 \wp'(z))$ lies on `L.weierstrassCurve`: this is
$\wp'^2 = 4\wp^3 - g_2\wp - g_3$ divided by $4$. -/
lemma weierstrassCurve_equation {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassCurve.toAffine.Equation (℘[L] z) (℘'[L] z / 2) := by
  simp only [equation_iff, weierstrassCurve, WeierstrassCurve.toAffine]
  linear_combination (L.derivWeierstrassP_sq z hz) / 4

/-- The point $(\wp(z), \tfrac12 \wp'(z))$ is nonsingular, as every affine point of an elliptic
curve is. -/
lemma weierstrassCurve_nonsingular {z : ℂ} (hz : z ∉ L.lattice) :
    L.weierstrassCurve.toAffine.Nonsingular (℘[L] z) (℘'[L] z / 2) :=
  equation_iff_nonsingular.mp (L.weierstrassCurve_equation hz)

open Classical in
/-- The uniformisation lift $\mathbb{C} \to E_\Lambda(\mathbb{C})$: $z \mapsto (\wp(z), \tfrac12
\wp'(z))$ off the lattice, and the point at infinity on it. -/
def toPoint (z : ℂ) : L.weierstrassCurve.toAffine.Point :=
  if hz : z ∈ L.lattice then 0 else .some _ _ (L.weierstrassCurve_nonsingular hz)

/-- On the lattice, `toPoint` is the point at infinity. -/
lemma toPoint_of_mem {z : ℂ} (hz : z ∈ L.lattice) : L.toPoint z = 0 := by
  rw [toPoint, dif_pos hz]

/-- Off the lattice, `toPoint z` is the affine point $(\wp(z), \tfrac12 \wp'(z))$. -/
lemma toPoint_of_notMem {z : ℂ} (hz : z ∉ L.lattice) :
    L.toPoint z = .some _ _ (L.weierstrassCurve_nonsingular hz) := by
  rw [toPoint, dif_neg hz]

/-- Translating by a lattice element does not move the point: $\wp$ and $\wp'$ are periodic. -/
lemma toPoint_add_coe (z : ℂ) (l : L.lattice) : L.toPoint (z + l) = L.toPoint z := by
  by_cases hz : z ∈ L.lattice
  · rw [L.toPoint_of_mem (add_mem hz l.2), L.toPoint_of_mem hz]
  · have hzl : z + l ∉ L.lattice := fun h ↦ hz (by simpa using sub_mem h l.2)
    rw [L.toPoint_of_notMem hzl, L.toPoint_of_notMem hz]
    congr 1
    · exact L.weierstrassP_add_coe z l
    · rw [L.derivWeierstrassP_add_coe z l]

/-- Negation on $\mathbb{C}$ is negation on the curve: $\wp$ is even and $\wp'$ is odd. -/
lemma toPoint_neg (z : ℂ) : L.toPoint (-z) = -L.toPoint z := by
  by_cases hz : z ∈ L.lattice
  · rw [L.toPoint_of_mem (neg_mem hz), L.toPoint_of_mem hz, Point.neg_zero]
  · have hnz : -z ∉ L.lattice := fun h ↦ hz (neg_mem_iff.mp h)
    rw [L.toPoint_of_notMem hnz, L.toPoint_of_notMem hz, Point.neg_some]
    congr 1
    · exact L.weierstrassP_neg z
    · simp only [negY, weierstrassCurve, WeierstrassCurve.toAffine, L.derivWeierstrassP_neg]
      ring

/-- Two complex numbers give the same point of the curve exactly when they differ by a lattice
element: on the lattice both give $O$; off it, $(\wp, \wp')$ is injective modulo $\Lambda$. -/
theorem toPoint_eq_iff {z w : ℂ} : L.toPoint z = L.toPoint w ↔ z - w ∈ L.lattice := by
  constructor
  · intro h
    by_cases hz : z ∈ L.lattice <;> by_cases hw : w ∈ L.lattice
    · exact sub_mem hz hw
    · rw [L.toPoint_of_mem hz, L.toPoint_of_notMem hw] at h
      exact absurd h.symm (Point.some_ne_zero _)
    · rw [L.toPoint_of_notMem hz, L.toPoint_of_mem hw] at h
      exact absurd h (Point.some_ne_zero _)
    · rw [L.toPoint_of_notMem hz, L.toPoint_of_notMem hw] at h
      obtain ⟨h₁, h₂⟩ := Point.some.inj h
      exact L.sub_mem_lattice_of_weierstrassP_eq_of_derivWeierstrassP_eq hz hw h₁
        (by linear_combination 2 * h₂)
  · intro h
    have key := L.toPoint_add_coe w ⟨z - w, h⟩
    rwa [show ((⟨z - w, h⟩ : L.lattice) : ℂ) = z - w from rfl, show w + (z - w) = z by ring]
      at key

/-- Every point of the curve is `toPoint z` for some `z`: the point at infinity comes from `0`, and
an affine point $(x, y)$ from a $z$ with $(\wp(z), \tfrac12 \wp'(z)) = (x, y)$. -/
theorem toPoint_surjective : Function.Surjective L.toPoint := by
  intro P
  cases P with
  | zero => exact ⟨0, L.toPoint_of_mem (zero_mem _)⟩
  | some x y h =>
    have hcurve : (2 * y) ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ := by
      have := (equation_iff ..).mp h.1
      simp only [weierstrassCurve, WeierstrassCurve.toAffine] at this
      linear_combination 4 * this
    obtain ⟨z, hz, hx, hy⟩ := L.exists_weierstrassP_eq_and_derivWeierstrassP_eq hcurve
    refine ⟨z, ?_⟩
    rw [L.toPoint_of_notMem hz]
    congr 1
    rw [hy]
    ring

/-- **Additivity of the lift**: `toPoint (z + w) = toPoint z + toPoint w`. When `z`, `w` or
`z + w` lies in `Λ` this is periodicity and `toPoint_neg`. In generic position, if `℘ z ≠ ℘ w` the
sum is the chord case `add_of_X_ne` and the coordinates are given by `weierstrassP_add` and
`derivWeierstrassP_add`; otherwise `w ≡ z` modulo `Λ` (`w ≡ -z` would put `z + w` in `Λ`), the sum
is the tangent case `add_of_Y_ne`, and the coordinates are given by the duplication formulas. -/
theorem toPoint_add (z w : ℂ) : L.toPoint (z + w) = L.toPoint z + L.toPoint w := by
  by_cases hz : z ∈ L.lattice
  · rw [L.toPoint_of_mem hz, zero_add, add_comm]
    exact L.toPoint_add_coe w ⟨z, hz⟩
  by_cases hw : w ∈ L.lattice
  · rw [L.toPoint_of_mem hw, add_zero]
    exact L.toPoint_add_coe z ⟨w, hw⟩
  by_cases hzw : z + w ∈ L.lattice
  · have hwz : L.toPoint w = -L.toPoint z := by
      rw [← L.toPoint_neg, L.toPoint_eq_iff, sub_neg_eq_add, add_comm]
      exact hzw
    rw [L.toPoint_of_mem hzw, hwz, add_neg_cancel]
  rw [L.toPoint_of_notMem hz, L.toPoint_of_notMem hw, L.toPoint_of_notMem hzw]
  by_cases hxx : ℘[L] z = ℘[L] w
  · -- the tangent case: `w ≡ z`, and the sum is the point over `2 * z`
    have hsub : z - w ∈ L.lattice := ((L.weierstrassP_eq_iff hz hw).mp hxx).resolve_right hzw
    have hwz : w - z ∈ L.lattice := by simpa using neg_mem hsub
    have h2z : 2 * z ∉ L.lattice := fun h2z ↦ hzw (by
      rw [show z + w = 2 * z + (w - z) by ring]
      exact add_mem h2z hwz)
    have hy0 : ℘'[L] z ≠ 0 :=
      fun h ↦ h2z (L.two_mul_mem_lattice_of_derivWeierstrassP_eq_zero hz h)
    have hy : ℘'[L] w = ℘'[L] z := by
      have h := L.derivWeierstrassP_add_coe z ⟨w - z, hwz⟩
      rwa [show z + ((⟨w - z, hwz⟩ : L.lattice) : ℂ) = w from by
        show z + (w - z) = w; ring] at h
    have hPzw : ℘[L] (z + w) = ℘[L] (2 * z) := by
      have h := L.weierstrassP_add_coe (2 * z) ⟨w - z, hwz⟩
      rwa [show 2 * z + ((⟨w - z, hwz⟩ : L.lattice) : ℂ) = z + w from by
        show 2 * z + (w - z) = z + w; ring] at h
    have hP'zw : ℘'[L] (z + w) = ℘'[L] (2 * z) := by
      have h := L.derivWeierstrassP_add_coe (2 * z) ⟨w - z, hwz⟩
      rwa [show 2 * z + ((⟨w - z, hwz⟩ : L.lattice) : ℂ) = z + w from by
        show 2 * z + (w - z) = z + w; ring] at h
    have hyne : ℘'[L] z / 2 ≠ L.weierstrassCurve.toAffine.negY (℘[L] w) (℘'[L] w / 2) := by
      simp only [negY, weierstrassCurve, WeierstrassCurve.toAffine]
      rw [hy]
      intro heq
      apply hy0
      linear_combination heq
    rw [Point.add_of_Y_ne hyne]
    congr 1
    · rw [slope_of_Y_ne hxx hyne]
      simp only [addX, negY, weierstrassCurve, WeierstrassCurve.toAffine]
      rw [hPzw, L.weierstrassP_two_mul hz h2z, ← hxx]
      ring
    · rw [addY, negY, negAddY, addX, slope_of_Y_ne hxx hyne]
      simp only [negY, weierstrassCurve, WeierstrassCurve.toAffine]
      rw [hP'zw, L.derivWeierstrassP_two_mul hz h2z, L.weierstrassP_two_mul hz h2z, ← hxx]
      ring
  · -- the chord case
    rw [Point.add_of_X_ne hxx]
    have hne : ℘[L] z - ℘[L] w ≠ 0 := sub_ne_zero.mpr hxx
    congr 1
    · rw [slope_of_X_ne hxx]
      simp only [addX, weierstrassCurve, WeierstrassCurve.toAffine]
      rw [L.weierstrassP_add hz hw hzw hxx]
      field_simp
      ring
    · rw [addY, negY, negAddY, addX, slope_of_X_ne hxx]
      simp only [weierstrassCurve, WeierstrassCurve.toAffine]
      rw [L.derivWeierstrassP_add hz hw hzw hxx, L.weierstrassP_add hz hw hzw hxx]
      field_simp
      ring

/- ## The uniformisation map on `ℂ/Λ` -/

/-- The uniformisation map $\phi : \mathbb{C}/\Lambda \to E_\Lambda(\mathbb{C})$, the descent of
`PeriodPair.toPoint` to the quotient. -/
def uniformization (q : ℂ ⧸ L.lattice.toAddSubgroup) : L.weierstrassCurve.toAffine.Point :=
  Quotient.liftOn' q L.toPoint fun a b hab ↦ by
    rw [QuotientAddGroup.leftRel_apply, Submodule.mem_toAddSubgroup] at hab
    exact L.toPoint_eq_iff.mpr (by simpa [sub_eq_neg_add] using neg_mem hab)

/-- `uniformization` on the class of `z` is `toPoint z`. -/
@[simp]
lemma uniformization_mk (z : ℂ) :
    L.uniformization (z : ℂ ⧸ L.lattice.toAddSubgroup) = L.toPoint z :=
  rfl

/-- $\phi(0) = O$. -/
@[simp]
lemma uniformization_zero : L.uniformization 0 = 0 := by
  rw [← QuotientAddGroup.mk_zero, uniformization_mk]
  exact L.toPoint_of_mem (zero_mem _)

/-- $\phi(-q) = -\phi(q)$. -/
lemma uniformization_neg (q : ℂ ⧸ L.lattice.toAddSubgroup) :
    L.uniformization (-q) = -L.uniformization q := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [← QuotientAddGroup.mk_neg, uniformization_mk, uniformization_mk]
  exact L.toPoint_neg z

/-- $\phi(p + q) = \phi(p) + \phi(q)$. -/
lemma uniformization_add (p q : ℂ ⧸ L.lattice.toAddSubgroup) :
    L.uniformization (p + q) = L.uniformization p + L.uniformization q := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective p
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [← QuotientAddGroup.mk_add, uniformization_mk, uniformization_mk, uniformization_mk,
    L.toPoint_add]

/-- $\phi$ is injective: two classes with the same image differ by a lattice element. -/
theorem uniformization_injective : Function.Injective L.uniformization := by
  intro p q h
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective p
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [uniformization_mk, uniformization_mk, L.toPoint_eq_iff] at h
  rw [QuotientAddGroup.eq, Submodule.mem_toAddSubgroup]
  simpa [neg_add_eq_sub] using neg_mem h

/-- $\phi$ is surjective. -/
theorem uniformization_surjective : Function.Surjective L.uniformization := fun P ↦
  let ⟨z, hz⟩ := L.toPoint_surjective P
  ⟨(z : ℂ ⧸ L.lattice.toAddSubgroup), hz⟩

/-- $\phi$ is bijective. -/
theorem uniformization_bijective : Function.Bijective L.uniformization :=
  ⟨L.uniformization_injective, L.uniformization_surjective⟩

/-- The uniformisation map as a group homomorphism
$\mathbb{C}/\Lambda \to E_\Lambda(\mathbb{C})$. -/
def uniformizationHom : ℂ ⧸ L.lattice.toAddSubgroup →+ L.weierstrassCurve.toAffine.Point where
  toFun := L.uniformization
  map_zero' := L.uniformization_zero
  map_add' := L.uniformization_add

/-- `uniformizationHom` acts as `uniformization`. -/
@[simp]
lemma uniformizationHom_apply (q : ℂ ⧸ L.lattice.toAddSubgroup) :
    L.uniformizationHom q = L.uniformization q :=
  rfl

/-- **Uniformisation of the curve of a lattice**: $z \mapsto (\wp(z), \tfrac12 \wp'(z))$ induces a
group isomorphism $\mathbb{C}/\Lambda \simeq E_\Lambda(\mathbb{C})$. -/
def uniformizationAddEquiv :
    ℂ ⧸ L.lattice.toAddSubgroup ≃+ L.weierstrassCurve.toAffine.Point :=
  AddEquiv.ofBijective L.uniformizationHom L.uniformization_bijective

/-- `uniformizationAddEquiv` acts as `uniformization`. -/
@[simp]
lemma uniformizationAddEquiv_apply (q : ℂ ⧸ L.lattice.toAddSubgroup) :
    L.uniformizationAddEquiv q = L.uniformization q :=
  rfl

end PeriodPair

end
