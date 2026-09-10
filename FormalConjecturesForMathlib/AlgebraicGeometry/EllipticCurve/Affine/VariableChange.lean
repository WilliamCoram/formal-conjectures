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

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

@[expose] public noncomputable section

/-!
# Variable changes acting on affine points

An admissible change of variables `C = (u, r, s, t)` sends the Weierstrass curve `C • W`, in the
coordinates $(X, Y)$, to `W` in the coordinates $(x, y) = (u^2 X + r,\ u^3 Y + u^2 s X + t)$.
This file transports the affine points along that substitution:
`WeierstrassCurve.Affine.Point.variableChange C` is the map
$(X, Y) \mapsto (u^2 X + r, u^3 Y + u^2 s X + t)$ from `(C • W)(F)` to `W(F)`, and it is an
isomorphism of groups (`WeierstrassCurve.Affine.Point.variableChangeAddEquiv`).

The group law being compatible with the substitution is a matter of the slope, `addX`, `addY`
and `negY` transforming as they should (`slope_variableChange`, `addX_variableChange`,
`addY_variableChange`, `negY_variableChange`); the equation and the nonsingularity condition
transport because the defining polynomial of `W` at the substituted point is $u^6$ times that of
`C • W` (`equation_variableChange_iff`, `nonsingular_variableChange_iff`).

`WeierstrassCurve.Affine.Point.addEquivOfEq` is the trivial isomorphism between the point groups
of two propositionally equal curves; it is what lets one identify the points of a curve given by a
`Classical.choose`d description with those of a curve given by an explicit one.

## Source correspondence

[Sil2009, III.3.1(b)] states that the only changes of variables preserving the Weierstrass form are
the substitutions above, and [Sil2009, III.3.4] describes the induced isomorphism of the curves;
that it is an isomorphism of *groups* is the statement that the group law is defined by the
geometry of lines, which the substitution preserves.

*References:*
- [Sil2009] Joseph H. Silverman. The Arithmetic of Elliptic Curves, 2nd edition, III.1 and III.3,
    https://link.springer.com/book/10.1007/978-0-387-09494-6
-/

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] {W : WeierstrassCurve F} (C : VariableChange F)

/- ## Transport of the equation and of nonsingularity -/

/-- The equation of `C • W` at `(X, Y)` is the equation of `W` at the substituted point: the
defining polynomial of `W` at `(u²X + r, u³Y + u²sX + t)` is `u⁶` times that of `C • W` at
`(X, Y)`. -/
lemma equation_variableChange_iff (x y : F) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [equation_iff', equation_iff']
  have key : (C.u : F) ^ 6 * (y ^ 2 + (C • W).toAffine.a₁ * x * y + (C • W).toAffine.a₃ * y
        - (x ^ 3 + (C • W).toAffine.a₂ * x ^ 2 + (C • W).toAffine.a₄ * x + (C • W).toAffine.a₆))
      = (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) ^ 2
        + W.toAffine.a₁ * (C.u ^ 2 * x + C.r) * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)
        + W.toAffine.a₃ * (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)
        - ((C.u ^ 2 * x + C.r) ^ 3 + W.toAffine.a₂ * (C.u ^ 2 * x + C.r) ^ 2
          + W.toAffine.a₄ * (C.u ^ 2 * x + C.r) + W.toAffine.a₆) := by
    simp only [WeierstrassCurve.toAffine, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [← key, mul_eq_zero, or_iff_right (pow_ne_zero 6 hu)]

/-- The partial derivatives of the two equations are related by an invertible triangular linear
substitution, so nonvanishing of one pair is nonvanishing of the other. -/
private lemma or_ne_zero_congr (u s : F) {A A' B B' : F} (hu : u ≠ 0)
    (hA : A = u ^ 4 * A' - s * u ^ 3 * B') (hB : B = u ^ 3 * B') :
    (A' ≠ 0 ∨ B' ≠ 0) ↔ (A ≠ 0 ∨ B ≠ 0) := by
  constructor
  · rintro (h | h)
    · by_cases hB' : B' = 0
      · exact Or.inl (by rw [hA, hB', mul_zero, sub_zero]; exact mul_ne_zero (pow_ne_zero 4 hu) h)
      · exact Or.inr (by rw [hB]; exact mul_ne_zero (pow_ne_zero 3 hu) hB')
    · exact Or.inr (by rw [hB]; exact mul_ne_zero (pow_ne_zero 3 hu) h)
  · rintro (h | h)
    · by_cases hB' : B' = 0
      · refine Or.inl fun hA' ↦ h ?_
        rw [hA, hB', hA', mul_zero, mul_zero, sub_zero]
      · exact Or.inr hB'
    · refine Or.inr fun hB' ↦ h ?_
      rw [hB, hB', mul_zero]

/-- Nonsingularity transports along the substitution. -/
lemma nonsingular_variableChange_iff (x y : F) :
    (C • W).toAffine.Nonsingular x y ↔
      W.toAffine.Nonsingular (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [nonsingular_iff', nonsingular_iff']
  refine and_congr (equation_variableChange_iff C x y) (or_ne_zero_congr (C.u : F) C.s hu ?_ ?_)
  · simp only [WeierstrassCurve.toAffine, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, Units.val_inv_eq_inv_val]
    field_simp
    ring
  · simp only [WeierstrassCurve.toAffine, variableChange_a₁, variableChange_a₃,
      Units.val_inv_eq_inv_val]
    field_simp
    ring

/- ## Transport of the group-law formulas -/

/-- Negation commutes with the substitution. -/
lemma negY_variableChange (x y : F) :
    W.toAffine.negY (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.u ^ 2 * C.s * x + C.t)
      = C.u ^ 3 * (C • W).toAffine.negY x y + C.u ^ 2 * C.s * x + C.t := by
  simp only [negY, WeierstrassCurve.toAffine, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- The pair `(x₁, y₁)`, `(x₂, y₂)` is a point and its negative exactly when the substituted pair
is. -/
lemma eq_negY_variableChange_iff (x₁ x₂ y₁ y₂ : F) :
    (C.u ^ 2 * x₁ + C.r = C.u ^ 2 * x₂ + C.r ∧ C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t
        = W.toAffine.negY (C.u ^ 2 * x₂ + C.r) (C.u ^ 3 * y₂ + C.u ^ 2 * C.s * x₂ + C.t))
      ↔ (x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [negY_variableChange]
  constructor
  · rintro ⟨hx, hy⟩
    have hx' : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (add_right_cancel hx)
    subst hx'
    refine ⟨rfl, mul_left_cancel₀ (pow_ne_zero 3 hu) ?_⟩
    linear_combination hy
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

/-- The slope of the line through two distinct affine points of the curve transforms as
`ℓ ↦ u ℓ + s`. -/
lemma slope_variableChange [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁)
    (h₂ : (C • W).toAffine.Equation x₂ y₂) (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope (C.u ^ 2 * x₁ + C.r) (C.u ^ 2 * x₂ + C.r)
        (C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t) (C.u ^ 3 * y₂ + C.u ^ 2 * C.s * x₂ + C.t)
      = C.u * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hy' : C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t
        ≠ W.toAffine.negY (C.u ^ 2 * x₁ + C.r) (C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t) :=
      fun h ↦ hy ((eq_negY_variableChange_iff C x₁ x₁ y₁ y₁).mp ⟨rfl, h⟩).2
    rw [slope_of_Y_ne rfl hy', slope_of_Y_ne rfl hy, negY_variableChange,
      show C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t
          - (C.u ^ 3 * (C • W).toAffine.negY x₁ y₁ + C.u ^ 2 * C.s * x₁ + C.t)
        = C.u ^ 3 * (y₁ - (C • W).toAffine.negY x₁ y₁) by ring]
    have hden : y₁ - (C • W).toAffine.negY x₁ y₁ ≠ 0 := sub_ne_zero.mpr hy
    -- the numerators are related by the same triangular substitution as the partial derivatives
    have key : 3 * (C.u ^ 2 * x₁ + C.r) ^ 2 + 2 * W.toAffine.a₂ * (C.u ^ 2 * x₁ + C.r)
          + W.toAffine.a₄ - W.toAffine.a₁ * (C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t)
        = C.u ^ 4 * (3 * x₁ ^ 2 + 2 * (C • W).toAffine.a₂ * x₁ + (C • W).toAffine.a₄
            - (C • W).toAffine.a₁ * y₁)
          + C.s * C.u ^ 3 * (y₁ - (C • W).toAffine.negY x₁ y₁) := by
      simp only [negY, WeierstrassCurve.toAffine, variableChange_a₁, variableChange_a₂,
        variableChange_a₃, variableChange_a₄, Units.val_inv_eq_inv_val]
      field_simp
      ring
    rw [key, div_eq_iff (mul_ne_zero (pow_ne_zero 3 hu) hden)]
    field_simp
  · have hx' : C.u ^ 2 * x₁ + C.r ≠ C.u ^ 2 * x₂ + C.r :=
      fun h ↦ hx (mul_left_cancel₀ (pow_ne_zero 2 hu) (add_right_cancel h))
    rw [slope_of_X_ne hx', slope_of_X_ne hx]
    have hne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    field_simp
    ring

/-- The `x`-coordinate of the sum transforms along the substitution, the slope transforming as
`ℓ ↦ u ℓ + s`. -/
lemma addX_variableChange (x₁ x₂ ℓ : F) :
    W.toAffine.addX (C.u ^ 2 * x₁ + C.r) (C.u ^ 2 * x₂ + C.r) (C.u * ℓ + C.s)
      = C.u ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp only [addX, WeierstrassCurve.toAffine, variableChange_a₁, variableChange_a₂,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- The `y`-coordinate of the sum transforms along the substitution. -/
lemma addY_variableChange (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY (C.u ^ 2 * x₁ + C.r) (C.u ^ 2 * x₂ + C.r)
        (C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t) (C.u * ℓ + C.s)
      = C.u ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + C.u ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [addY, negAddY, addX, negY, WeierstrassCurve.toAffine, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, Units.val_inv_eq_inv_val]
  field_simp
  ring

/- ## The map on points -/

namespace Point

/-- The map on affine points induced by the change of variables `C`: the point `(X, Y)` of
`C • W` goes to the point `(u²X + r, u³Y + u²sX + t)` of `W`. -/
def variableChange : (C • W).toAffine.Point → W.toAffine.Point
  | zero => zero
  | some x y h => some _ _ ((nonsingular_variableChange_iff C x y).mp h)

/-- The point at infinity goes to the point at infinity. -/
@[simp]
lemma variableChange_zero : variableChange C (0 : (C • W).toAffine.Point) = 0 :=
  rfl

/-- An affine point $(X, Y)$ goes to $(u^2 X + r, u^3 Y + u^2 s X + t)$. -/
@[simp]
lemma variableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    variableChange C (some x y h) = some _ _ ((nonsingular_variableChange_iff C x y).mp h) :=
  rfl

/-- The map on points commutes with negation. -/
lemma variableChange_neg (P : (C • W).toAffine.Point) :
    variableChange C (-P) = -variableChange C P := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [neg_some, variableChange_some, variableChange_some, neg_some]
    congr 1
    exact (negY_variableChange C x y).symm

/-- The map on points is additive: the chord-and-tangent law is preserved by the
substitution. -/
lemma variableChange_add [DecidableEq F] (P Q : (C • W).toAffine.Point) :
    variableChange C (P + Q) = variableChange C P + variableChange C Q := by
  cases P with
  | zero =>
    change variableChange C (0 + Q) = variableChange C 0 + variableChange C Q
    rw [zero_add, variableChange_zero, zero_add]
  | some x₁ y₁ h₁ =>
  cases Q with
  | zero =>
    change variableChange C (some x₁ y₁ h₁ + 0)
      = variableChange C (some x₁ y₁ h₁) + variableChange C 0
    rw [add_zero, variableChange_zero, add_zero]
  | some x₂ y₂ h₂ =>
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · obtain ⟨hx, hy⟩ := hxy
    have hxy' := (eq_negY_variableChange_iff C x₁ x₂ y₁ y₂).mpr ⟨hx, hy⟩
    rw [add_of_Y_eq hx hy, variableChange_zero, variableChange_some, variableChange_some,
      add_of_Y_eq hxy'.1 hxy'.2]
  · have hxy' : ¬(C.u ^ 2 * x₁ + C.r = C.u ^ 2 * x₂ + C.r ∧ C.u ^ 3 * y₁ + C.u ^ 2 * C.s * x₁ + C.t
        = W.toAffine.negY (C.u ^ 2 * x₂ + C.r) (C.u ^ 3 * y₂ + C.u ^ 2 * C.s * x₂ + C.t)) :=
      fun h ↦ hxy ((eq_negY_variableChange_iff C x₁ x₂ y₁ y₂).mp h)
    rw [add_some hxy, variableChange_some, variableChange_some, variableChange_some,
      add_some hxy']
    congr 1
    · rw [slope_variableChange C h₁.1 h₂.1 hxy, addX_variableChange]
    · rw [slope_variableChange C h₁.1 h₂.1 hxy, addY_variableChange]

/-- The map on points is injective, the substitution being invertible. -/
lemma variableChange_injective : Function.Injective (variableChange C (W := W)) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  intro P Q h
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y hQ => exact absurd h.symm (some_ne_zero _)
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => exact absurd h (some_ne_zero _)
    | some x₂ y₂ h₂ =>
      rw [variableChange_some, variableChange_some] at h
      obtain ⟨hx, hy⟩ := some.inj h
      have hx' : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (add_right_cancel hx)
      subst hx'
      have hy' : y₁ = y₂ := mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hy)
      subst hy'
      rfl

/-- The map on points is surjective: $(x, y)$ is the image of
$(u^{-2}(x - r),\ u^{-3}(y - s(x - r) - t))$. -/
lemma variableChange_surjective : Function.Surjective (variableChange C (W := W)) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  intro P
  cases P with
  | zero => exact ⟨0, rfl⟩
  | some x y h =>
    -- the preimage of `(x, y)` is `(X, Y) = (u⁻²(x - r), u⁻³(y - s(x - r) - t))`
    have hx : C.u ^ 2 * ((C.u : F)⁻¹ ^ 2 * (x - C.r)) + C.r = x := by
      field_simp
      ring
    have hy : C.u ^ 3 * ((C.u : F)⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t))
        + C.u ^ 2 * C.s * ((C.u : F)⁻¹ ^ 2 * (x - C.r)) + C.t = y := by
      field_simp
      ring
    have hns : (C • W).toAffine.Nonsingular ((C.u : F)⁻¹ ^ 2 * (x - C.r))
        ((C.u : F)⁻¹ ^ 3 * (y - C.s * (x - C.r) - C.t)) := by
      rw [nonsingular_variableChange_iff, hx, hy]
      exact h
    refine ⟨some _ _ hns, ?_⟩
    rw [variableChange_some]
    congr 1

/-- The change of variables `C` induces a homomorphism of groups `(C • W)(F) →+ W(F)`. -/
def variableChangeHom [DecidableEq F] : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := variableChange C
  map_zero' := variableChange_zero C
  map_add' := variableChange_add C

/-- `variableChangeHom` acts as `variableChange`. -/
@[simp]
lemma variableChangeHom_apply [DecidableEq F] (P : (C • W).toAffine.Point) :
    variableChangeHom C P = variableChange C P :=
  rfl

/-- The change of variables `C` induces an isomorphism of groups `(C • W)(F) ≃+ W(F)`. -/
def variableChangeAddEquiv [DecidableEq F] : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  AddEquiv.ofBijective (variableChangeHom C)
    ⟨variableChange_injective C, variableChange_surjective C⟩

/-- `variableChangeAddEquiv` acts as `variableChange`. -/
@[simp]
lemma variableChangeAddEquiv_apply [DecidableEq F] (P : (C • W).toAffine.Point) :
    variableChangeAddEquiv C P = variableChange C P :=
  rfl

/- ## Propositionally equal curves -/

/-- The isomorphism between the point groups of two equal curves. -/
def addEquivOfEq [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    W₁.toAffine.Point ≃+ W₂.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

/-- `addEquivOfEq rfl` is the identity. -/
@[simp]
lemma addEquivOfEq_refl [DecidableEq F] (W₁ : WeierstrassCurve F) :
    addEquivOfEq (rfl : W₁ = W₁) = AddEquiv.refl _ :=
  rfl

/-- `addEquivOfEq` fixes the point at infinity. -/
lemma addEquivOfEq_zero [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) :
    addEquivOfEq h (0 : W₁.toAffine.Point) = 0 := by
  subst h
  rfl

/-- `addEquivOfEq` fixes the coordinates of an affine point. -/
lemma addEquivOfEq_some [DecidableEq F] {W₁ W₂ : WeierstrassCurve F} (h : W₁ = W₂) {x y : F}
    (hxy : W₁.toAffine.Nonsingular x y) :
    addEquivOfEq h (some x y hxy) = some x y (h ▸ hxy) := by
  subst h
  rfl

end Point

end WeierstrassCurve.Affine

end
