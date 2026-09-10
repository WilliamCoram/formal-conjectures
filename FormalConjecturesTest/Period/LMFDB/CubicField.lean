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

public import FormalConjecturesTest.Period.AlgebraicGeometry.EllipticCurve.ComplexPeriodIntegral
public import FormalConjecturesTest.Period.AlgebraicGeometry.EllipticCurve.RealPeriod

@[expose] public noncomputable section

/-!
# The period of an LMFDB curve over a cubic field with a real and a complex place

The field `K = ℚ(w)`, `w³ - w² + 1 = 0`, is the cubic field of discriminant `-23` (LMFDB
`3.1.23.1`, class number one); it has one real place, `w ↦ ρ ≈ -0.7549`, and one complex place,
`w ↦ σ = (1 - ρ)/2 + (s/2) i` with `s = √(3ρ² - 2ρ - 1)`. So the period of an elliptic curve
`E/K` in the Birch and Swinnerton-Dyer conjecture (LMFDB knowl `ec.period`) is the product of a
real and a complex period,
$$\Omega(E/K) = \Omega_\rho(E) \cdot \Omega_\sigma(E)
  = \int_{E_\rho(\mathbb{R})} |\omega|
    \cdot \int_{E_\sigma(\mathbb{C})} |\omega \wedge \bar\omega|,$$
`WeierstrassCurve.realPeriodIntegral` of one base change times
`WeierstrassCurve.complexPeriodIntegral` of the other (`LMFDB.CubicCurve.mixedGlobalPeriod`). This
file instantiates it on the LMFDB curve `3.1.23.1-89.1-A1`,
`[a₁, a₂, a₃, a₄, a₆] = [w + 1, -w² - w - 1, w² + w, -w², 1 - w²]` (a global minimal model, of
conductor norm `89`), proves that both base changes are elliptic, that `E_ρ(ℝ)` has two components
(`Δ_ρ = 5 - 4ρ > 0`), and expresses `Ω(E/K)` through the period lattices:
$$\Omega(E/K) = 2\omega_1(E_\rho) \cdot 2\,|\operatorname{Im}(\bar\omega_1 \omega_2)(E_\sigma)|.$$

The real root `ρ` is obtained from the intermediate value theorem on `[-1, 0]`; the sign of the
cubic at rational points then locates it (`lt_ρ`, `ρ_lt`), which is all the discriminant
computations need.

## Numerical check against the LMFDB

Evaluating the two local periods numerically as in `QuadraticFields.lean` (quadrature of the
integral defining `realPeriodIntegral` at `ρ`; twice the covolume of the period lattice at `σ`):
`Ω_ρ = 2ω₁ ≈ 2 × 3.549176925459 = 7.098353850919` and
`Ω_σ = 2 covol ≈ 2 × 11.40238486441 = 22.80476972882`, so
`Ω(E/K) ≈ 161.87632502394820401`. The LMFDB page of the curve gives
`Ω(E/K) ≈ 161.876325023948204`, every digit of which is reproduced, and its BSD line
`0.337535471 ≈ 1 · 161.876325 · 1 · 1 / (10² · 4.795832)` uses this value with `√|d_K| = √23`.
(The `mwdata.3.1.23.1` file of the `ecnf-data` repository still carries
`omega = 80.938162511974102`, exactly half: the real period there was taken over one
component of `E_ρ(ℝ)` only, and with it the BSD quotient would be `0.1688`, half of `L(E/K, 1)`.)
-/

open WeierstrassCurve

namespace LMFDB

/-- LMFDB's `ainvs` for a curve over a cubic field `K = ℚ(w)`: the five `a`-invariants as triples
of integers `(u, v, t)` standing for `u + v w + t w²`. -/
structure CubicCurve where
  /-- `a₁ = u + v w + t w²`. -/
  a₁ : ℤ × ℤ × ℤ
  /-- `a₂ = u + v w + t w²`. -/
  a₂ : ℤ × ℤ × ℤ
  /-- `a₃ = u + v w + t w²`. -/
  a₃ : ℤ × ℤ × ℤ
  /-- `a₄ = u + v w + t w²`. -/
  a₄ : ℤ × ℤ × ℤ
  /-- `a₆ = u + v w + t w²`. -/
  a₆ : ℤ × ℤ × ℤ

/-- The base change of the curve along the embedding `K → F` sending `w` to `w`. -/
def CubicCurve.map (E : CubicCurve) {F : Type*} [Field F] (w : F) : WeierstrassCurve F where
  a₁ := E.a₁.1 + E.a₁.2.1 * w + E.a₁.2.2 * w ^ 2
  a₂ := E.a₂.1 + E.a₂.2.1 * w + E.a₂.2.2 * w ^ 2
  a₃ := E.a₃.1 + E.a₃.2.1 * w + E.a₃.2.2 * w ^ 2
  a₄ := E.a₄.1 + E.a₄.2.1 * w + E.a₄.2.2 * w ^ 2
  a₆ := E.a₆.1 + E.a₆.2.1 * w + E.a₆.2.2 * w ^ 2

/-- `Ω(E/K)` for a cubic field with one real place `w ↦ ρ` and one complex place `w ↦ σ`: the real
period at `ρ` times the complex period at `σ` (LMFDB knowl `ec.period`, for a global minimal
model). -/
def CubicCurve.mixedGlobalPeriod (E : CubicCurve) (ρ : ℝ) (σ : ℂ) : ℝ :=
  (E.map ρ).realPeriodIntegral * (E.map σ).complexPeriodIntegral

/-! ### `3.1.23.1-89.1-A1` over the cubic field of discriminant `-23` -/

namespace «3.1.23.1»

/-- `x³ - x² + 1` has a root in `[-1, 0]`, by the intermediate value theorem. -/
lemma exists_root : ∃ x ∈ Set.Icc (-1 : ℝ) 0, x ^ 3 - x ^ 2 + 1 = 0 := by
  have h := intermediate_value_Icc (a := (-1 : ℝ)) (b := 0) (by norm_num)
    (f := fun x : ℝ ↦ x ^ 3 - x ^ 2 + 1) (by fun_prop)
  obtain ⟨x, hx, hfx⟩ := h (show (0 : ℝ) ∈ Set.Icc ((-1 : ℝ) ^ 3 - (-1) ^ 2 + 1)
    ((0 : ℝ) ^ 3 - 0 ^ 2 + 1) by norm_num)
  exact ⟨x, hx, hfx⟩

/-- `w = ρ ≈ -0.7549`, the real root of `x³ - x² + 1`: the real place of `ℚ(w)`. -/
def ρ : ℝ := Classical.choose exists_root

lemma ρ_spec : ρ ∈ Set.Icc (-1 : ℝ) 0 ∧ ρ ^ 3 - ρ ^ 2 + 1 = 0 := Classical.choose_spec exists_root

/-- `x³ - x² + 1` is increasing on `[-1, 0]`: a point of `[-1, 0]` where it is negative lies below
`ρ`. -/
lemma lt_ρ {a : ℝ} (ha : a ≤ 0) (hfa : a ^ 3 - a ^ 2 + 1 < 0) : a < ρ := by
  obtain ⟨⟨_, h2⟩, hf⟩ := ρ_spec
  by_contra h
  have h := not_lt.mp h
  have hg : 0 ≤ ρ ^ 2 + ρ * a + a ^ 2 - ρ - a := by
    nlinarith [sq_nonneg (ρ + a / 2), sq_nonneg a]
  nlinarith [mul_nonneg (sub_nonneg.2 h) hg]

/-- A point where `x³ - x² + 1` is positive lies above `ρ` (if it is at most `ρ`, it is in
`[-1, 0]`, where the cubic is increasing). -/
lemma ρ_lt {a : ℝ} (hfa : 0 < a ^ 3 - a ^ 2 + 1) : ρ < a := by
  obtain ⟨⟨_, h2⟩, hf⟩ := ρ_spec
  by_contra h
  have h := not_lt.mp h
  have ha' : a ≤ 0 := by nlinarith [sq_nonneg a, sq_nonneg (a + 1)]
  have hg : 0 ≤ ρ ^ 2 + ρ * a + a ^ 2 - ρ - a := by
    nlinarith [sq_nonneg (ρ + a / 2), sq_nonneg a]
  nlinarith [mul_nonneg (sub_nonneg.2 h) hg]

lemma ρ_gt : (-0.7549 : ℝ) < ρ := lt_ρ (by norm_num) (by norm_num)

lemma ρ_lt' : ρ < -0.7548 := ρ_lt (by norm_num)

/-- `s = √(3ρ² - 2ρ - 1) ≈ 1.4897`: the complex roots of `x³ - x² + 1` are `(1 - ρ)/2 ± (s/2) i`,
because `x³ - x² + 1 = (x - ρ)(x² + (ρ - 1)x + ρ² - ρ)`. -/
def s : ℝ := √(3 * ρ ^ 2 - 2 * ρ - 1)

lemma s_pos : 0 < s := Real.sqrt_pos.mpr (by nlinarith [ρ_gt, ρ_lt'])

lemma s_sq : s ^ 2 = 3 * ρ ^ 2 - 2 * ρ - 1 := Real.sq_sqrt (by nlinarith [ρ_gt, ρ_lt'])

/-- `w ↦ σ = (1 - ρ)/2 + (s/2) i`: the complex place of `ℚ(w)`. -/
def σ : ℂ := (1 - ρ) / 2 + s / 2 * Complex.I

lemma ρ_cubic : (ρ : ℂ) ^ 3 - (ρ : ℂ) ^ 2 + 1 = 0 := by exact_mod_cast ρ_spec.2

lemma s_sq' : (s : ℂ) ^ 2 = 3 * (ρ : ℂ) ^ 2 - 2 * ρ - 1 := by
  rw [← Complex.ofReal_pow, s_sq]; push_cast; ring

/-- `σ` is a root of `x³ - x² + 1`. -/
lemma σ_cubic : σ ^ 3 - σ ^ 2 + 1 = 0 := by
  simp only [σ]
  linear_combination ((-3 / 8 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 2 + (1 / 8 : ℂ) * (s : ℂ) ^ 3 * Complex.I +
    (1 / 8 : ℂ) * (s : ℂ) ^ 2) * Complex.I_sq + ((3 / 8 : ℂ) * (ρ : ℂ) +
    (-1 / 8 : ℂ) * (s : ℂ) * Complex.I + (-1 / 8 : ℂ)) * s_sq' + ((1 : ℂ)) * ρ_cubic

/-- LMFDB `3.1.23.1-89.1-A1`: `[a₁, a₂, a₃, a₄, a₆] = [w + 1, -w² - w - 1, w² + w, -w², 1 - w²]`, a
global minimal model, of conductor norm `89`; its discriminant is `Δ = 5 - 4w`. LMFDB: `Ω(E/K) ≈
161.876325023948204`. -/
def «89.1-A1» : CubicCurve := ⟨(1, 1, 0), (-1, -1, -1), (0, 1, 1), (0, 0, -1), (1, 0, -1)⟩

/-- `Δ = 5 - 4ρ ≈ 8.0195 > 0` at the real place. -/
lemma Δ_ρ : («89.1-A1».map ρ).Δ = 5 - 4 * ρ := by
  have hρ := ρ_spec.2
  simp only [CubicCurve.map, «89.1-A1», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((9 : ℝ) * ρ ^ 7 + (4 : ℝ) * ρ ^ 6 + (-49 : ℝ) * ρ ^ 5 + (-143 : ℝ) * ρ ^ 4 +
    (-123 : ℝ) * ρ ^ 3 + (265 : ℝ) * ρ ^ 2 + (-50 : ℝ) * ρ + (-410 : ℝ)) * hρ

lemma Δ_ρ_pos : 0 < («89.1-A1».map ρ).Δ := by
  rw [Δ_ρ]; linarith [ρ_spec.1.2]

instance : («89.1-A1».map ρ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ_pos.ne'⟩

/-- `Δ = 5 - 4σ = 3 + 2ρ - 2 s i ≈ 1.4902 - 2.9794i ≠ 0` at the complex place. -/
lemma Δ_σ : («89.1-A1».map σ).Δ = 3 + 2 * (ρ : ℂ) - 2 * (s : ℂ) * Complex.I := by
  simp only [CubicCurve.map, «89.1-A1», σ, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((405 / 1024 : ℂ) * (ρ : ℂ) ^ 8 * (s : ℂ) ^ 2 +
    (-135 / 128 : ℂ) * (ρ : ℂ) ^ 7 * (s : ℂ) ^ 3 * Complex.I +
    (-45 / 16 : ℂ) * (ρ : ℂ) ^ 7 * (s : ℂ) ^ 2 +
    (945 / 512 : ℂ) * (ρ : ℂ) ^ 6 * (s : ℂ) ^ 4 * Complex.I ^ 2 +
    (-945 / 512 : ℂ) * (ρ : ℂ) ^ 6 * (s : ℂ) ^ 4 +
    (105 / 16 : ℂ) * (ρ : ℂ) ^ 6 * (s : ℂ) ^ 3 * Complex.I +
    (721 / 256 : ℂ) * (ρ : ℂ) ^ 6 * (s : ℂ) ^ 2 +
    (-567 / 256 : ℂ) * (ρ : ℂ) ^ 5 * (s : ℂ) ^ 5 * Complex.I ^ 3 +
    (567 / 256 : ℂ) * (ρ : ℂ) ^ 5 * (s : ℂ) ^ 5 * Complex.I +
    (-315 / 32 : ℂ) * (ρ : ℂ) ^ 5 * (s : ℂ) ^ 4 * Complex.I ^ 2 +
    (315 / 32 : ℂ) * (ρ : ℂ) ^ 5 * (s : ℂ) ^ 4 +
    (-721 / 128 : ℂ) * (ρ : ℂ) ^ 5 * (s : ℂ) ^ 3 * Complex.I +
    (4347 / 128 : ℂ) * (ρ : ℂ) ^ 5 * (s : ℂ) ^ 2 +
    (945 / 512 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) ^ 6 * Complex.I ^ 4 +
    (-945 / 512 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) ^ 6 * Complex.I ^ 2 +
    (945 / 512 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) ^ 6 +
    (315 / 32 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) ^ 5 * Complex.I ^ 3 +
    (-315 / 32 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) ^ 5 * Complex.I +
    (3605 / 512 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) ^ 4 * Complex.I ^ 2 +
    (-3605 / 512 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) ^ 4 +
    (-7245 / 128 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) ^ 3 * Complex.I +
    (-69465 / 512 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) ^ 2 +
    (-135 / 128 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 7 * Complex.I ^ 5 +
    (135 / 128 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 7 * Complex.I ^ 3 +
    (-135 / 128 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 7 * Complex.I +
    (-105 / 16 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 6 * Complex.I ^ 4 +
    (105 / 16 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 6 * Complex.I ^ 2 +
    (-105 / 16 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 6 +
    (-721 / 128 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 5 * Complex.I ^ 3 +
    (721 / 128 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 5 * Complex.I +
    (7245 / 128 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 4 * Complex.I ^ 2 +
    (-7245 / 128 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 4 +
    (23155 / 128 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 3 * Complex.I +
    (7495 / 64 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 2 +
    (405 / 1024 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 8 * Complex.I ^ 6 +
    (-405 / 1024 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 8 * Complex.I ^ 4 +
    (405 / 1024 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 8 * Complex.I ^ 2 +
    (-405 / 1024 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 8 +
    (45 / 16 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 7 * Complex.I ^ 5 +
    (-45 / 16 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 7 * Complex.I ^ 3 +
    (45 / 16 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 7 * Complex.I +
    (721 / 256 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 6 * Complex.I ^ 4 +
    (-721 / 256 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 6 * Complex.I ^ 2 +
    (721 / 256 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 6 +
    (-4347 / 128 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 5 * Complex.I ^ 3 +
    (4347 / 128 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 5 * Complex.I +
    (-69465 / 512 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 4 * Complex.I ^ 2 +
    (69465 / 512 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 4 +
    (-7495 / 64 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 3 * Complex.I +
    (-10983 / 256 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 2 +
    (-45 / 512 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 9 * Complex.I ^ 7 +
    (45 / 512 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 9 * Complex.I ^ 5 +
    (-45 / 512 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 9 * Complex.I ^ 3 +
    (45 / 512 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 9 * Complex.I +
    (-45 / 64 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 8 * Complex.I ^ 6 +
    (45 / 64 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 8 * Complex.I ^ 4 +
    (-45 / 64 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 8 * Complex.I ^ 2 + (45 / 64 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 8 +
    (-103 / 128 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 7 * Complex.I ^ 5 +
    (103 / 128 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 7 * Complex.I ^ 3 +
    (-103 / 128 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 7 * Complex.I +
    (1449 / 128 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 6 * Complex.I ^ 4 +
    (-1449 / 128 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 6 * Complex.I ^ 2 +
    (1449 / 128 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 6 +
    (13893 / 256 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 5 * Complex.I ^ 3 +
    (-13893 / 256 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 5 * Complex.I +
    (7495 / 128 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 4 * Complex.I ^ 2 +
    (-7495 / 128 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 4 +
    (3661 / 128 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 3 * Complex.I +
    (36879 / 128 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 2 + (9 / 1024 : ℂ) * (s : ℂ) ^ 10 * Complex.I ^ 8 +
    (-9 / 1024 : ℂ) * (s : ℂ) ^ 10 * Complex.I ^ 6 + (9 / 1024 : ℂ) * (s : ℂ) ^ 10 * Complex.I ^ 4 +
    (-9 / 1024 : ℂ) * (s : ℂ) ^ 10 * Complex.I ^ 2 + (9 / 1024 : ℂ) * (s : ℂ) ^ 10 +
    (5 / 64 : ℂ) * (s : ℂ) ^ 9 * Complex.I ^ 7 + (-5 / 64 : ℂ) * (s : ℂ) ^ 9 * Complex.I ^ 5 +
    (5 / 64 : ℂ) * (s : ℂ) ^ 9 * Complex.I ^ 3 + (-5 / 64 : ℂ) * (s : ℂ) ^ 9 * Complex.I +
    (103 / 1024 : ℂ) * (s : ℂ) ^ 8 * Complex.I ^ 6 +
    (-103 / 1024 : ℂ) * (s : ℂ) ^ 8 * Complex.I ^ 4 +
    (103 / 1024 : ℂ) * (s : ℂ) ^ 8 * Complex.I ^ 2 + (-103 / 1024 : ℂ) * (s : ℂ) ^ 8 +
    (-207 / 128 : ℂ) * (s : ℂ) ^ 7 * Complex.I ^ 5 + (207 / 128 : ℂ) * (s : ℂ) ^ 7 * Complex.I ^ 3 +
    (-207 / 128 : ℂ) * (s : ℂ) ^ 7 * Complex.I + (-4631 / 512 : ℂ) * (s : ℂ) ^ 6 * Complex.I ^ 4 +
    (4631 / 512 : ℂ) * (s : ℂ) ^ 6 * Complex.I ^ 2 + (-4631 / 512 : ℂ) * (s : ℂ) ^ 6 +
    (-1499 / 128 : ℂ) * (s : ℂ) ^ 5 * Complex.I ^ 3 + (1499 / 128 : ℂ) * (s : ℂ) ^ 5 * Complex.I +
    (-3661 / 512 : ℂ) * (s : ℂ) ^ 4 * Complex.I ^ 2 + (3661 / 512 : ℂ) * (s : ℂ) ^ 4 +
    (-12293 / 128 : ℂ) * (s : ℂ) ^ 3 * Complex.I +
    (-94475 / 1024 : ℂ) * (s : ℂ) ^ 2) * Complex.I_sq + ((-1539 / 1024 : ℂ) * (ρ : ℂ) ^ 8 +
    (783 / 512 : ℂ) * (ρ : ℂ) ^ 7 * (s : ℂ) * Complex.I + (6327 / 512 : ℂ) * (ρ : ℂ) ^ 7 +
    (-189 / 512 : ℂ) * (ρ : ℂ) ^ 6 * (s : ℂ) ^ 2 +
    (-951 / 256 : ℂ) * (ρ : ℂ) ^ 6 * (s : ℂ) * Complex.I + (-10733 / 512 : ℂ) * (ρ : ℂ) ^ 6 +
    (81 / 512 : ℂ) * (ρ : ℂ) ^ 5 * (s : ℂ) ^ 3 * Complex.I +
    (1503 / 512 : ℂ) * (ρ : ℂ) ^ 5 * (s : ℂ) ^ 2 +
    (2629 / 512 : ℂ) * (ρ : ℂ) ^ 5 * (s : ℂ) * Complex.I + (21131 / 512 : ℂ) * (ρ : ℂ) ^ 5 +
    (-189 / 256 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) ^ 4 +
    (135 / 128 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) ^ 3 * Complex.I +
    (-1079 / 256 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) ^ 2 +
    (-247 / 8 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) * Complex.I + (-1309 / 8 : ℂ) * (ρ : ℂ) ^ 4 +
    (405 / 512 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 5 * Complex.I +
    (1929 / 512 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 4 +
    (151 / 256 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 3 * Complex.I +
    (5951 / 256 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) ^ 2 +
    (13673 / 512 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) * Complex.I + (95029 / 512 : ℂ) * (ρ : ℂ) ^ 3 +
    (189 / 512 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 6 +
    (-615 / 256 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 5 * Complex.I +
    (-761 / 512 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 4 +
    (-3637 / 128 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 3 * Complex.I +
    (-43865 / 512 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) ^ 2 +
    (1245 / 256 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) * Complex.I + (-11651 / 512 : ℂ) * (ρ : ℂ) ^ 2 +
    (-45 / 512 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 7 * Complex.I + (-351 / 512 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 6 +
    (377 / 512 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 5 * Complex.I +
    (-5557 / 512 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 4 +
    (25833 / 512 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 3 * Complex.I +
    (26387 / 512 : ℂ) * (ρ : ℂ) * (s : ℂ) ^ 2 + (-26909 / 512 : ℂ) * (ρ : ℂ) * (s : ℂ) * Complex.I +
    (-157431 / 512 : ℂ) * (ρ : ℂ) + (-9 / 1024 : ℂ) * (s : ℂ) ^ 8 +
    (5 / 64 : ℂ) * (s : ℂ) ^ 7 * Complex.I + (7 / 64 : ℂ) * (s : ℂ) ^ 6 +
    (197 / 128 : ℂ) * (s : ℂ) ^ 5 * Complex.I + (4575 / 512 : ℂ) * (s : ℂ) ^ 4 +
    (-53 / 4 : ℂ) * (s : ℂ) ^ 3 * Complex.I + (-2059 / 128 : ℂ) * (s : ℂ) ^ 2 +
    (13989 / 128 : ℂ) * (s : ℂ) * Complex.I + (110947 / 1024 : ℂ)) * s_sq' +
    ((-9 / 2 : ℂ) * (ρ : ℂ) ^ 7 + (9 / 2 : ℂ) * (ρ : ℂ) ^ 6 * (s : ℂ) * Complex.I +
    (71 / 2 : ℂ) * (ρ : ℂ) ^ 6 + (-9 : ℂ) * (ρ : ℂ) ^ 5 * (s : ℂ) * Complex.I +
    (-101 / 2 : ℂ) * (ρ : ℂ) ^ 5 + (23 / 2 : ℂ) * (ρ : ℂ) ^ 4 * (s : ℂ) * Complex.I +
    (109 : ℂ) * (ρ : ℂ) ^ 4 + (-207 / 2 : ℂ) * (ρ : ℂ) ^ 3 * (s : ℂ) * Complex.I +
    (-488 : ℂ) * (ρ : ℂ) ^ 3 + (193 / 2 : ℂ) * (ρ : ℂ) ^ 2 * (s : ℂ) * Complex.I +
    (417 : ℂ) * (ρ : ℂ) ^ 2 + (37 / 2 : ℂ) * (ρ : ℂ) * (s : ℂ) * Complex.I + (25 : ℂ) * (ρ : ℂ) +
    (-87 / 2 : ℂ) * (s : ℂ) * Complex.I + (-907 / 2 : ℂ)) * ρ_cubic

lemma Δ_σ_ne : («89.1-A1».map σ).Δ ≠ 0 := by
  rw [Δ_σ]
  intro h
  have h' := congrArg Complex.im h
  simp at h'
  nlinarith [s_pos]

instance : («89.1-A1».map σ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_σ_ne⟩

/-- `E(ℝ)` has two components at `ρ`, so `Ω_ρ = 2ω₁ ≈ 2 × 3.5491769254 = 7.0983538509`. -/
example : («89.1-A1».map ρ).realPeriodIntegral = 2 * («89.1-A1».map ρ).leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_ρ_pos

/-- `Ω_σ = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 11.402384864 = 22.804769728`. -/
example : («89.1-A1».map σ).complexPeriodIntegral =
    2 * |((starRingEnd ℂ) («89.1-A1».map σ).periodPair.ω₁ * («89.1-A1».map σ).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

/-- `Ω(E/K) = Ω_ρ Ω_σ ≈ 7.0983538509 × 22.804769728 = 161.87632502394`; the LMFDB page gives
`161.876325023948204`. -/
example : «89.1-A1».mixedGlobalPeriod ρ σ =
    2 * («89.1-A1».map ρ).leastRealPeriod *
      (2 * |((starRingEnd ℂ) («89.1-A1».map σ).periodPair.ω₁ *
        («89.1-A1».map σ).periodPair.ω₂).im|) := by
  rw [CubicCurve.mixedGlobalPeriod, realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_ρ_pos,
    complexPeriodIntegral_eq_two_mul_abs_im]

end «3.1.23.1»

end LMFDB

end
