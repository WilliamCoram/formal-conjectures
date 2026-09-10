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
# The periods of ten LMFDB curves over quadratic fields

For an elliptic curve $E$ over a number field $K$ the period in the Birch and Swinnerton-Dyer
conjecture is $\Omega(E/K) = \prod_{v \mid \infty} \Omega_v(E_v)$, computed on a global minimal
model (LMFDB knowl `ec.period`): at a real place $\Omega_v = \int_{E_v(\mathbb{R})} |\omega|$,
which is `WeierstrassCurve.realPeriodIntegral` of the base change, and at a complex place
$\Omega_v = \int_{E_v(\mathbb{C})} |\omega \wedge \bar\omega|$, which is
`WeierstrassCurve.complexPeriodIntegral` of the base change.

This file instantiates the two definitions on ten curves taken from the LMFDB, five over
imaginary and five over real quadratic fields, all of class number one (so the listed model is a
global minimal model). The `a`-invariants are entered exactly as the LMFDB `ainvs` data, as pairs
of integers `(u, v)` standing for `u + v w` (`LMFDB.QuadraticCurve`), and are base-changed along
the explicit infinite places `w ↦ ...` (`LMFDB.QuadraticCurve.map`). For each base change we prove
that the discriminant is what it is (a `linear_combination` certificate modulo `√m ^ 2 = m` and
`I ^ 2 = -1`), hence that the curve is elliptic and, at a real place, the sign of the discriminant,
so that the theorems `complexPeriodIntegral_eq_two_mul_abs_im`,
`realPeriodIntegral_eq_leastRealPeriod` and `realPeriodIntegral_eq_two_mul_leastRealPeriod`
apply and express $\Omega(E/K)$ through the period lattices.

## Numerical check against the LMFDB

| LMFDB curve | `K` | `Ω(E/K)`, LMFDB | `∏ᵥ Ωᵥ`, this file |
|---|---|---|---|
| `2.0.4.1-65.3-a1` | `ℚ(i)` | `1.7008732894138306` | `1.7008732894138306` |
| `2.0.8.1-51.4-a1` | `ℚ(√-2)` | `14.244822644424032` | `14.244822644424032` |
| `2.0.3.1-73.2-a1` | `ℚ(√-3)` | `6.4846681785642341` | `6.4846681785642341` |
| `2.0.7.1-28.2-a2` | `ℚ(√-7)` | `5.2525028111640324` | `5.2525028111640324` |
| `2.0.11.1-27.2-a1` | `ℚ(√-11)` | `4.5792688032839055` | `4.5792688032839055` |
| `2.2.5.1-31.1-a1` | `ℚ(√5)` | `51.508839712536627` | `51.508839712536627` |
| `2.2.8.1-9.1-a1` | `ℚ(√2)` | `1.2669233425030481` | `1.2669233425030481` |
| `2.2.12.1-9.1-a1` | `ℚ(√3)` | `3.2834968692197041` | `3.2834968692197041` |
| `2.2.13.1-4.1-a1` | `ℚ(√13)` | `1.1422605397837213` | `1.1422605397837213` |
| `2.2.17.1-4.1-a1` | `ℚ(√17)` | `2.551261986836842` | `2.551261986836842` |

The last column is the product of the local periods of the definitions above, evaluated
numerically (mpmath, 30 digits) from the same `ainvs`: at a real place by quadrature of
$2\int_{F > 0} dx / \sqrt{F(x)}$, $F = 4x^3 + b_2x^2 + 2b_4x + b_6$ (the integral defining
`realPeriodIntegral`, cross-checked against the classical AGM formulas for the least real
period), and at the complex place as $2 |\operatorname{Im}(\bar\omega_1 \omega_2)|$ for a basis of
the period lattice, obtained from $(g_2, g_3) = (c_4/12, c_6/216)$ by inverting the $j$-invariant
and scaling by the Eisenstein series $E_4, E_6$ (checked by recomputing $g_2, g_3$ from the
basis). The LMFDB values are reproduced to every digit shown, which confirms the two
normalisations that matter for the definitions: at a complex place LMFDB's $\Omega_v$ is twice the
covolume of the period lattice, as `complexPeriodIntegral_eq_two_mul_covolume` says of
`complexPeriodIntegral`, and at a real place it is the integral over all of $E(\mathbb{R})$,
twice the least real period when $E(\mathbb{R})$ has two components. A cruder direct
two-dimensional quadrature of the density $4/|\Psi_2^2(x)|$ defining `complexPeriodIntegral` agrees
with $2\,\mathrm{covol}$ to the accuracy of the quadrature:
`2.0.8.1-51.4-a1`: 10 digits,
`2.0.3.1-73.2-a1`: 9 digits,
`2.0.7.1-28.2-a2`: 10 digits,
`2.0.11.1-27.2-a1`: 10 digits,
`2.0.4.1-65.3-a1`: only 0.2 %, two of its roots being a mere `0.024` apart.

The LMFDB data were read from the `ecnf-data` repository (`curves.*`, `mwdata.*`) and the LMFDB
curve pages (`Ω(E/K)` for the imaginary quadratic fields, which `ecnf-data` does not carry). The
exact discriminants below have the norms of the `normdisc` column and satisfy $c_4^3 = j \Delta$
with the `jinv` column.
-/

open WeierstrassCurve

namespace LMFDB

/-- LMFDB's `ainvs` for a curve over a quadratic field `K = ℚ(w)`: the five `a`-invariants as
pairs of integers `(u, v)` standing for `u + v w`. -/
structure QuadraticCurve where
  /-- `a₁ = u + v w`. -/
  a₁ : ℤ × ℤ
  /-- `a₂ = u + v w`. -/
  a₂ : ℤ × ℤ
  /-- `a₃ = u + v w`. -/
  a₃ : ℤ × ℤ
  /-- `a₄ = u + v w`. -/
  a₄ : ℤ × ℤ
  /-- `a₆ = u + v w`. -/
  a₆ : ℤ × ℤ

/-- The base change of the curve along the embedding `K → F` sending `w` to `w`. -/
def QuadraticCurve.map (E : QuadraticCurve) {F : Type*} [Field F] (w : F) : WeierstrassCurve F where
  a₁ := E.a₁.1 + E.a₁.2 * w
  a₂ := E.a₂.1 + E.a₂.2 * w
  a₃ := E.a₃.1 + E.a₃.2 * w
  a₄ := E.a₄.1 + E.a₄.2 * w
  a₆ := E.a₆.1 + E.a₆.2 * w

/-- `Ω(E/K)` for a real quadratic field: the product of the real periods at the two real places
`w ↦ w`, `w ↦ w'` (LMFDB knowl `ec.period`, for a global minimal model). -/
def QuadraticCurve.realGlobalPeriod (E : QuadraticCurve) (w w' : ℝ) : ℝ :=
  (E.map w).realPeriodIntegral * (E.map w').realPeriodIntegral

/-- `Ω(E/K)` for an imaginary quadratic field: the complex period at its complex place `w ↦ w`
(LMFDB knowl `ec.period`, for a global minimal model). -/
def QuadraticCurve.complexGlobalPeriod (E : QuadraticCurve) (w : ℂ) : ℝ :=
  (E.map w).complexPeriodIntegral

/-! ### `2.0.4.1-65.3-a1` over `ℚ(i)` -/

namespace «2.0.4.1»

/-- `w = i`, the generator of `ℚ(i)` (LMFDB field `2.0.4.1`, `w² = -1`), at
its complex place. -/
def w : ℂ := Complex.I

/-- LMFDB `2.0.4.1-65.3-a1`: `[a₁, a₂, a₃, a₄, a₆] = [w + 1, -w, w, -240w - 399, 2869w + 2627]`, a
global minimal model, of conductor norm `65`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
1.7008732894138306`. -/
def «65.3-a1» : QuadraticCurve := ⟨(1, 1), (0, -1), (0, 1), (-399, -240), (2627, 2869)⟩

/-- `Δ = 14611 - 10798 * i ≠ 0`. -/
lemma Δ_w : («65.3-a1».map w).Δ = 14611 - 10798 * Complex.I := by
  simp only [QuadraticCurve.map, «65.3-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-3108 : ℂ) * Complex.I ^ 5 + (72505 : ℂ) * Complex.I ^ 4 +
    (48129 : ℂ) * Complex.I ^ 3 + (-55388133 : ℂ) * Complex.I ^ 2 + (831643452 : ℂ) * Complex.I +
    (1008742515 : ℂ)) * Complex.I_sq

lemma Δ_w_ne : («65.3-a1».map w).Δ ≠ 0 := by
  rw [Δ_w]
  intro h
  have h' := congrArg Complex.im h
  simp at h'

instance : («65.3-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_ne⟩

/-- `Ω(E/K) = Ω_w = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 0.85043664470691529 = 1.7008732894138306`; LMFDB gives
`1.7008732894138306`. -/
example : «65.3-a1».complexGlobalPeriod w =
    2 * |((starRingEnd ℂ) («65.3-a1».map w).periodPair.ω₁ * («65.3-a1».map w).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

end «2.0.4.1»

/-! ### `2.0.8.1-51.4-a1` over `ℚ(√-2)` -/

namespace «2.0.8.1»

/-- `w = √-2`, the generator of `ℚ(√-2)` (LMFDB field `2.0.8.1`, `w² = -2`), at
its complex place. -/
def w : ℂ := √2 * Complex.I

/-- LMFDB `2.0.8.1-51.4-a1`: `[a₁, a₂, a₃, a₄, a₆] = [w, -w - 1, 1, 0, 0]`, a global minimal model,
of conductor norm `51` and rank `1`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
14.244822644424032`. -/
def «51.4-a1» : QuadraticCurve := ⟨(0, 1), (-1, -1), (1, 0), (0, 0), (0, 0)⟩

/-- `Δ = -47 + 14 * √2 i ≠ 0`. -/
lemma Δ_w : («51.4-a1».map w).Δ = -47 + 14 * √2 * Complex.I := by
  have hs : ((√2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [QuadraticCurve.map, «51.4-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℂ) * ((√2 : ℝ) : ℂ) ^ 5 * Complex.I ^ 3 +
    (-1 : ℂ) * ((√2 : ℝ) : ℂ) ^ 5 * Complex.I + (-7 : ℂ) * ((√2 : ℝ) : ℂ) ^ 4 * Complex.I ^ 2 +
    (7 : ℂ) * ((√2 : ℝ) : ℂ) ^ 4 + (1 : ℂ) * ((√2 : ℝ) : ℂ) ^ 3 * Complex.I +
    (4 : ℂ) * ((√2 : ℝ) : ℂ) ^ 2) * Complex.I_sq + ((1 : ℂ) * ((√2 : ℝ) : ℂ) ^ 3 * Complex.I +
    (-7 : ℂ) * ((√2 : ℝ) : ℂ) ^ 2 + (1 : ℂ) * ((√2 : ℝ) : ℂ) * Complex.I + (-18 : ℂ)) * hs

lemma Δ_w_ne : («51.4-a1».map w).Δ ≠ 0 := by
  rw [Δ_w]
  intro h
  have h' := congrArg Complex.im h
  simp at h'

instance : («51.4-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_ne⟩

/-- `Ω(E/K) = Ω_w = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 7.1224113222120159 = 14.244822644424032`; LMFDB gives
`14.244822644424032`. -/
example : «51.4-a1».complexGlobalPeriod w =
    2 * |((starRingEnd ℂ) («51.4-a1».map w).periodPair.ω₁ * («51.4-a1».map w).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

end «2.0.8.1»

/-! ### `2.0.3.1-73.2-a1` over `ℚ(√-3)` -/

namespace «2.0.3.1»

/-- `w = (1 + √-3)/2`, the generator of `ℚ(√-3)` (LMFDB field `2.0.3.1`, `w² = -1 + w`), at
its complex place. -/
def w : ℂ := (1 + √3 * Complex.I) / 2

/-- LMFDB `2.0.3.1-73.2-a1`: `[a₁, a₂, a₃, a₄, a₆] = [1, -w - 1, 1, -4w + 14, 16w - 6]`, a global
minimal model, of conductor norm `73`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
6.4846681785642341`. -/
def «73.2-a1» : QuadraticCurve := ⟨(1, 0), (-1, -1), (1, 0), (14, -4), (-6, 16)⟩

/-- `Δ = 271 / 2 - 703 / 2 * √3 i ≠ 0`. -/
lemma Δ_w : («73.2-a1».map w).Δ = 271 / 2 - 703 / 2 * √3 * Complex.I := by
  have hs : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [QuadraticCurve.map, «73.2-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((80 : ℂ) * ((√3 : ℝ) : ℂ) ^ 4 * Complex.I ^ 2 +
    (-80 : ℂ) * ((√3 : ℝ) : ℂ) ^ 4 + (3194 : ℂ) * ((√3 : ℝ) : ℂ) ^ 3 * Complex.I +
    (-44180 : ℂ) * ((√3 : ℝ) : ℂ) ^ 2) * Complex.I_sq + ((80 : ℂ) * ((√3 : ℝ) : ℂ) ^ 2 +
    (-3194 : ℂ) * ((√3 : ℝ) : ℂ) * Complex.I + (44420 : ℂ)) * hs

lemma Δ_w_ne : («73.2-a1».map w).Δ ≠ 0 := by
  rw [Δ_w]
  intro h
  have h' := congrArg Complex.im h
  simp at h'

instance : («73.2-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_ne⟩

/-- `Ω(E/K) = Ω_w = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 3.2423340892821171 = 6.4846681785642341`; LMFDB gives
`6.4846681785642341`. -/
example : «73.2-a1».complexGlobalPeriod w =
    2 * |((starRingEnd ℂ) («73.2-a1».map w).periodPair.ω₁ * («73.2-a1».map w).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

end «2.0.3.1»

/-! ### `2.0.7.1-28.2-a2` over `ℚ(√-7)` -/

namespace «2.0.7.1»

/-- `w = (1 + √-7)/2`, the generator of `ℚ(√-7)` (LMFDB field `2.0.7.1`, `w² = -2 + w`), at
its complex place. -/
def w : ℂ := (1 + √7 * Complex.I) / 2

/-- LMFDB `2.0.7.1-28.2-a2`: `[a₁, a₂, a₃, a₄, a₆] = [1, w, w + 1, -10w + 15, -5w - 16]`, a global
minimal model, of conductor norm `28`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
5.2525028111640324`. -/
def «28.2-a2» : QuadraticCurve := ⟨(1, 0), (0, 1), (1, 1), (15, -10), (-16, -5)⟩

/-- `Δ = -3332 - 140 * √7 i ≠ 0`. -/
lemma Δ_w : («28.2-a2».map w).Δ = -3332 - 140 * √7 * Complex.I := by
  have hs : ((√7 : ℝ) : ℂ) ^ 2 = 7 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [QuadraticCurve.map, «28.2-a2», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-1 / 2 : ℂ) * ((√7 : ℝ) : ℂ) ^ 5 * Complex.I ^ 3 +
    (1 / 2 : ℂ) * ((√7 : ℝ) : ℂ) ^ 5 * Complex.I +
    (969 / 16 : ℂ) * ((√7 : ℝ) : ℂ) ^ 4 * Complex.I ^ 2 + (-969 / 16 : ℂ) * ((√7 : ℝ) : ℂ) ^ 4 +
    (34155 / 4 : ℂ) * ((√7 : ℝ) : ℂ) ^ 3 * Complex.I +
    (-288379 / 8 : ℂ) * ((√7 : ℝ) : ℂ) ^ 2) * Complex.I_sq +
    ((-1 / 2 : ℂ) * ((√7 : ℝ) : ℂ) ^ 3 * Complex.I + (969 / 16 : ℂ) * ((√7 : ℝ) : ℂ) ^ 2 +
    (-34169 / 4 : ℂ) * ((√7 : ℝ) : ℂ) * Complex.I + (583541 / 16 : ℂ)) * hs

lemma Δ_w_ne : («28.2-a2».map w).Δ ≠ 0 := by
  rw [Δ_w]
  intro h
  have h' := congrArg Complex.im h
  simp at h'

instance : («28.2-a2».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_ne⟩

/-- `Ω(E/K) = Ω_w = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 2.6262514055820162 = 5.2525028111640324`; LMFDB gives
`5.2525028111640324`. -/
example : «28.2-a2».complexGlobalPeriod w =
    2 * |((starRingEnd ℂ) («28.2-a2».map w).periodPair.ω₁ * («28.2-a2».map w).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

end «2.0.7.1»

/-! ### `2.0.11.1-27.2-a1` over `ℚ(√-11)` -/

namespace «2.0.11.1»

/-- `w = (1 + √-11)/2`, the generator of `ℚ(√-11)` (LMFDB field `2.0.11.1`, `w² = -3 + w`), at
its complex place. -/
def w : ℂ := (1 + √11 * Complex.I) / 2

/-- LMFDB `2.0.11.1-27.2-a1`: `[a₁, a₂, a₃, a₄, a₆] = [w, w, w + 1, -7w + 15, -3w - 13]`, a global
minimal model, of conductor norm `27`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
4.5792688032839055`. -/
def «27.2-a1» : QuadraticCurve := ⟨(0, 1), (0, 1), (1, 1), (15, -7), (-13, -3)⟩

/-- `Δ = -32805 / 2 - 6561 / 2 * √11 i ≠ 0`. -/
lemma Δ_w : («27.2-a1».map w).Δ = -32805 / 2 - 6561 / 2 * √11 * Complex.I := by
  have hs : ((√11 : ℝ) : ℂ) ^ 2 = 11 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [QuadraticCurve.map, «27.2-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-5 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 7 * Complex.I ^ 5 +
    (5 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 7 * Complex.I ^ 3 +
    (-5 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 7 * Complex.I +
    (47 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 6 * Complex.I ^ 4 +
    (-47 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 6 * Complex.I ^ 2 + (47 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 6 +
    (2615 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 5 * Complex.I ^ 3 +
    (-2615 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 5 * Complex.I +
    (-22181 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 4 * Complex.I ^ 2 +
    (22181 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 4 + (582609 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 3 * Complex.I +
    (-2584243 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 2) * Complex.I_sq +
    ((5 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 5 * Complex.I + (-47 / 128 : ℂ) * ((√11 : ℝ) : ℂ) ^ 4 +
    (1335 / 64 : ℂ) * ((√11 : ℝ) : ℂ) ^ 3 * Complex.I + (-11349 / 64 : ℂ) * ((√11 : ℝ) : ℂ) ^ 2 +
    (-553239 / 128 : ℂ) * ((√11 : ℝ) : ℂ) * Complex.I + (2334565 / 128 : ℂ)) * hs

lemma Δ_w_ne : («27.2-a1».map w).Δ ≠ 0 := by
  rw [Δ_w]
  intro h
  have h' := congrArg Complex.im h
  simp at h'

instance : («27.2-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_ne⟩

/-- `Ω(E/K) = Ω_w = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 2.2896344016419527 = 4.5792688032839055`; LMFDB gives
`4.5792688032839055`. -/
example : «27.2-a1».complexGlobalPeriod w =
    2 * |((starRingEnd ℂ) («27.2-a1».map w).periodPair.ω₁ * («27.2-a1».map w).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

end «2.0.11.1»

/-! ### `2.2.5.1-31.1-a1` over `ℚ(√5)` -/

namespace «2.2.5.1»

/-- `w = (1 + √5)/2`, the generator of `ℚ(√5)` (LMFDB field `2.2.5.1`, `w² = 1 + w`), at
the first real place. -/
def w : ℝ := (1 + √5) / 2

/-- The image of `w` at the second real place. -/
def w' : ℝ := (1 - √5) / 2

/-- LMFDB `2.2.5.1-31.1-a1`: `[a₁, a₂, a₃, a₄, a₆] = [1, w + 1, w, w, 0]`, a global minimal model,
of conductor norm `31`. LMFDB: `Ω(E/K) ≈ 51.508839712536627`. -/
def «31.1-a1» : QuadraticCurve := ⟨(1, 0), (1, 1), (0, 1), (0, 1), (0, 0)⟩

/-- `Δ = 17 - 8 * √5 ≈ -0.88854 < 0` at `w`. -/
lemma Δ_w : («31.1-a1».map w).Δ = 17 - 8 * √5 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «31.1-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-1 / 2 : ℝ) * √5 ^ 3 + (17 / 16 : ℝ) * √5 ^ 2 + (-3 / 2 : ℝ) * √5 +
    (51 / 16 : ℝ)) * hs

lemma Δ_w_neg : («31.1-a1».map w).Δ < 0 := by
  rw [Δ_w]
  have h₁ : (2.2360 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √5 < 2.2361 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («31.1-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_neg.ne⟩

/-- `E(ℝ)` is connected at `w`, so `Ω_w = ω₁ ≈ 8.4380598879`. -/
example : («31.1-a1».map w).realPeriodIntegral = («31.1-a1».map w).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg

/-- `Δ = 17 + 8 * √5 ≈ 34.889 > 0` at `w'`. -/
lemma Δ_w' : («31.1-a1».map w').Δ = 17 + 8 * √5 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «31.1-a1», w', WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 / 2 : ℝ) * √5 ^ 3 + (17 / 16 : ℝ) * √5 ^ 2 + (3 / 2 : ℝ) * √5 +
    (51 / 16 : ℝ)) * hs

lemma Δ_w'_pos : 0 < («31.1-a1».map w').Δ := by
  rw [Δ_w']
  have h₁ : (2.2360 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √5 < 2.2361 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («31.1-a1».map w').IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w'_pos.ne'⟩

/-- `E(ℝ)` has two components at `w'`, so `Ω_w' = 2ω₁ ≈ 2 × 3.0521731534 = 6.1043463067`. -/
example : («31.1-a1».map w').realPeriodIntegral = 2 * («31.1-a1».map w').leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_w'_pos

/-- `Ω(E/K) = Ω_w Ω_w' ≈ 8.4380598879 × 6.1043463067 = 51.5088397125`; LMFDB gives
`51.508839712536627`. -/
example : «31.1-a1».realGlobalPeriod w w' =
    («31.1-a1».map w).leastRealPeriod * (2 * («31.1-a1».map w').leastRealPeriod) := by
  rw [QuadraticCurve.realGlobalPeriod, realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg,
    realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_w'_pos]

end «2.2.5.1»

/-! ### `2.2.8.1-9.1-a1` over `ℚ(√2)` -/

namespace «2.2.8.1»

/-- `w = √2`, the generator of `ℚ(√2)` (LMFDB field `2.2.8.1`, `w² = 2`), at
the first real place. -/
def w : ℝ := √2

/-- The image of `w` at the second real place. -/
def w' : ℝ := -√2

/-- LMFDB `2.2.8.1-9.1-a1`: `[a₁, a₂, a₃, a₄, a₆] = [w, -w - 1, w + 1, -40w - 60, -153w - 220]`, a
global minimal model, of conductor norm `9`. LMFDB: `Ω(E/K) ≈ 1.2669233425030481`. -/
def «9.1-a1» : QuadraticCurve := ⟨(0, 1), (-1, -1), (1, 1), (-60, -40), (-220, -153)⟩

/-- `Δ = -5845851 - 4133430 * √2 ≈ -1.1691e+7 < 0` at `w`. -/
lemma Δ_w : («9.1-a1».map w).Δ = -5845851 - 4133430 * √2 := by
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «9.1-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((114 : ℝ) * √2 ^ 5 + (200 : ℝ) * √2 ^ 4 + (-8838 : ℝ) * √2 ^ 3 +
    (292205 : ℝ) * √2 ^ 2 + (3155849 : ℝ) * √2 + (2472600 : ℝ)) * hs

lemma Δ_w_neg : («9.1-a1».map w).Δ < 0 := by
  rw [Δ_w]
  have h₁ : (1.4142 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √2 < 1.4143 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («9.1-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_neg.ne⟩

/-- `E(ℝ)` is connected at `w`, so `Ω_w = ω₁ ≈ 0.72441481967`. -/
example : («9.1-a1».map w).realPeriodIntegral = («9.1-a1».map w).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg

/-- `Δ = -5845851 + 4133430 * √2 ≈ -298.23 < 0` at `w'`. -/
lemma Δ_w' : («9.1-a1».map w').Δ = -5845851 + 4133430 * √2 := by
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «9.1-a1», w', WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-114 : ℝ) * √2 ^ 5 + (200 : ℝ) * √2 ^ 4 + (8838 : ℝ) * √2 ^ 3 +
    (292205 : ℝ) * √2 ^ 2 + (-3155849 : ℝ) * √2 + (2472600 : ℝ)) * hs

lemma Δ_w'_neg : («9.1-a1».map w').Δ < 0 := by
  rw [Δ_w']
  have h₁ : (1.41421 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √2 < 1.41422 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («9.1-a1».map w').IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w'_neg.ne⟩

/-- `E(ℝ)` is connected at `w'`, so `Ω_w' = ω₁ ≈ 1.7488920824`. -/
example : («9.1-a1».map w').realPeriodIntegral = («9.1-a1».map w').leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg

/-- `Ω(E/K) = Ω_w Ω_w' ≈ 0.72441481967 × 1.7488920824 = 1.2669233425`; LMFDB gives
`1.2669233425030481`. -/
example : «9.1-a1».realGlobalPeriod w w' =
    («9.1-a1».map w).leastRealPeriod * («9.1-a1».map w').leastRealPeriod := by
  rw [QuadraticCurve.realGlobalPeriod, realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg,
    realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg]

end «2.2.8.1»

/-! ### `2.2.12.1-9.1-a1` over `ℚ(√3)` -/

namespace «2.2.12.1»

/-- `w = √3`, the generator of `ℚ(√3)` (LMFDB field `2.2.12.1`, `w² = 3`), at
the first real place. -/
def w : ℝ := √3

/-- The image of `w` at the second real place. -/
def w' : ℝ := -√3

/-- LMFDB `2.2.12.1-9.1-a1`: `[a₁, a₂, a₃, a₄, a₆] = [w + 1, w - 1, w, 25w - 45, 72w - 127]`, a
global minimal model, of conductor norm `9`, with complex multiplication by the order of
discriminant `-36`. LMFDB: `Ω(E/K) ≈ 3.2834968692197041`. -/
def «9.1-a1» : QuadraticCurve := ⟨(1, 1), (-1, 1), (0, 1), (-45, 25), (-127, 72)⟩

/-- `Δ = 243 - 162 * √3 ≈ -37.592 < 0` at `w`. -/
lemma Δ_w : («9.1-a1».map w).Δ = 243 - 162 * √3 := by
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «9.1-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-48 : ℝ) * √3 ^ 5 + (-274 : ℝ) * √3 ^ 4 + (2592 : ℝ) * √3 ^ 3 +
    (80574 : ℝ) * √3 ^ 2 + (-594459 : ℝ) * √3 + (785205 : ℝ)) * hs

lemma Δ_w_neg : («9.1-a1».map w).Δ < 0 := by
  rw [Δ_w]
  have h₁ : (1.7320 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («9.1-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_neg.ne⟩

/-- `E(ℝ)` is connected at `w`, so `Ω_w = ω₁ ≈ 2.1178621619`. -/
example : («9.1-a1».map w).realPeriodIntegral = («9.1-a1».map w).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg

/-- `Δ = 243 + 162 * √3 ≈ 523.59 > 0` at `w'`. -/
lemma Δ_w' : («9.1-a1».map w').Δ = 243 + 162 * √3 := by
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «9.1-a1», w', WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((48 : ℝ) * √3 ^ 5 + (-274 : ℝ) * √3 ^ 4 + (-2592 : ℝ) * √3 ^ 3 +
    (80574 : ℝ) * √3 ^ 2 + (594459 : ℝ) * √3 + (785205 : ℝ)) * hs

lemma Δ_w'_pos : 0 < («9.1-a1».map w').Δ := by
  rw [Δ_w']
  have h₁ : (1.7320 : ℝ) < √3 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √3 < 1.7321 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («9.1-a1».map w').IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w'_pos.ne'⟩

/-- `E(ℝ)` has two components at `w'`, so `Ω_w' = 2ω₁ ≈ 2 × 0.77519135295 = 1.5503827059`. -/
example : («9.1-a1».map w').realPeriodIntegral = 2 * («9.1-a1».map w').leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_w'_pos

/-- `Ω(E/K) = Ω_w Ω_w' ≈ 2.1178621619 × 1.5503827059 = 3.28349686922`; LMFDB gives
`3.2834968692197041`. -/
example : «9.1-a1».realGlobalPeriod w w' =
    («9.1-a1».map w).leastRealPeriod * (2 * («9.1-a1».map w').leastRealPeriod) := by
  rw [QuadraticCurve.realGlobalPeriod, realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg,
    realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_w'_pos]

end «2.2.12.1»

/-! ### `2.2.13.1-4.1-a1` over `ℚ(√13)` -/

namespace «2.2.13.1»

/-- `w = (1 + √13)/2`, the generator of `ℚ(√13)` (LMFDB field `2.2.13.1`, `w² = 3 + w`), at
the first real place. -/
def w : ℝ := (1 + √13) / 2

/-- The image of `w` at the second real place. -/
def w' : ℝ := (1 - √13) / 2

/-- LMFDB `2.2.13.1-4.1-a1`: `[a₁, a₂, a₃, a₄, a₆] = [1, 1, w, -29w + 2, -52w - 106]`, a global
minimal model, of conductor norm `4`. LMFDB: `Ω(E/K) ≈ 1.1422605397837213`. -/
def «4.1-a1» : QuadraticCurve := ⟨(1, 0), (1, 0), (0, 1), (2, -29), (-106, -52)⟩

/-- `Δ = -2471216 + 685392 * √13 ≈ -0.00020719 < 0` at `w`. -/
lemma Δ_w : («4.1-a1».map w).Δ = -2471216 + 685392 * √13 := by
  have hs : √13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «4.1-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-27 / 16 : ℝ) * √13 ^ 2 + (1490157 / 8 : ℝ) * √13 + (5328109 / 16 : ℝ)) * hs

lemma Δ_w_neg : («4.1-a1».map w).Δ < 0 := by
  rw [Δ_w]
  have h₁ : (3.6055512754 : ℝ) < √13 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √13 < 3.6055512755 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («4.1-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_neg.ne⟩

/-- `E(ℝ)` is connected at `w`, so `Ω_w = ω₁ ≈ 0.8434716636`. -/
example : («4.1-a1».map w).realPeriodIntegral = («4.1-a1».map w).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg

/-- `Δ = -2471216 - 685392 * √13 ≈ -4.9424e+6 < 0` at `w'`. -/
lemma Δ_w' : («4.1-a1».map w').Δ = -2471216 - 685392 * √13 := by
  have hs : √13 ^ 2 = 13 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «4.1-a1», w', WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-27 / 16 : ℝ) * √13 ^ 2 + (-1490157 / 8 : ℝ) * √13 + (5328109 / 16 : ℝ)) * hs

lemma Δ_w'_neg : («4.1-a1».map w').Δ < 0 := by
  rw [Δ_w']
  have h₁ : (3.6055 : ℝ) < √13 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √13 < 3.6056 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («4.1-a1».map w').IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w'_neg.ne⟩

/-- `E(ℝ)` is connected at `w'`, so `Ω_w' = ω₁ ≈ 1.3542370053`. -/
example : («4.1-a1».map w').realPeriodIntegral = («4.1-a1».map w').leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg

/-- `Ω(E/K) = Ω_w Ω_w' ≈ 0.8434716636 × 1.3542370053 = 1.14226053978`; LMFDB gives
`1.1422605397837213`. -/
example : «4.1-a1».realGlobalPeriod w w' =
    («4.1-a1».map w).leastRealPeriod * («4.1-a1».map w').leastRealPeriod := by
  rw [QuadraticCurve.realGlobalPeriod, realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg,
    realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg]

end «2.2.13.1»

/-! ### `2.2.17.1-4.1-a1` over `ℚ(√17)` -/

namespace «2.2.17.1»

/-- `w = (1 + √17)/2`, the generator of `ℚ(√17)` (LMFDB field `2.2.17.1`, `w² = 4 + w`), at
the first real place. -/
def w : ℝ := (1 + √17) / 2

/-- The image of `w` at the second real place. -/
def w' : ℝ := (1 - √17) / 2

/-- LMFDB `2.2.17.1-4.1-a1`: `[a₁, a₂, a₃, a₄, a₆] = [1, 0, 1, -9w + 22, 106w - 272]`, a global
minimal model, of conductor norm `4`. LMFDB: `Ω(E/K) ≈ 2.551261986836842`. -/
def «4.1-a1» : QuadraticCurve := ⟨(1, 0), (0, 0), (1, 0), (22, -9), (-272, 106)⟩

/-- `Δ = -43438684 + 10535428 * √17 ≈ -1.5449 < 0` at `w`. -/
lemma Δ_w : («4.1-a1».map w).Δ = -43438684 + 10535428 * √17 := by
  have hs : √17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «4.1-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((5832 : ℝ) * √17 + (-5202495 / 4 : ℝ)) * hs

lemma Δ_w_neg : («4.1-a1».map w).Δ < 0 := by
  rw [Δ_w]
  have h₁ : (4.1231056 : ℝ) < √17 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √17 < 4.1231057 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («4.1-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_neg.ne⟩

/-- `E(ℝ)` is connected at `w`, so `Ω_w = ω₁ ≈ 2.7299553523`. -/
example : («4.1-a1».map w).realPeriodIntegral = («4.1-a1».map w).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg

/-- `Δ = -43438684 - 10535428 * √17 ≈ -8.6877e+7 < 0` at `w'`. -/
lemma Δ_w' : («4.1-a1».map w').Δ = -43438684 - 10535428 * √17 := by
  have hs : √17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «4.1-a1», w', WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-5832 : ℝ) * √17 + (-5202495 / 4 : ℝ)) * hs

lemma Δ_w'_neg : («4.1-a1».map w').Δ < 0 := by
  rw [Δ_w']
  have h₁ : (4.1231 : ℝ) < √17 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √17 < 4.1232 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («4.1-a1».map w').IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w'_neg.ne⟩

/-- `E(ℝ)` is connected at `w'`, so `Ω_w' = ω₁ ≈ 0.93454348425`. -/
example : («4.1-a1».map w').realPeriodIntegral = («4.1-a1».map w').leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg

/-- `Ω(E/K) = Ω_w Ω_w' ≈ 2.7299553523 × 0.93454348425 = 2.55126198684`; LMFDB gives
`2.551261986836842`. -/
example : «4.1-a1».realGlobalPeriod w w' =
    («4.1-a1».map w).leastRealPeriod * («4.1-a1».map w').leastRealPeriod := by
  rw [QuadraticCurve.realGlobalPeriod, realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg,
    realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg]

end «2.2.17.1»

end LMFDB

end
