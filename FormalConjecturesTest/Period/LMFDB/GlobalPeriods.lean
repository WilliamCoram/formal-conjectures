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

public import FormalConjecturesTest.Period.LMFDB.CubicField
public import FormalConjecturesTest.Period.LMFDB.QuadraticFields

@[expose] public noncomputable section

/-!
# The global periods of twenty LMFDB curves of rank 0, 1 and 2

For an elliptic curve $E$ over a number field $K$ the period in the Birch and Swinnerton-Dyer
conjecture is $\Omega(E/K) = \prod_{v \mid \infty} \Omega_v(E_v)$, computed on a global minimal
model (LMFDB knowl `ec.period`), with $\Omega_v$ the integral of $|\omega|$ over $E_v(\mathbb{R})$
at a real place (`WeierstrassCurve.realPeriodIntegral`) and of $|\omega \wedge \bar\omega|$ over
$E_v(\mathbb{C})$ at a complex place (`WeierstrassCurve.complexPeriodIntegral`).
`QuadraticFields.lean` and `CubicField.lean` check these definitions on eleven curves; this file
adds twenty more, chosen to cover every signature of field of degree at most three and ranks
`0`, `1` and `2` (`ecnf-data` has no curve of rank `2` over the totally real cubic fields
`3.3.49.1`, `3.3.81.1` and `3.3.148.1`):

* over `ℚ`: `rationalGlobalPeriod`, the real period of the base change to `ℝ`;
* over `ℚ(i)` and `ℚ(√-3)`: `QuadraticCurve.complexGlobalPeriod`, one complex place;
* over `ℚ(√5)` and `ℚ(√2)`: `QuadraticCurve.realGlobalPeriod`, two real places;
* over the cubic field `3.1.23.1`: `CubicCurve.mixedGlobalPeriod`, a real and a complex place;
* over the totally real cubic fields `3.3.49.1` and `3.3.81.1`: `CubicCurve.realGlobalPeriod`,
  three real places.

All fields have class number one, so the LMFDB model is a global minimal model. For each base
change we prove the discriminant (a `linear_combination` certificate modulo the minimal polynomial
of the place, or `√m ^ 2 = m` and `I ^ 2 = -1`), hence that the curve is elliptic and, at a real
place, the sign of the discriminant; then `realPeriodIntegral_eq_leastRealPeriod`,
`realPeriodIntegral_eq_two_mul_leastRealPeriod` and `complexPeriodIntegral_eq_two_mul_abs_im`
express $\Omega(E/K)$ through the period lattices. The places of a totally real cubic field are
roots of its minimal polynomial in disjoint rational intervals, found by the intermediate value
theorem; the places of the other fields are those of the two imported files.

## Numerical check against the LMFDB

| LMFDB curve | `K` | rank | `Ω(E/K)`, LMFDB | `∏ᵥ Ωᵥ`, this file |
|---|---|---|---|---|
| `11.a2` | `ℚ` | 0 | `1.26920930427955` | `1.26920930427955` |
| `37.a1` | `ℚ` | 1 | `5.98691729246392` | `5.98691729246392` |
| `389.a1` | `ℚ` | 2 | `4.98042512171011` | `4.98042512171011` |
| `2.0.4.1-65.2-a5` | `ℚ(i)` | 0 | `15.307859604724475` | `15.307859604724475` |
| `2.0.4.1-233.1-a1` | `ℚ(i)` | 1 | `17.613883210052948` | `17.613883210052948` |
| `2.0.4.1-2053.1-a1` | `ℚ(i)` | 2 | `14.747340402883734` | `14.747340402883734` |
| `2.0.3.1-124.1-a2` | `ℚ(√-3)` | 0 | `18.421589302895372` | `18.421589302895372` |
| `2.0.3.1-283.1-a1` | `ℚ(√-3)` | 1 | `17.499805378424805` | `17.499805378424805` |
| `2.0.3.1-2809.1-a1` | `ℚ(√-3)` | 2 | `14.443472129715849` | `14.443472129715849` |
| `2.2.5.1-36.1-a1` | `ℚ(√5)` | 0 | `44.299621696875097` | `44.299621696875097` |
| `2.2.5.1-199.1-c1` | `ℚ(√5)` | 1 | `42.895444109769151` | `42.895444109769151` |
| `2.2.5.1-1831.1-c1` | `ℚ(√5)` | 2 | `37.781912518434661` | `37.781912518434661` |
| `2.2.8.1-119.1-c1` | `ℚ(√2)` | 1 | `20.018521488357718` | `20.018521488357718` |
| `2.2.8.1-1031.1-b1` | `ℚ(√2)` | 2 | `36.842709403669651` | `36.842709403669651` |
| `3.1.23.1-107.1-A1` | `3.1.23.1` | 0 | `144.23368496198089` | `144.23368496198089` |
| `3.1.23.1-719.3-A1` | `3.1.23.1` | 1 | `135.92435690010297` | `135.92435690010297` |
| `3.1.23.1-9173.1-A1` | `3.1.23.1` | 2 | `111.48202230312048` | `111.48202230312048` |
| `3.3.49.1-41.2-a3` | `3.3.49.1` | 0 | `339.45684154604091` | `339.45684154604091` |
| `3.3.49.1-377.4-c3` | `3.3.49.1` | 1 | `344.26478758311204` | `344.26478758311204` |
| `3.3.81.1-199.2-a1` | `3.3.81.1` | 1 | `359.142964000285` | `359.142964000285` |

The last column is the product of the local periods of the definitions, evaluated numerically
(mpmath, 30 digits) from the same `a`-invariants: at a real place by quadrature of the integral
defining `realPeriodIntegral` (cross-checked against the AGM formula for the least real period),
at a complex place as twice the covolume of the period lattice (by inverting the `j`-invariant and
scaling by Eisenstein series). The LMFDB column reproduces to every digit shown.

The data are Cremona's `ecdata` tables (`allbsd`, whose `OM` column is the LMFDB `real_period`, to
15 significant digits) for the curves over `ℚ`, and the `ecnf-data` tables (`curves.*`, `mwdata.*`)
behind the LMFDB pages for the others; every model satisfies $c_4^3 = j\Delta$ with the `jinv`
column. At a field with a complex place the `omega` column of `mwdata` is half the LMFDB
`Ω(E/K)`: it holds the covolume of the period lattice, not $\int |\omega \wedge \bar\omega|$ (the
LMFDB pages of `2.0.4.1-65.3-a1`, `2.0.8.1-51.4-a1`, `2.0.3.1-73.2-a1` and `3.1.23.1-89.1-A1` give
exactly twice `omega`), so the table shows `2 · omega` there.
-/

open WeierstrassCurve

namespace LMFDB

/-- `Ω(E/ℚ)` for a curve over `ℚ`: the real period of its base change to `ℝ`, at the only infinite
place (LMFDB knowl `ec.period`, for a global minimal model). -/
def rationalGlobalPeriod (E : WeierstrassCurve ℚ) : ℝ :=
  (E.map (algebraMap ℚ ℝ)).realPeriodIntegral

/-- `Ω(E/K)` for a totally real cubic field: the product of the real periods at the three real
places `w ↦ w₁, w₂, w₃` (LMFDB knowl `ec.period`, for a global minimal model). -/
def CubicCurve.realGlobalPeriod (E : CubicCurve) (w₁ w₂ w₃ : ℝ) : ℝ :=
  (E.map w₁).realPeriodIntegral * (E.map w₂).realPeriodIntegral * (E.map w₃).realPeriodIntegral

/-! ### `11.a2` over `ℚ`, rank `0` -/

/-- LMFDB `11.a2` (Cremona `11a1`): `[a₁, a₂, a₃, a₄, a₆] = [0, -1, 1, -10, -20]`, the global
minimal model, of conductor `11` and rank `0`. LMFDB: `Ω(E/ℚ) ≈ 1.26920930427955`. -/
def «11.a2» : WeierstrassCurve ℚ := ⟨0, -1, 1, -10, -20⟩

namespace «11.a2»

lemma Δ_eq : «11.a2».Δ = -161051 := by
  simp only [«11.a2», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

lemma Δ_neg : («11.a2».map (algebraMap ℚ ℝ)).Δ < 0 := by
  rw [map_Δ, Δ_eq]; norm_num

instance : («11.a2».map (algebraMap ℚ ℝ)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_neg.ne⟩

/-- `E(ℝ)` is connected, so `Ω(E/ℚ) = ω₁ ≈ 1.26920930427955`; LMFDB gives `1.26920930427955`. -/
example : rationalGlobalPeriod «11.a2» = («11.a2».map (algebraMap ℚ ℝ)).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_neg

end «11.a2»

/-! ### `37.a1` over `ℚ`, rank `1` -/

/-- LMFDB `37.a1` (Cremona `37a1`): `[a₁, a₂, a₃, a₄, a₆] = [0, 0, 1, -1, 0]`, the global minimal
model, of conductor `37` and rank `1`. LMFDB: `Ω(E/ℚ) ≈ 5.98691729246392`. -/
def «37.a1» : WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩

namespace «37.a1»

lemma Δ_eq : «37.a1».Δ = 37 := by
  simp only [«37.a1», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

lemma Δ_pos : 0 < («37.a1».map (algebraMap ℚ ℝ)).Δ := by
  rw [map_Δ, Δ_eq]; norm_num

instance : («37.a1».map (algebraMap ℚ ℝ)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_pos.ne'⟩

/-- `E(ℝ)` has two components, so `Ω(E/ℚ) = 2ω₁ ≈ 2 × 2.99345864623196 = 5.98691729246392`; LMFDB
gives `5.98691729246392`. -/
example : rationalGlobalPeriod «37.a1» = 2 * («37.a1».map (algebraMap ℚ ℝ)).leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_pos

end «37.a1»

/-! ### `389.a1` over `ℚ`, rank `2` -/

/-- LMFDB `389.a1` (Cremona `389a1`): `[a₁, a₂, a₃, a₄, a₆] = [0, 1, 1, -2, 0]`, the global minimal
model, of conductor `389` and rank `2`. LMFDB: `Ω(E/ℚ) ≈ 4.98042512171011`. -/
def «389.a1» : WeierstrassCurve ℚ := ⟨0, 1, 1, -2, 0⟩

namespace «389.a1»

lemma Δ_eq : «389.a1».Δ = 389 := by
  simp only [«389.a1», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

lemma Δ_pos : 0 < («389.a1».map (algebraMap ℚ ℝ)).Δ := by
  rw [map_Δ, Δ_eq]; norm_num

instance : («389.a1».map (algebraMap ℚ ℝ)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_pos.ne'⟩

/-- `E(ℝ)` has two components, so `Ω(E/ℚ) = 2ω₁ ≈ 2 × 2.49021256085506 = 4.98042512171011`; LMFDB
gives `4.98042512171011`. -/
example : rationalGlobalPeriod «389.a1» = 2 * («389.a1».map (algebraMap ℚ ℝ)).leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_pos

end «389.a1»

/-! ### `2.0.4.1-65.2-a5` over `ℚ(i)`, rank `0` -/

namespace «2.0.4.1»

/-- LMFDB `2.0.4.1-65.2-a5`: `[a₁, a₂, a₃, a₄, a₆] = [w + 1, 0, w, -w + 1, 0]`, a global minimal
model, of conductor norm `65` and rank `0`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
15.307859604724475`. -/
def «65.2-a5» : QuadraticCurve := ⟨(1, 1), (0, 0), (0, 1), (1, -1), (0, 0)⟩

namespace «65.2-a5»

/-- `Δ = -29 - 2 * i ≠ 0`. -/
lemma Δ_w : («65.2-a5».map w).Δ = -29 - 2 * Complex.I := by
  simp only [QuadraticCurve.map, «65.2-a5», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-1 : ℂ) * Complex.I ^ 5 + (-2 : ℂ) * Complex.I ^ 4 +
    (31 : ℂ) * Complex.I ^ 3 + (-89 : ℂ) * Complex.I ^ 2 + (101 : ℂ) * Complex.I +
    (-34 : ℂ)) * Complex.I_sq

lemma Δ_w_ne : («65.2-a5».map w).Δ ≠ 0 := by
  rw [Δ_w]
  intro h
  have h' := congrArg Complex.im h
  simp at h'

instance : («65.2-a5».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_ne⟩

/-- `Ω(E/K) = Ω_w = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 7.6539298023622376 = 15.307859604724475`; LMFDB gives
`15.307859604724475`. -/
example : «65.2-a5».complexGlobalPeriod w =
    2 * |((starRingEnd ℂ) («65.2-a5».map w).periodPair.ω₁ *
      («65.2-a5».map w).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

end «65.2-a5»

end «2.0.4.1»

/-! ### `2.0.4.1-233.1-a1` over `ℚ(i)`, rank `1` -/

namespace «2.0.4.1»

/-- LMFDB `2.0.4.1-233.1-a1`: `[a₁, a₂, a₃, a₄, a₆] = [0, w - 1, 1, -w, 0]`, a global minimal model,
of conductor norm `233` and rank `1`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
17.613883210052948`. -/
def «233.1-a1» : QuadraticCurve := ⟨(0, 0), (-1, 1), (1, 0), (0, -1), (0, 0)⟩

namespace «233.1-a1»

/-- `Δ = 13 + 8 * i ≠ 0`. -/
lemma Δ_w : («233.1-a1».map w).Δ = 13 + 8 * Complex.I := by
  simp only [QuadraticCurve.map, «233.1-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((16 : ℂ) * Complex.I ^ 2 + (16 : ℂ) * Complex.I + (-24 : ℂ)) * Complex.I_sq

lemma Δ_w_ne : («233.1-a1».map w).Δ ≠ 0 := by
  rw [Δ_w]
  intro h
  have h' := congrArg Complex.im h
  simp at h'

instance : («233.1-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_ne⟩

/-- `Ω(E/K) = Ω_w = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 8.8069416050264741 = 17.613883210052948`; LMFDB gives
`17.613883210052948`. -/
example : «233.1-a1».complexGlobalPeriod w =
    2 * |((starRingEnd ℂ) («233.1-a1».map w).periodPair.ω₁ *
      («233.1-a1».map w).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

end «233.1-a1»

end «2.0.4.1»

/-! ### `2.0.4.1-2053.1-a1` over `ℚ(i)`, rank `2` -/

namespace «2.0.4.1»

/-- LMFDB `2.0.4.1-2053.1-a1`: `[a₁, a₂, a₃, a₄, a₆] = [w + 1, w + 1, w, w, 0]`, a global minimal
model, of conductor norm `2053` and rank `2`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
14.747340402883734`. -/
def «2053.1-a1» : QuadraticCurve := ⟨(1, 1), (1, 1), (0, 1), (0, 1), (0, 0)⟩

namespace «2053.1-a1»

/-- `Δ = -17 + 42 * i ≠ 0`. -/
lemma Δ_w : («2053.1-a1».map w).Δ = -17 + 42 * Complex.I := by
  simp only [QuadraticCurve.map, «2053.1-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((2 : ℂ) * Complex.I ^ 4 + (21 : ℂ) * Complex.I ^ 3 + (8 : ℂ) * Complex.I ^ 2 +
    (-42 : ℂ) * Complex.I + (17 : ℂ)) * Complex.I_sq

lemma Δ_w_ne : («2053.1-a1».map w).Δ ≠ 0 := by
  rw [Δ_w]
  intro h
  have h' := congrArg Complex.im h
  simp at h'

instance : («2053.1-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_ne⟩

/-- `Ω(E/K) = Ω_w = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 7.3736702014418672 = 14.747340402883734`; LMFDB gives
`14.747340402883734`. -/
example : «2053.1-a1».complexGlobalPeriod w =
    2 * |((starRingEnd ℂ) («2053.1-a1».map w).periodPair.ω₁ *
      («2053.1-a1».map w).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

end «2053.1-a1»

end «2.0.4.1»

/-! ### `2.0.3.1-124.1-a2` over `ℚ(√-3)`, rank `0` -/

namespace «2.0.3.1»

/-- LMFDB `2.0.3.1-124.1-a2`: `[a₁, a₂, a₃, a₄, a₆] = [w + 1, w, w, 0, 0]`, a global minimal model,
of conductor norm `124` and rank `0`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
18.421589302895372`. -/
def «124.1-a2» : QuadraticCurve := ⟨(1, 1), (0, 1), (0, 1), (0, 0), (0, 0)⟩

namespace «124.1-a2»

/-- `Δ = -11 - √3 i ≠ 0`. -/
lemma Δ_w : («124.1-a2».map w).Δ = -11 - √3 * Complex.I := by
  have hs : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [QuadraticCurve.map, «124.1-a2», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-1 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 7 * Complex.I ^ 5 +
    (1 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 7 * Complex.I ^ 3 +
    (-1 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 7 * Complex.I +
    (-29 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 6 * Complex.I ^ 4 +
    (29 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 6 * Complex.I ^ 2 + (-29 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 6 +
    (-149 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 5 * Complex.I ^ 3 +
    (149 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 5 * Complex.I +
    (-345 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 4 * Complex.I ^ 2 + (345 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 4 +
    (-435 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 3 * Complex.I +
    (-311 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 2) * Complex.I_sq +
    ((1 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 5 * Complex.I + (29 / 128 : ℂ) * ((√3 : ℝ) : ℂ) ^ 4 +
    (-73 / 64 : ℂ) * ((√3 : ℝ) : ℂ) ^ 3 * Complex.I + (-129 / 64 : ℂ) * ((√3 : ℝ) : ℂ) ^ 2 +
    (-3 / 128 : ℂ) * ((√3 : ℝ) : ℂ) * Complex.I + (-463 / 128 : ℂ)) * hs

lemma Δ_w_ne : («124.1-a2».map w).Δ ≠ 0 := by
  rw [Δ_w]
  intro h
  have h' := congrArg Complex.im h
  simp at h'

instance : («124.1-a2».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_ne⟩

/-- `Ω(E/K) = Ω_w = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 9.2107946514476859 = 18.421589302895372`; LMFDB gives
`18.421589302895372`. -/
example : «124.1-a2».complexGlobalPeriod w =
    2 * |((starRingEnd ℂ) («124.1-a2».map w).periodPair.ω₁ *
      («124.1-a2».map w).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

end «124.1-a2»

end «2.0.3.1»

/-! ### `2.0.3.1-283.1-a1` over `ℚ(√-3)`, rank `1` -/

namespace «2.0.3.1»

/-- LMFDB `2.0.3.1-283.1-a1`: `[a₁, a₂, a₃, a₄, a₆] = [1, w, w + 1, -1, -w]`, a global minimal
model, of conductor norm `283` and rank `1`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
17.499805378424805`. -/
def «283.1-a1» : QuadraticCurve := ⟨(1, 0), (0, 1), (1, 1), (-1, 0), (0, -1)⟩

namespace «283.1-a1»

/-- `Δ = 16 - 3 * √3 i ≠ 0`. -/
lemma Δ_w : («283.1-a1».map w).Δ = 16 - 3 * √3 * Complex.I := by
  have hs : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [QuadraticCurve.map, «283.1-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-1 / 2 : ℂ) * ((√3 : ℝ) : ℂ) ^ 5 * Complex.I ^ 3 +
    (1 / 2 : ℂ) * ((√3 : ℝ) : ℂ) ^ 5 * Complex.I +
    (-7 / 16 : ℂ) * ((√3 : ℝ) : ℂ) ^ 4 * Complex.I ^ 2 + (7 / 16 : ℂ) * ((√3 : ℝ) : ℂ) ^ 4 +
    (13 / 4 : ℂ) * ((√3 : ℝ) : ℂ) ^ 3 * Complex.I +
    (-67 / 8 : ℂ) * ((√3 : ℝ) : ℂ) ^ 2) * Complex.I_sq +
    ((-1 / 2 : ℂ) * ((√3 : ℝ) : ℂ) ^ 3 * Complex.I + (-7 / 16 : ℂ) * ((√3 : ℝ) : ℂ) ^ 2 +
    (-19 / 4 : ℂ) * ((√3 : ℝ) : ℂ) * Complex.I + (113 / 16 : ℂ)) * hs

lemma Δ_w_ne : («283.1-a1».map w).Δ ≠ 0 := by
  rw [Δ_w]
  intro h
  have h' := congrArg Complex.im h
  simp at h'

instance : («283.1-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_ne⟩

/-- `Ω(E/K) = Ω_w = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 8.7499026892124025 = 17.499805378424805`; LMFDB gives
`17.499805378424805`. -/
example : «283.1-a1».complexGlobalPeriod w =
    2 * |((starRingEnd ℂ) («283.1-a1».map w).periodPair.ω₁ *
      («283.1-a1».map w).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

end «283.1-a1»

end «2.0.3.1»

/-! ### `2.0.3.1-2809.1-a1` over `ℚ(√-3)`, rank `2` -/

namespace «2.0.3.1»

/-- LMFDB `2.0.3.1-2809.1-a1`: `[a₁, a₂, a₃, a₄, a₆] = [w + 1, 0, 1, -1, 0]`, a global minimal
model, of conductor norm `2809` and rank `2`. LMFDB: `Ω(E/K) ≈ 14.443472129715849`. -/
def «2809.1-a1» : QuadraticCurve := ⟨(1, 1), (0, 0), (1, 0), (-1, 0), (0, 0)⟩

namespace «2809.1-a1»

/-- `Δ = -53 ≠ 0`. -/
lemma Δ_w : («2809.1-a1».map w).Δ = -53 := by
  have hs : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  simp only [QuadraticCurve.map, «2809.1-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-1 / 32 : ℂ) * ((√3 : ℝ) : ℂ) ^ 5 * Complex.I ^ 3 +
    (1 / 32 : ℂ) * ((√3 : ℝ) : ℂ) ^ 5 * Complex.I +
    (-13 / 32 : ℂ) * ((√3 : ℝ) : ℂ) ^ 4 * Complex.I ^ 2 + (13 / 32 : ℂ) * ((√3 : ℝ) : ℂ) ^ 4 +
    (-31 / 16 : ℂ) * ((√3 : ℝ) : ℂ) ^ 3 * Complex.I +
    (57 / 16 : ℂ) * ((√3 : ℝ) : ℂ) ^ 2) * Complex.I_sq +
    ((-1 / 32 : ℂ) * ((√3 : ℝ) : ℂ) ^ 3 * Complex.I + (-13 / 32 : ℂ) * ((√3 : ℝ) : ℂ) ^ 2 +
    (59 / 32 : ℂ) * ((√3 : ℝ) : ℂ) * Complex.I + (-153 / 32 : ℂ)) * hs

lemma Δ_w_ne : («2809.1-a1».map w).Δ ≠ 0 := by
  rw [Δ_w]; norm_num

instance : («2809.1-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_ne⟩

/-- `Ω(E/K) = Ω_w = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 7.2217360648579243 = 14.443472129715849`; LMFDB gives
`14.443472129715849`. -/
example : «2809.1-a1».complexGlobalPeriod w =
    2 * |((starRingEnd ℂ) («2809.1-a1».map w).periodPair.ω₁ *
      («2809.1-a1».map w).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

end «2809.1-a1»

end «2.0.3.1»

/-! ### `2.2.5.1-36.1-a1` over `ℚ(√5)`, rank `0` -/

namespace «2.2.5.1»

/-- LMFDB `2.2.5.1-36.1-a1`: `[a₁, a₂, a₃, a₄, a₆] = [w + 1, w, w, 0, 0]`, a global minimal model,
of conductor norm `36` and rank `0`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
44.299621696875097`. -/
def «36.1-a1» : QuadraticCurve := ⟨(1, 1), (0, 1), (0, 1), (0, 0), (0, 0)⟩

namespace «36.1-a1»

/-- `Δ = -108 - 48 * √5 ≈ -215.33 < 0` at `w`. -/
lemma Δ_w : («36.1-a1».map w).Δ = -108 - 48 * √5 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «36.1-a1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-1 / 128 : ℝ) * √5 ^ 5 + (-29 / 128 : ℝ) * √5 ^ 4 + (-77 / 64 : ℝ) * √5 ^ 3 +
    (-245 / 64 : ℝ) * √5 ^ 2 + (-1205 / 128 : ℝ) * √5 + (-2761 / 128 : ℝ)) * hs

lemma Δ_w_neg : («36.1-a1».map w).Δ < 0 := by
  rw [Δ_w]
  have h₁ : (2.2360 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √5 < 2.2361 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («36.1-a1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_neg.ne⟩

/-- `E(ℝ)` is connected at `w`, so `Ω_w = ω₁ ≈ 5.2324632724`. -/
example : («36.1-a1».map w).realPeriodIntegral = («36.1-a1».map w).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg

/-- `Δ = -108 + 48 * √5 ≈ -0.66874 < 0` at `w'`. -/
lemma Δ_w' : («36.1-a1».map w').Δ = -108 + 48 * √5 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «36.1-a1», w', WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 / 128 : ℝ) * √5 ^ 5 + (-29 / 128 : ℝ) * √5 ^ 4 + (77 / 64 : ℝ) * √5 ^ 3 +
    (-245 / 64 : ℝ) * √5 ^ 2 + (1205 / 128 : ℝ) * √5 + (-2761 / 128 : ℝ)) * hs

lemma Δ_w'_neg : («36.1-a1».map w').Δ < 0 := by
  rw [Δ_w']
  have h₁ : (2.2360 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √5 < 2.2361 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («36.1-a1».map w').IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w'_neg.ne⟩

/-- `E(ℝ)` is connected at `w'`, so `Ω_w' = ω₁ ≈ 8.4663034197`. -/
example : («36.1-a1».map w').realPeriodIntegral = («36.1-a1».map w').leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg

/-- `Ω(E/K) = Ω_w Ω_w' ≈ 5.2324632724 × 8.4663034197 = 44.2996216969`; LMFDB gives
`44.299621696875097`. -/
example : «36.1-a1».realGlobalPeriod w w' =
    («36.1-a1».map w).leastRealPeriod * («36.1-a1».map w').leastRealPeriod := by
  rw [QuadraticCurve.realGlobalPeriod, realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg,
    realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg]

end «36.1-a1»

end «2.2.5.1»

/-! ### `2.2.5.1-199.1-c1` over `ℚ(√5)`, rank `1` -/

namespace «2.2.5.1»

/-- LMFDB `2.2.5.1-199.1-c1`: `[a₁, a₂, a₃, a₄, a₆] = [0, w + 1, 1, w, 0]`, a global minimal model,
of conductor norm `199` and rank `1`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
42.895444109769151`. -/
def «199.1-c1» : QuadraticCurve := ⟨(0, 0), (1, 1), (1, 0), (0, 1), (0, 0)⟩

namespace «199.1-c1»

/-- `Δ = -11 + 8 * √5 ≈ 6.8885 > 0` at `w`. -/
lemma Δ_w : («199.1-c1».map w).Δ = -11 + 8 * √5 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «199.1-c1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℝ) * √5 ^ 2 + (-2 : ℝ) * √5 + (3 : ℝ)) * hs

lemma Δ_w_pos : 0 < («199.1-c1».map w).Δ := by
  rw [Δ_w]
  have h₁ : (2.2360 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √5 < 2.2361 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («199.1-c1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_pos.ne'⟩

/-- `E(ℝ)` has two components at `w`, so `Ω_w = 2ω₁ ≈ 2 × 3.5348927466 = 7.0697854932`. -/
example : («199.1-c1».map w).realPeriodIntegral =
    2 * («199.1-c1».map w).leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_w_pos

/-- `Δ = -11 - 8 * √5 ≈ -28.889 < 0` at `w'`. -/
lemma Δ_w' : («199.1-c1».map w').Δ = -11 - 8 * √5 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «199.1-c1», w', WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℝ) * √5 ^ 2 + (2 : ℝ) * √5 + (3 : ℝ)) * hs

lemma Δ_w'_neg : («199.1-c1».map w').Δ < 0 := by
  rw [Δ_w']
  have h₁ : (2.2360 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √5 < 2.2361 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («199.1-c1».map w').IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w'_neg.ne⟩

/-- `E(ℝ)` is connected at `w'`, so `Ω_w' = ω₁ ≈ 6.0674321946`. -/
example : («199.1-c1».map w').realPeriodIntegral = («199.1-c1».map w').leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg

/-- `Ω(E/K) = Ω_w Ω_w' ≈ 7.0697854932 × 6.0674321946 = 42.8954441098`; LMFDB gives
`42.895444109769151`. -/
example : «199.1-c1».realGlobalPeriod w w' =
    (2 * («199.1-c1».map w).leastRealPeriod) * («199.1-c1».map w').leastRealPeriod := by
  rw [QuadraticCurve.realGlobalPeriod, realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_w_pos,
    realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg]

end «199.1-c1»

end «2.2.5.1»

/-! ### `2.2.5.1-1831.1-c1` over `ℚ(√5)`, rank `2` -/

namespace «2.2.5.1»

/-- LMFDB `2.2.5.1-1831.1-c1`: `[a₁, a₂, a₃, a₄, a₆] = [0, w, 1, -w - 1, 0]`, a global minimal
model, of conductor norm `1831` and rank `2`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
37.781912518434661`. -/
def «1831.1-c1» : QuadraticCurve := ⟨(0, 0), (0, 1), (1, 0), (-1, -1), (0, 0)⟩

namespace «1831.1-c1»

/-- `Δ = 517 + 232 * √5 ≈ 1035.8 > 0` at `w`. -/
lemma Δ_w : («1831.1-c1».map w).Δ = 517 + 232 * √5 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «1831.1-c1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℝ) * √5 ^ 2 + (14 : ℝ) * √5 + (75 : ℝ)) * hs

lemma Δ_w_pos : 0 < («1831.1-c1».map w).Δ := by
  rw [Δ_w]
  have h₁ : (2.2360 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √5 < 2.2361 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («1831.1-c1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_pos.ne'⟩

/-- `E(ℝ)` has two components at `w`, so `Ω_w = 2ω₁ ≈ 2 × 2.3227628593 = 4.6455257186`. -/
example : («1831.1-c1».map w).realPeriodIntegral =
    2 * («1831.1-c1».map w).leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_w_pos

/-- `Δ = 517 - 232 * √5 ≈ -1.7678 < 0` at `w'`. -/
lemma Δ_w' : («1831.1-c1».map w').Δ = 517 - 232 * √5 := by
  have hs : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «1831.1-c1», w', WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℝ) * √5 ^ 2 + (-14 : ℝ) * √5 + (75 : ℝ)) * hs

lemma Δ_w'_neg : («1831.1-c1».map w').Δ < 0 := by
  rw [Δ_w']
  have h₁ : (2.2360 : ℝ) < √5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √5 < 2.2361 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («1831.1-c1».map w').IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w'_neg.ne⟩

/-- `E(ℝ)` is connected at `w'`, so `Ω_w' = ω₁ ≈ 8.1329681088`. -/
example : («1831.1-c1».map w').realPeriodIntegral = («1831.1-c1».map w').leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg

/-- `Ω(E/K) = Ω_w Ω_w' ≈ 4.6455257186 × 8.1329681088 = 37.7819125184`; LMFDB gives
`37.781912518434661`. -/
example : «1831.1-c1».realGlobalPeriod w w' =
    (2 * («1831.1-c1».map w).leastRealPeriod) * («1831.1-c1».map w').leastRealPeriod := by
  rw [QuadraticCurve.realGlobalPeriod, realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_w_pos,
    realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg]

end «1831.1-c1»

end «2.2.5.1»

/-! ### `2.2.8.1-119.1-c1` over `ℚ(√2)`, rank `1` -/

namespace «2.2.8.1»

/-- LMFDB `2.2.8.1-119.1-c1`: `[a₁, a₂, a₃, a₄, a₆] = [w, -w - 1, 1, -w, 0]`, a global minimal
model, of conductor norm `119` and rank `1`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
20.018521488357718`. -/
def «119.1-c1» : QuadraticCurve := ⟨(0, 1), (-1, -1), (1, 0), (0, -1), (0, 0)⟩

namespace «119.1-c1»

/-- `Δ = 113 + 86 * √2 ≈ 234.62 > 0` at `w`. -/
lemma Δ_w : («119.1-c1».map w).Δ = 113 + 86 * √2 := by
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «119.1-c1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℝ) * √2 ^ 3 + (-7 : ℝ) * √2 ^ 2 + (1 : ℝ) * √2 + (62 : ℝ)) * hs

lemma Δ_w_pos : 0 < («119.1-c1».map w).Δ := by
  rw [Δ_w]
  have h₁ : (1.4142 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √2 < 1.4143 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («119.1-c1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_pos.ne'⟩

/-- `E(ℝ)` has two components at `w`, so `Ω_w = 2ω₁ ≈ 2 × 2.0717591743 = 4.1435183487`. -/
example : («119.1-c1».map w).realPeriodIntegral =
    2 * («119.1-c1».map w).leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_w_pos

/-- `Δ = 113 - 86 * √2 ≈ -8.6224 < 0` at `w'`. -/
lemma Δ_w' : («119.1-c1».map w').Δ = 113 - 86 * √2 := by
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «119.1-c1», w', WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-1 : ℝ) * √2 ^ 3 + (-7 : ℝ) * √2 ^ 2 + (-1 : ℝ) * √2 + (62 : ℝ)) * hs

lemma Δ_w'_neg : («119.1-c1».map w').Δ < 0 := by
  rw [Δ_w']
  have h₁ : (1.4142 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √2 < 1.4143 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («119.1-c1».map w').IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w'_neg.ne⟩

/-- `E(ℝ)` is connected at `w'`, so `Ω_w' = ω₁ ≈ 4.831285831`. -/
example : («119.1-c1».map w').realPeriodIntegral = («119.1-c1».map w').leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg

/-- `Ω(E/K) = Ω_w Ω_w' ≈ 4.1435183487 × 4.831285831 = 20.0185214884`; LMFDB gives
`20.018521488357718`. -/
example : «119.1-c1».realGlobalPeriod w w' =
    (2 * («119.1-c1».map w).leastRealPeriod) * («119.1-c1».map w').leastRealPeriod := by
  rw [QuadraticCurve.realGlobalPeriod, realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_w_pos,
    realPeriodIntegral_eq_leastRealPeriod _ Δ_w'_neg]

end «119.1-c1»

end «2.2.8.1»

/-! ### `2.2.8.1-1031.1-b1` over `ℚ(√2)`, rank `2` -/

namespace «2.2.8.1»

/-- LMFDB `2.2.8.1-1031.1-b1`: `[a₁, a₂, a₃, a₄, a₆] = [0, w, w + 1, -w - 1, 0]`, a global minimal
model, of conductor norm `1031` and rank `2`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
36.842709403669651`. -/
def «1031.1-b1» : QuadraticCurve := ⟨(0, 0), (0, 1), (1, 1), (-1, -1), (0, 0)⟩

namespace «1031.1-b1»

/-- `Δ = -763 - 540 * √2 ≈ -1526.7 < 0` at `w`. -/
lemma Δ_w : («1031.1-b1».map w).Δ = -763 - 540 * √2 := by
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «1031.1-b1», w, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-16 : ℝ) * √2 ^ 3 + (-115 : ℝ) * √2 ^ 2 + (-276 : ℝ) * √2 + (-400 : ℝ)) * hs

lemma Δ_w_neg : («1031.1-b1».map w).Δ < 0 := by
  rw [Δ_w]
  have h₁ : (1.4142 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √2 < 1.4143 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («1031.1-b1».map w).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w_neg.ne⟩

/-- `E(ℝ)` is connected at `w`, so `Ω_w = ω₁ ≈ 4.4504769245`. -/
example : («1031.1-b1».map w).realPeriodIntegral = («1031.1-b1».map w).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg

/-- `Δ = -763 + 540 * √2 ≈ 0.67532 > 0` at `w'`. -/
lemma Δ_w' : («1031.1-b1».map w').Δ = -763 + 540 * √2 := by
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [QuadraticCurve.map, «1031.1-b1», w', WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((16 : ℝ) * √2 ^ 3 + (-115 : ℝ) * √2 ^ 2 + (276 : ℝ) * √2 + (-400 : ℝ)) * hs

lemma Δ_w'_pos : 0 < («1031.1-b1».map w').Δ := by
  rw [Δ_w']
  have h₁ : (1.4142 : ℝ) < √2 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h₂ : √2 < 1.4143 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  linarith

instance : («1031.1-b1».map w').IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_w'_pos.ne'⟩

/-- `E(ℝ)` has two components at `w'`, so `Ω_w' = 2ω₁ ≈ 2 × 4.1391866567 = 8.2783733133`. -/
example : («1031.1-b1».map w').realPeriodIntegral =
    2 * («1031.1-b1».map w').leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_w'_pos

/-- `Ω(E/K) = Ω_w Ω_w' ≈ 4.4504769245 × 8.2783733133 = 36.8427094037`; LMFDB gives
`36.842709403669651`. -/
example : «1031.1-b1».realGlobalPeriod w w' =
    («1031.1-b1».map w).leastRealPeriod * (2 * («1031.1-b1».map w').leastRealPeriod) := by
  rw [QuadraticCurve.realGlobalPeriod, realPeriodIntegral_eq_leastRealPeriod _ Δ_w_neg,
    realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_w'_pos]

end «1031.1-b1»

end «2.2.8.1»

/-! ### The complex place of `3.1.23.1` -/

namespace «3.1.23.1»

lemma σ_re : σ.re = (1 - ρ) / 2 := by simp [σ]

lemma σ_im : σ.im = s / 2 := by simp [σ]

/-- An element `A + Bσ + Cσ²` of `ℚ(σ) = σ(K)` with real `A, B, C` is nonzero as soon as its
imaginary part `(s/2)(B + C(1 - ρ))` is. -/
lemma ne_zero_of_im_ne_zero {z : ℂ} (A B C : ℝ) (hz : z = A + B * σ + C * σ ^ 2)
    (h : B + C * (1 - ρ) ≠ 0) : z ≠ 0 := by
  rintro rfl
  have him := congrArg Complex.im hz
  simp only [Complex.zero_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    sq, σ_re, σ_im] at him
  have : s * (B + C * (1 - ρ)) = 0 := by linarith
  exact h ((mul_eq_zero.1 this).resolve_left s_pos.ne')

end «3.1.23.1»

/-! ### `3.1.23.1-107.1-A1` over the cubic field of discriminant `-23`, rank `0` -/

namespace «3.1.23.1»

/-- LMFDB `3.1.23.1-107.1-A1`: `[a₁, a₂, a₃, a₄, a₆] = [0, w² + w - 1, w² + 1, w² - w - 1, -w²]`, a
global minimal model, of conductor norm `107` and rank `0`, not a base change from `ℚ`. LMFDB:
`Ω(E/K) ≈ 144.23368496198089`. -/
def «107.1-A1» : CubicCurve :=
  ⟨(0, 0, 0), (-1, 1, 1), (1, 0, 1), (-1, -1, 1), (0, 0, -1)⟩

namespace «107.1-A1»

/-- `Δ = -7 - 5 * ρ + 4 * ρ ^ 2 ≈ -0.94625 < 0` at the real place. -/
lemma Δ_ρ : («107.1-A1».map ρ).Δ = -7 - 5 * ρ + 4 * ρ ^ 2 := by
  simp only [CubicCurve.map, «107.1-A1», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-16 : ℝ) * ρ ^ 7 + (-64 : ℝ) * ρ ^ 6 + (29 : ℝ) * ρ ^ 5 + (221 : ℝ) * ρ ^ 4 +
    (-143 : ℝ) * ρ ^ 3 + (-236 : ℝ) * ρ ^ 2 + (149 : ℝ) * ρ + (148 : ℝ)) * ρ_spec.2

lemma Δ_ρ_neg : («107.1-A1».map ρ).Δ < 0 := by
  rw [Δ_ρ]
  have h₁ : (-0.7549 : ℝ) < ρ := lt_ρ (by norm_num) (by norm_num)
  have h₂ : ρ < -0.7548 := ρ_lt (by norm_num)
  nlinarith [mul_pos (sub_pos.2 h₁) (sub_pos.2 h₂), sq_nonneg (ρ + 0.75485)]

instance : («107.1-A1».map ρ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ_neg.ne⟩

/-- `E(ℝ)` is connected at `ρ`, so `Ω_ρ = ω₁ ≈ 7.7676611671`. -/
example : («107.1-A1».map ρ).realPeriodIntegral = («107.1-A1».map ρ).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ_neg

/-- `Δ = -7 - 5 * σ + 4 * σ ^ 2 ≈ (-10.527 + 1.5043j) ≠ 0` at the complex place. -/
lemma Δ_σ : («107.1-A1».map σ).Δ = -7 - 5 * σ + 4 * σ ^ 2 := by
  simp only [CubicCurve.map, «107.1-A1», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-16 : ℂ) * σ ^ 7 + (-64 : ℂ) * σ ^ 6 + (29 : ℂ) * σ ^ 5 + (221 : ℂ) * σ ^ 4 +
    (-143 : ℂ) * σ ^ 3 + (-236 : ℂ) * σ ^ 2 + (149 : ℂ) * σ + (148 : ℂ)) * σ_cubic

lemma Δ_σ_ne : («107.1-A1».map σ).Δ ≠ 0 :=
  ne_zero_of_im_ne_zero (-7) (-5) (4) (by rw [Δ_σ]; push_cast; ring)
    (by intro h; linarith [ρ_gt, ρ_lt'])

instance : («107.1-A1».map σ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_σ_ne⟩

/-- `Ω_σ = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 9.2842415405997 = 18.568483081199`. -/
example : («107.1-A1».map σ).complexPeriodIntegral =
    2 * |((starRingEnd ℂ) («107.1-A1».map σ).periodPair.ω₁ *
      («107.1-A1».map σ).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

/-- `Ω(E/K) = Ω_ρ Ω_σ ≈ 7.76766116711 × 18.5684830812 = 144.23368496198`; LMFDB gives
`144.23368496198089`. -/
example : «107.1-A1».mixedGlobalPeriod ρ σ =
    («107.1-A1».map ρ).leastRealPeriod *
      (2 * |((starRingEnd ℂ) («107.1-A1».map σ).periodPair.ω₁ *
        («107.1-A1».map σ).periodPair.ω₂).im|) := by
  rw [CubicCurve.mixedGlobalPeriod, realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ_neg,
    complexPeriodIntegral_eq_two_mul_abs_im]

end «107.1-A1»

end «3.1.23.1»

/-! ### `3.1.23.1-719.3-A1` over the cubic field of discriminant `-23`, rank `1` -/

namespace «3.1.23.1»

/-- LMFDB `3.1.23.1-719.3-A1`: `[a₁, a₂, a₃, a₄, a₆] = [w² + w, w² + w, w + 1, -2w - 2, -w² - w]`, a
global minimal model, of conductor norm `719` and rank `1`, not a base change from `ℚ`. LMFDB:
`Ω(E/K) ≈ 135.92435690010297`. -/
def «719.3-A1» : CubicCurve :=
  ⟨(0, 1, 1), (0, 1, 1), (1, 1, 0), (-2, -2, 0), (0, -1, -1)⟩

namespace «719.3-A1»

/-- `Δ = -11 - 5 * ρ + 7 * ρ ^ 2 ≈ -3.2367 < 0` at the real place. -/
lemma Δ_ρ : («719.3-A1».map ρ).Δ = -11 - 5 * ρ + 7 * ρ ^ 2 := by
  simp only [CubicCurve.map, «719.3-A1», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℝ) * ρ ^ 11 + (8 : ℝ) * ρ ^ 10 + (38 : ℝ) * ρ ^ 9 + (123 : ℝ) * ρ ^ 8 +
    (295 : ℝ) * ρ ^ 7 + (498 : ℝ) * ρ ^ 6 + (511 : ℝ) * ρ ^ 5 + (233 : ℝ) * ρ ^ 4 +
    (94 : ℝ) * ρ ^ 3 + (703 : ℝ) * ρ ^ 2 + (1121 : ℝ) * ρ + (496 : ℝ)) * ρ_spec.2

lemma Δ_ρ_neg : («719.3-A1».map ρ).Δ < 0 := by
  rw [Δ_ρ]
  have h₁ : (-0.7549 : ℝ) < ρ := lt_ρ (by norm_num) (by norm_num)
  have h₂ : ρ < -0.7548 := ρ_lt (by norm_num)
  nlinarith [mul_pos (sub_pos.2 h₁) (sub_pos.2 h₂), sq_nonneg (ρ + 0.75485)]

instance : («719.3-A1».map ρ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ_neg.ne⟩

/-- `E(ℝ)` is connected at `ρ`, so `Ω_ρ = ω₁ ≈ 7.627447259`. -/
example : («719.3-A1».map ρ).realPeriodIntegral = («719.3-A1».map ρ).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ_neg

/-- `Δ = -11 - 5 * σ + 7 * σ ^ 2 ≈ (-13.882 + 5.4257j) ≠ 0` at the complex place. -/
lemma Δ_σ : («719.3-A1».map σ).Δ = -11 - 5 * σ + 7 * σ ^ 2 := by
  simp only [CubicCurve.map, «719.3-A1», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℂ) * σ ^ 11 + (8 : ℂ) * σ ^ 10 + (38 : ℂ) * σ ^ 9 + (123 : ℂ) * σ ^ 8 +
    (295 : ℂ) * σ ^ 7 + (498 : ℂ) * σ ^ 6 + (511 : ℂ) * σ ^ 5 + (233 : ℂ) * σ ^ 4 +
    (94 : ℂ) * σ ^ 3 + (703 : ℂ) * σ ^ 2 + (1121 : ℂ) * σ + (496 : ℂ)) * σ_cubic

lemma Δ_σ_ne : («719.3-A1».map σ).Δ ≠ 0 :=
  ne_zero_of_im_ne_zero (-11) (-5) (7) (by rw [Δ_σ]; push_cast; ring)
    (by intro h; linarith [ρ_gt, ρ_lt'])

instance : («719.3-A1».map σ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_σ_ne⟩

/-- `Ω_σ = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 8.9102128330317 = 17.820425666063`. -/
example : («719.3-A1».map σ).complexPeriodIntegral =
    2 * |((starRingEnd ℂ) («719.3-A1».map σ).periodPair.ω₁ *
      («719.3-A1».map σ).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

/-- `Ω(E/K) = Ω_ρ Ω_σ ≈ 7.62744725896 × 17.8204256661 = 135.9243569001`; LMFDB gives
`135.92435690010297`. -/
example : «719.3-A1».mixedGlobalPeriod ρ σ =
    («719.3-A1».map ρ).leastRealPeriod *
      (2 * |((starRingEnd ℂ) («719.3-A1».map σ).periodPair.ω₁ *
        («719.3-A1».map σ).periodPair.ω₂).im|) := by
  rw [CubicCurve.mixedGlobalPeriod, realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ_neg,
    complexPeriodIntegral_eq_two_mul_abs_im]

end «719.3-A1»

end «3.1.23.1»

/-! ### `3.1.23.1-9173.1-A1` over the cubic field of discriminant `-23`, rank `2` -/

namespace «3.1.23.1»

/-- LMFDB `3.1.23.1-9173.1-A1`: `[a₁, a₂, a₃, a₄, a₆] = [w, -w - 1, w + 1, -w² + w, -w]`, a global
minimal model, of conductor norm `9173` and rank `2`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
111.48202230312048`. -/
def «9173.1-A1» : CubicCurve :=
  ⟨(0, 1, 0), (-1, -1, 0), (1, 1, 0), (0, 1, -1), (0, -1, 0)⟩

namespace «9173.1-A1»

/-- `Δ = -17 + 17 * ρ - 20 * ρ ^ 2 ≈ -41.23 < 0` at the real place. -/
lemma Δ_ρ : («9173.1-A1».map ρ).Δ = -17 + 17 * ρ - 20 * ρ ^ 2 := by
  simp only [CubicCurve.map, «9173.1-A1», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-1 : ℝ) * ρ + (6 : ℝ)) * ρ_spec.2

lemma Δ_ρ_neg : («9173.1-A1».map ρ).Δ < 0 := by
  rw [Δ_ρ]
  have h₁ : (-0.7549 : ℝ) < ρ := lt_ρ (by norm_num) (by norm_num)
  have h₂ : ρ < -0.7548 := ρ_lt (by norm_num)
  nlinarith [mul_pos (sub_pos.2 h₁) (sub_pos.2 h₂), sq_nonneg (ρ + 0.75485)]

instance : («9173.1-A1».map ρ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ_neg.ne⟩

/-- `E(ℝ)` is connected at `ρ`, so `Ω_ρ = ω₁ ≈ 6.2445845541`. -/
example : («9173.1-A1».map ρ).realPeriodIntegral = («9173.1-A1».map ρ).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ_neg

/-- `Δ = -17 + 17 * σ - 20 * σ ^ 2 ≈ (-6.3851 - 13.48j) ≠ 0` at the complex place. -/
lemma Δ_σ : («9173.1-A1».map σ).Δ = -17 + 17 * σ - 20 * σ ^ 2 := by
  simp only [CubicCurve.map, «9173.1-A1», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((-1 : ℂ) * σ + (6 : ℂ)) * σ_cubic

lemma Δ_σ_ne : («9173.1-A1».map σ).Δ ≠ 0 :=
  ne_zero_of_im_ne_zero (-17) (17) (-20) (by rw [Δ_σ]; push_cast; ring)
    (by intro h; linarith [ρ_gt, ρ_lt'])

instance : («9173.1-A1».map σ).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_σ_ne⟩

/-- `Ω_σ = 2 |Im(ω̄₁ ω₂)| ≈ 2 × 8.9262961640532 = 17.852592328106`. -/
example : («9173.1-A1».map σ).complexPeriodIntegral =
    2 * |((starRingEnd ℂ) («9173.1-A1».map σ).periodPair.ω₁ *
      («9173.1-A1».map σ).periodPair.ω₂).im| :=
  complexPeriodIntegral_eq_two_mul_abs_im _

/-- `Ω(E/K) = Ω_ρ Ω_σ ≈ 6.24458455412 × 17.8525923281 = 111.48202230312`; LMFDB gives
`111.48202230312048`. -/
example : «9173.1-A1».mixedGlobalPeriod ρ σ =
    («9173.1-A1».map ρ).leastRealPeriod *
      (2 * |((starRingEnd ℂ) («9173.1-A1».map σ).periodPair.ω₁ *
        («9173.1-A1».map σ).periodPair.ω₂).im|) := by
  rw [CubicCurve.mixedGlobalPeriod, realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ_neg,
    complexPeriodIntegral_eq_two_mul_abs_im]

end «9173.1-A1»

end «3.1.23.1»

/-! ### The totally real cubic field `3.3.49.1`

`K = ℚ(w)` with `w³ - w² - 2w + 1 = 0` is the maximal real subfield of `ℚ(ζ₇)`.
Its three real places send `w` to the roots `ρ₁ < ρ₂ < ρ₃` of `x³ - x² - 2x + 1`, located by the
intermediate value theorem. -/

namespace «3.3.49.1»

/-- `x³ - x² - 2x + 1` has a root in `[-1.2470, -1.2469]`, by the intermediate value theorem. -/
lemma exists_root_1 : ∃ x ∈ Set.Icc (-1.2470 : ℝ) (-1.2469), x ^ 3 - x ^ 2 - 2 * x + 1 = 0 := by
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (a := (-1.2470 : ℝ)) (b := (-1.2469)) (by norm_num)
    (f := fun x : ℝ ↦ x ^ 3 - x ^ 2 - 2 * x + 1) (by fun_prop)
    (show (0 : ℝ) ∈ Set.Icc ((-1.2470 : ℝ) ^ 3 - (-1.2470 : ℝ) ^ 2 - 2 * (-1.2470 : ℝ) + 1)
      ((-1.2469 : ℝ) ^ 3 - (-1.2469 : ℝ) ^ 2 - 2 * (-1.2469 : ℝ) + 1) by norm_num)
  exact ⟨x, hx, hfx⟩

/-- `w ↦ ρ₁ ≈ -1.246979604`, the first real place of `K`. -/
def ρ₁ : ℝ := Classical.choose exists_root_1

lemma ρ₁_spec : ρ₁ ∈ Set.Icc (-1.2470 : ℝ) (-1.2469) ∧ ρ₁ ^ 3 - ρ₁ ^ 2 - 2 * ρ₁ + 1 = 0 :=
  Classical.choose_spec exists_root_1

/-- `x³ - x² - 2x + 1` has a root in `[0.4450, 0.4451]`, by the intermediate value theorem. -/
lemma exists_root_2 : ∃ x ∈ Set.Icc (0.4450 : ℝ) (0.4451), x ^ 3 - x ^ 2 - 2 * x + 1 = 0 := by
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' (a := (0.4450 : ℝ)) (b := (0.4451)) (by norm_num)
    (f := fun x : ℝ ↦ x ^ 3 - x ^ 2 - 2 * x + 1) (by fun_prop)
    (show (0 : ℝ) ∈ Set.Icc ((0.4451 : ℝ) ^ 3 - (0.4451 : ℝ) ^ 2 - 2 * (0.4451 : ℝ) + 1)
      ((0.4450 : ℝ) ^ 3 - (0.4450 : ℝ) ^ 2 - 2 * (0.4450 : ℝ) + 1) by norm_num)
  exact ⟨x, hx, hfx⟩

/-- `w ↦ ρ₂ ≈ 0.4450418679`, the second real place of `K`. -/
def ρ₂ : ℝ := Classical.choose exists_root_2

lemma ρ₂_spec : ρ₂ ∈ Set.Icc (0.4450 : ℝ) (0.4451) ∧ ρ₂ ^ 3 - ρ₂ ^ 2 - 2 * ρ₂ + 1 = 0 :=
  Classical.choose_spec exists_root_2

/-- `x³ - x² - 2x + 1` has a root in `[1.8019, 1.8020]`, by the intermediate value theorem. -/
lemma exists_root_3 : ∃ x ∈ Set.Icc (1.8019 : ℝ) (1.8020), x ^ 3 - x ^ 2 - 2 * x + 1 = 0 := by
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (a := (1.8019 : ℝ)) (b := (1.8020)) (by norm_num)
    (f := fun x : ℝ ↦ x ^ 3 - x ^ 2 - 2 * x + 1) (by fun_prop)
    (show (0 : ℝ) ∈ Set.Icc ((1.8019 : ℝ) ^ 3 - (1.8019 : ℝ) ^ 2 - 2 * (1.8019 : ℝ) + 1)
      ((1.8020 : ℝ) ^ 3 - (1.8020 : ℝ) ^ 2 - 2 * (1.8020 : ℝ) + 1) by norm_num)
  exact ⟨x, hx, hfx⟩

/-- `w ↦ ρ₃ ≈ 1.801937736`, the third real place of `K`. -/
def ρ₃ : ℝ := Classical.choose exists_root_3

lemma ρ₃_spec : ρ₃ ∈ Set.Icc (1.8019 : ℝ) (1.8020) ∧ ρ₃ ^ 3 - ρ₃ ^ 2 - 2 * ρ₃ + 1 = 0 :=
  Classical.choose_spec exists_root_3

end «3.3.49.1»

/-! ### `3.3.49.1-41.2-a3` over `3.3.49.1`, rank `0` -/

namespace «3.3.49.1»

/-- LMFDB `3.3.49.1-41.2-a3`: `[a₁, a₂, a₃, a₄, a₆] = [1, w + 1, 1, w, 0]`, a global minimal model,
of conductor norm `41` and rank `0`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
339.45684154604091`. -/
def «41.2-a3» : CubicCurve :=
  ⟨(1, 0, 0), (1, 1, 0), (1, 0, 0), (0, 1, 0), (0, 0, 0)⟩

namespace «41.2-a3»

/-- `Δ = -7 + 6 * ρ₁ + 9 * ρ₁ ^ 2 ≈ -0.48725 < 0` at `ρ₁`. -/
lemma Δ_ρ₁ : («41.2-a3».map ρ₁).Δ = -7 + 6 * ρ₁ + 9 * ρ₁ ^ 2 := by
  simp only [CubicCurve.map, «41.2-a3», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((16 : ℝ) * ρ₁ + (-8 : ℝ)) * ρ₁_spec.2

lemma Δ_ρ₁_neg : («41.2-a3».map ρ₁).Δ < 0 := by
  obtain ⟨⟨h₁, h₂⟩, -⟩ := ρ₁_spec
  rw [Δ_ρ₁]
  nlinarith [mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₂), sq_nonneg (ρ₁ + 1.24695)]

instance : («41.2-a3».map ρ₁).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ₁_neg.ne⟩

/-- `E(ℝ)` is connected at `ρ₁`, so `Ω_ρ₁ = ω₁ ≈ 9.3648697299`. -/
example : («41.2-a3».map ρ₁).realPeriodIntegral = («41.2-a3».map ρ₁).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ₁_neg

/-- `Δ = -7 + 6 * ρ₂ + 9 * ρ₂ ^ 2 ≈ -2.5472 < 0` at `ρ₂`. -/
lemma Δ_ρ₂ : («41.2-a3».map ρ₂).Δ = -7 + 6 * ρ₂ + 9 * ρ₂ ^ 2 := by
  simp only [CubicCurve.map, «41.2-a3», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((16 : ℝ) * ρ₂ + (-8 : ℝ)) * ρ₂_spec.2

lemma Δ_ρ₂_neg : («41.2-a3».map ρ₂).Δ < 0 := by
  obtain ⟨⟨h₁, h₂⟩, -⟩ := ρ₂_spec
  rw [Δ_ρ₂]
  nlinarith [mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₂), sq_nonneg (ρ₂ - 0.44505)]

instance : («41.2-a3».map ρ₂).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ₂_neg.ne⟩

/-- `E(ℝ)` is connected at `ρ₂`, so `Ω_ρ₂ = ω₁ ≈ 6.4986639947`. -/
example : («41.2-a3».map ρ₂).realPeriodIntegral = («41.2-a3».map ρ₂).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ₂_neg

/-- `Δ = -7 + 6 * ρ₃ + 9 * ρ₃ ^ 2 ≈ 33.034 > 0` at `ρ₃`. -/
lemma Δ_ρ₃ : («41.2-a3».map ρ₃).Δ = -7 + 6 * ρ₃ + 9 * ρ₃ ^ 2 := by
  simp only [CubicCurve.map, «41.2-a3», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((16 : ℝ) * ρ₃ + (-8 : ℝ)) * ρ₃_spec.2

lemma Δ_ρ₃_pos : 0 < («41.2-a3».map ρ₃).Δ := by
  obtain ⟨⟨h₁, h₂⟩, -⟩ := ρ₃_spec
  rw [Δ_ρ₃]
  nlinarith [mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₂), sq_nonneg (ρ₃ - 1.80195)]

instance : («41.2-a3».map ρ₃).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ₃_pos.ne'⟩

/-- `E(ℝ)` has two components at `ρ₃`, so `Ω_ρ₃ = 2ω₁ ≈ 2 × 2.7888730592 = 5.5777461184`. -/
example : («41.2-a3».map ρ₃).realPeriodIntegral =
    2 * («41.2-a3».map ρ₃).leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_ρ₃_pos

/-- `Ω(E/K) = Ω_ρ₁ Ω_ρ₂ Ω_ρ₃ ≈ 9.3648697299 × 6.4986639947 × 5.5777461184 = 339.45684154604`; LMFDB
gives `339.45684154604091`. -/
example : «41.2-a3».realGlobalPeriod ρ₁ ρ₂ ρ₃ =
    («41.2-a3».map ρ₁).leastRealPeriod *
      («41.2-a3».map ρ₂).leastRealPeriod *
      (2 * («41.2-a3».map ρ₃).leastRealPeriod) := by
  rw [CubicCurve.realGlobalPeriod, realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ₁_neg,
    realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ₂_neg,
    realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_ρ₃_pos]

end «41.2-a3»

end «3.3.49.1»

/-! ### `3.3.49.1-377.4-c3` over `3.3.49.1`, rank `1` -/

namespace «3.3.49.1»

/-- LMFDB `3.3.49.1-377.4-c3`: `[a₁, a₂, a₃, a₄, a₆] = [w² + w - 1, -1, 1, 0, 0]`, a global minimal
model, of conductor norm `377` and rank `1`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
344.26478758311204`. -/
def «377.4-c3» : CubicCurve :=
  ⟨(-1, 1, 1), (-1, 0, 0), (1, 0, 0), (0, 0, 0), (0, 0, 0)⟩

namespace «377.4-c3»

/-- `Δ = -4 + 5 * ρ₁ + 13 * ρ₁ ^ 2 ≈ 9.9796 > 0` at `ρ₁`. -/
lemma Δ_ρ₁ : («377.4-c3».map ρ₁).Δ = -4 + 5 * ρ₁ + 13 * ρ₁ ^ 2 := by
  simp only [CubicCurve.map, «377.4-c3», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℝ) * ρ₁ ^ 5 + (5 : ℝ) * ρ₁ ^ 4 + (10 : ℝ) * ρ₁ ^ 3 + (14 : ℝ) * ρ₁ ^ 2 +
    (16 : ℝ) * ρ₁ + (21 : ℝ)) * ρ₁_spec.2

lemma Δ_ρ₁_pos : 0 < («377.4-c3».map ρ₁).Δ := by
  obtain ⟨⟨h₁, h₂⟩, -⟩ := ρ₁_spec
  rw [Δ_ρ₁]
  nlinarith [mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₂), sq_nonneg (ρ₁ + 1.24695)]

instance : («377.4-c3».map ρ₁).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ₁_pos.ne'⟩

/-- `E(ℝ)` has two components at `ρ₁`, so `Ω_ρ₁ = 2ω₁ ≈ 2 × 3.2856819088 = 6.5713638175`. -/
example : («377.4-c3».map ρ₁).realPeriodIntegral =
    2 * («377.4-c3».map ρ₁).leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_ρ₁_pos

/-- `Δ = -4 + 5 * ρ₂ + 13 * ρ₂ ^ 2 ≈ 0.80002 > 0` at `ρ₂`. -/
lemma Δ_ρ₂ : («377.4-c3».map ρ₂).Δ = -4 + 5 * ρ₂ + 13 * ρ₂ ^ 2 := by
  simp only [CubicCurve.map, «377.4-c3», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℝ) * ρ₂ ^ 5 + (5 : ℝ) * ρ₂ ^ 4 + (10 : ℝ) * ρ₂ ^ 3 + (14 : ℝ) * ρ₂ ^ 2 +
    (16 : ℝ) * ρ₂ + (21 : ℝ)) * ρ₂_spec.2

lemma Δ_ρ₂_pos : 0 < («377.4-c3».map ρ₂).Δ := by
  obtain ⟨⟨h₁, h₂⟩, -⟩ := ρ₂_spec
  rw [Δ_ρ₂]
  nlinarith [mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₂), sq_nonneg (ρ₂ - 0.44505)]

instance : («377.4-c3».map ρ₂).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ₂_pos.ne'⟩

/-- `E(ℝ)` has two components at `ρ₂`, so `Ω_ρ₂ = 2ω₁ ≈ 2 × 4.3988905362 = 8.7977810725`. -/
example : («377.4-c3».map ρ₂).realPeriodIntegral =
    2 * («377.4-c3».map ρ₂).leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_ρ₂_pos

/-- `Δ = -4 + 5 * ρ₃ + 13 * ρ₃ ^ 2 ≈ 47.22 > 0` at `ρ₃`. -/
lemma Δ_ρ₃ : («377.4-c3».map ρ₃).Δ = -4 + 5 * ρ₃ + 13 * ρ₃ ^ 2 := by
  simp only [CubicCurve.map, «377.4-c3», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℝ) * ρ₃ ^ 5 + (5 : ℝ) * ρ₃ ^ 4 + (10 : ℝ) * ρ₃ ^ 3 + (14 : ℝ) * ρ₃ ^ 2 +
    (16 : ℝ) * ρ₃ + (21 : ℝ)) * ρ₃_spec.2

lemma Δ_ρ₃_pos : 0 < («377.4-c3».map ρ₃).Δ := by
  obtain ⟨⟨h₁, h₂⟩, -⟩ := ρ₃_spec
  rw [Δ_ρ₃]
  nlinarith [mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₂), sq_nonneg (ρ₃ - 1.80195)]

instance : («377.4-c3».map ρ₃).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ₃_pos.ne'⟩

/-- `E(ℝ)` has two components at `ρ₃`, so `Ω_ρ₃ = 2ω₁ ≈ 2 × 2.9773777983 = 5.9547555967`. -/
example : («377.4-c3».map ρ₃).realPeriodIntegral =
    2 * («377.4-c3».map ρ₃).leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_ρ₃_pos

/-- `Ω(E/K) = Ω_ρ₁ Ω_ρ₂ Ω_ρ₃ ≈ 6.5713638175 × 8.7977810725 × 5.9547555967 = 344.26478758311`; LMFDB
gives `344.26478758311204`. -/
example : «377.4-c3».realGlobalPeriod ρ₁ ρ₂ ρ₃ =
    (2 * («377.4-c3».map ρ₁).leastRealPeriod) *
      (2 * («377.4-c3».map ρ₂).leastRealPeriod) *
      (2 * («377.4-c3».map ρ₃).leastRealPeriod) := by
  rw [CubicCurve.realGlobalPeriod, realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_ρ₁_pos,
    realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_ρ₂_pos,
    realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_ρ₃_pos]

end «377.4-c3»

end «3.3.49.1»

/-! ### The totally real cubic field `3.3.81.1`

`K = ℚ(w)` with `w³ - 3w - 1 = 0` is the maximal real subfield of `ℚ(ζ₉)`.
Its three real places send `w` to the roots `ρ₁ < ρ₂ < ρ₃` of `x³ - 3x - 1`, located by the
intermediate value theorem. -/

namespace «3.3.81.1»

/-- `x³ - 3x - 1` has a root in `[-1.5321, -1.5320]`, by the intermediate value theorem. -/
lemma exists_root_1 : ∃ x ∈ Set.Icc (-1.5321 : ℝ) (-1.5320), x ^ 3 - 3 * x - 1 = 0 := by
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (a := (-1.5321 : ℝ)) (b := (-1.5320)) (by norm_num)
    (f := fun x : ℝ ↦ x ^ 3 - 3 * x - 1) (by fun_prop)
    (show (0 : ℝ) ∈ Set.Icc ((-1.5321 : ℝ) ^ 3 - 3 * (-1.5321 : ℝ) - 1)
      ((-1.5320 : ℝ) ^ 3 - 3 * (-1.5320 : ℝ) - 1) by norm_num)
  exact ⟨x, hx, hfx⟩

/-- `w ↦ ρ₁ ≈ -1.532088886`, the first real place of `K`. -/
def ρ₁ : ℝ := Classical.choose exists_root_1

lemma ρ₁_spec : ρ₁ ∈ Set.Icc (-1.5321 : ℝ) (-1.5320) ∧ ρ₁ ^ 3 - 3 * ρ₁ - 1 = 0 :=
  Classical.choose_spec exists_root_1

/-- `x³ - 3x - 1` has a root in `[-0.3473, -0.3472]`, by the intermediate value theorem. -/
lemma exists_root_2 : ∃ x ∈ Set.Icc (-0.3473 : ℝ) (-0.3472), x ^ 3 - 3 * x - 1 = 0 := by
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc' (a := (-0.3473 : ℝ)) (b := (-0.3472)) (by norm_num)
    (f := fun x : ℝ ↦ x ^ 3 - 3 * x - 1) (by fun_prop)
    (show (0 : ℝ) ∈ Set.Icc ((-0.3472 : ℝ) ^ 3 - 3 * (-0.3472 : ℝ) - 1)
      ((-0.3473 : ℝ) ^ 3 - 3 * (-0.3473 : ℝ) - 1) by norm_num)
  exact ⟨x, hx, hfx⟩

/-- `w ↦ ρ₂ ≈ -0.3472963553`, the second real place of `K`. -/
def ρ₂ : ℝ := Classical.choose exists_root_2

lemma ρ₂_spec : ρ₂ ∈ Set.Icc (-0.3473 : ℝ) (-0.3472) ∧ ρ₂ ^ 3 - 3 * ρ₂ - 1 = 0 :=
  Classical.choose_spec exists_root_2

/-- `x³ - 3x - 1` has a root in `[1.8793, 1.8794]`, by the intermediate value theorem. -/
lemma exists_root_3 : ∃ x ∈ Set.Icc (1.8793 : ℝ) (1.8794), x ^ 3 - 3 * x - 1 = 0 := by
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (a := (1.8793 : ℝ)) (b := (1.8794)) (by norm_num)
    (f := fun x : ℝ ↦ x ^ 3 - 3 * x - 1) (by fun_prop)
    (show (0 : ℝ) ∈ Set.Icc ((1.8793 : ℝ) ^ 3 - 3 * (1.8793 : ℝ) - 1)
      ((1.8794 : ℝ) ^ 3 - 3 * (1.8794 : ℝ) - 1) by norm_num)
  exact ⟨x, hx, hfx⟩

/-- `w ↦ ρ₃ ≈ 1.879385242`, the third real place of `K`. -/
def ρ₃ : ℝ := Classical.choose exists_root_3

lemma ρ₃_spec : ρ₃ ∈ Set.Icc (1.8793 : ℝ) (1.8794) ∧ ρ₃ ^ 3 - 3 * ρ₃ - 1 = 0 :=
  Classical.choose_spec exists_root_3

end «3.3.81.1»

/-! ### `3.3.81.1-199.2-a1` over `3.3.81.1`, rank `1` -/

namespace «3.3.81.1»

/-- LMFDB `3.3.81.1-199.2-a1`: `[a₁, a₂, a₃, a₄, a₆] = [w² - 1, w + 1, w + 1, w, 0]`, a global
minimal model, of conductor norm `199` and rank `1`, not a base change from `ℚ`. LMFDB: `Ω(E/K) ≈
359.142964000285`. -/
def «199.2-a1» : CubicCurve :=
  ⟨(-1, 0, 1), (1, 1, 0), (1, 1, 0), (0, 1, 0), (0, 0, 0)⟩

namespace «199.2-a1»

/-- `Δ = -75 - 165 * ρ₁ + 109 * ρ₁ ^ 2 ≈ 433.65 > 0` at `ρ₁`. -/
lemma Δ_ρ₁ : («199.2-a1».map ρ₁).Δ = -75 - 165 * ρ₁ + 109 * ρ₁ ^ 2 := by
  simp only [CubicCurve.map, «199.2-a1», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℝ) * ρ₁ ^ 9 + (-4 : ℝ) * ρ₁ ^ 7 + (6 : ℝ) * ρ₁ ^ 6 + (16 : ℝ) * ρ₁ ^ 5 +
    (-40 : ℝ) * ρ₁ ^ 4 + (-52 : ℝ) * ρ₁ ^ 3 + (-8 : ℝ) * ρ₁ ^ 2 + (146 : ℝ) * ρ₁ +
    (14 : ℝ)) * ρ₁_spec.2

lemma Δ_ρ₁_pos : 0 < («199.2-a1».map ρ₁).Δ := by
  obtain ⟨⟨h₁, h₂⟩, -⟩ := ρ₁_spec
  rw [Δ_ρ₁]
  nlinarith [mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₂), sq_nonneg (ρ₁ + 1.53205)]

instance : («199.2-a1».map ρ₁).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ₁_pos.ne'⟩

/-- `E(ℝ)` has two components at `ρ₁`, so `Ω_ρ₁ = 2ω₁ ≈ 2 × 2.2418944947 = 4.4837889894`. -/
example : («199.2-a1».map ρ₁).realPeriodIntegral =
    2 * («199.2-a1».map ρ₁).leastRealPeriod :=
  realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_ρ₁_pos

/-- `Δ = -75 - 165 * ρ₂ + 109 * ρ₂ ^ 2 ≈ -4.5491 < 0` at `ρ₂`. -/
lemma Δ_ρ₂ : («199.2-a1».map ρ₂).Δ = -75 - 165 * ρ₂ + 109 * ρ₂ ^ 2 := by
  simp only [CubicCurve.map, «199.2-a1», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℝ) * ρ₂ ^ 9 + (-4 : ℝ) * ρ₂ ^ 7 + (6 : ℝ) * ρ₂ ^ 6 + (16 : ℝ) * ρ₂ ^ 5 +
    (-40 : ℝ) * ρ₂ ^ 4 + (-52 : ℝ) * ρ₂ ^ 3 + (-8 : ℝ) * ρ₂ ^ 2 + (146 : ℝ) * ρ₂ +
    (14 : ℝ)) * ρ₂_spec.2

lemma Δ_ρ₂_neg : («199.2-a1».map ρ₂).Δ < 0 := by
  obtain ⟨⟨h₁, h₂⟩, -⟩ := ρ₂_spec
  rw [Δ_ρ₂]
  nlinarith [mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₂), sq_nonneg (ρ₂ + 0.34725)]

instance : («199.2-a1».map ρ₂).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ₂_neg.ne⟩

/-- `E(ℝ)` is connected at `ρ₂`, so `Ω_ρ₂ = ω₁ ≈ 7.6255237323`. -/
example : («199.2-a1».map ρ₂).realPeriodIntegral = («199.2-a1».map ρ₂).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ₂_neg

/-- `Δ = -75 - 165 * ρ₃ + 109 * ρ₃ ^ 2 ≈ -0.10088 < 0` at `ρ₃`. -/
lemma Δ_ρ₃ : («199.2-a1».map ρ₃).Δ = -75 - 165 * ρ₃ + 109 * ρ₃ ^ 2 := by
  simp only [CubicCurve.map, «199.2-a1», WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  push_cast
  linear_combination ((1 : ℝ) * ρ₃ ^ 9 + (-4 : ℝ) * ρ₃ ^ 7 + (6 : ℝ) * ρ₃ ^ 6 + (16 : ℝ) * ρ₃ ^ 5 +
    (-40 : ℝ) * ρ₃ ^ 4 + (-52 : ℝ) * ρ₃ ^ 3 + (-8 : ℝ) * ρ₃ ^ 2 + (146 : ℝ) * ρ₃ +
    (14 : ℝ)) * ρ₃_spec.2

lemma Δ_ρ₃_neg : («199.2-a1».map ρ₃).Δ < 0 := by
  obtain ⟨⟨h₁, h₂⟩, -⟩ := ρ₃_spec
  rw [Δ_ρ₃]
  nlinarith [mul_nonneg (sub_nonneg.2 h₁) (sub_nonneg.2 h₂), sq_nonneg (ρ₃ - 1.87935)]

instance : («199.2-a1».map ρ₃).IsElliptic := ⟨isUnit_iff_ne_zero.mpr Δ_ρ₃_neg.ne⟩

/-- `E(ℝ)` is connected at `ρ₃`, so `Ω_ρ₃ = ω₁ ≈ 10.503946942`. -/
example : («199.2-a1».map ρ₃).realPeriodIntegral = («199.2-a1».map ρ₃).leastRealPeriod :=
  realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ₃_neg

/-- `Ω(E/K) = Ω_ρ₁ Ω_ρ₂ Ω_ρ₃ ≈ 4.4837889894 × 7.6255237323 × 10.503946942 = 359.14296400029`; LMFDB
gives `359.142964000285`. -/
example : «199.2-a1».realGlobalPeriod ρ₁ ρ₂ ρ₃ =
    (2 * («199.2-a1».map ρ₁).leastRealPeriod) *
      («199.2-a1».map ρ₂).leastRealPeriod *
      («199.2-a1».map ρ₃).leastRealPeriod := by
  rw [CubicCurve.realGlobalPeriod, realPeriodIntegral_eq_two_mul_leastRealPeriod _ Δ_ρ₁_pos,
    realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ₂_neg,
    realPeriodIntegral_eq_leastRealPeriod _ Δ_ρ₃_neg]

end «199.2-a1»

end «3.3.81.1»

end LMFDB

end
