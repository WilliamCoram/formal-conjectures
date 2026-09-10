# Development Plan: the period lattice of an elliptic curve over ℂ as integrals

Board: `.mathlib-quality/complex-period/` (this directory). The finished real-period board lives
in `.mathlib-quality/{plan,decomposition,tickets}.md` and is not touched. Prior-B2 log (shared):
`.mathlib-quality/b2_log.jsonl` (empty as of 2026-09-10). Branch: `periods`.

## Goal

```lean
/-- The integrals of the invariant differential dx/(2y + a₁x + a₃) along the C¹ loops on
E(ℂ) avoiding the point at infinity and the points of order two are exactly the elements of
the lattice with invariants g₂ = c₄/12, g₃ = c₆/216. -/
theorem WeierstrassCurve.integralPeriodLattice_eq (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    W.integralPeriodLattice = (W.periodPair.lattice : Set ℂ)
```
with
```lean
def WeierstrassCurve.integralPeriodLattice (W : WeierstrassCurve ℂ) : Set ℂ :=
  curveIntegralPeriods W.invariantDifferential W.affineNonTwoTorsion
def curveIntegralPeriods (ω : E → E →L[𝕜] F) (S : Set E) : Set F :=
  {w | ∃ (p : E) (γ : Path p p), ContDiffOn ℝ 1 γ.extend I ∧ range γ ⊆ S ∧ ∫ᶜ x in γ, ω x = w}
```
(`∫ᶜ` is Mathlib's `curveIntegral`). The statement is an equality of **sets**: the pair
`W.periodPair` is a `Classical.choose`d ℤ-basis, determined only up to `GL₂(ℤ)`, so no statement
about `ω₁`, `ω₂` individually is provable or wanted (see the conversation of 2026-09-10 and the
docstring of `ComplexPeriod.lean`). The corollary
`WeierstrassCurve.exists_curveIntegral_eq_of_mem_lattice` says every lattice element is a loop
integral, which is the precise form of "the two periods are integrals over two loops".

## References

| Tag | Reference | Used for |
|---|---|---|
| [LMFDB-PL] | LMFDB knowl `ec.q.period_lattice` (https://www.lmfdb.org/knowledge/show/ec.q.period_lattice) | definition of the period lattice as periods of `dx/(2y+a₁x+a₃)`; `ℂ/Λ ≅ E(ℂ)` via ℘ |
| [LMFDB-P] | LMFDB knowl `ec.period` | complex-place period is the covolume `2 Im(w̄₁w₂)` — why set equality is the right level |
| [DLMF] | DLMF §23.6(iv), eqs 23.6.34–23.6.36 (https://dlmf.nist.gov/23.6.iv) | periods as elliptic integrals; `w = ∫_z^∞ dt/√(4t³−g₂t−g₃)` inverts ℘ |
| [Pas2017] | G. Pastras, *Four Lectures on Weierstrass Elliptic Function…*, arXiv:1706.07371 (text extracted to the session tool-results dir, `pastras.txt`) | Thm 1.2 (Liouville), Thm 1.3 (roots = poles), eqs (1.30)–(1.32) (inverse of ℘ as the integral), (1.34)–(1.36) (half-periods), p. 14 "all other complex numbers appear twice" |
| [WW1927] | Whittaker–Watson, *A Course of Modern Analysis*, 4th ed., §20.12(IV), §20.13, footnote to §20.31 (public-domain OCR, `ww.txt`) | Liouville for elliptic functions; "℘(z) − ℘(y) … has only two irreducible zeros; and the points congruent to z = ±y therefore give all the zeros" |
| [Mil2006] | J. S. Milne, *Elliptic Curves*, 2006, Ch. III §§1–3 (https://www.jmilne.org/math/Books/ectext6.pdf, `milne.txt`) | Cor 2.2 (Liouville proof), Prop 3.7 (`ℂ/Λ → E(Λ)(ℂ)` isomorphism, "local isomorphism except at the four points") |
| [Sil2009] | Silverman, *AEC*, 2nd ed., III §1, VI §1, VI.3.6, VI.5.1 | statements only (not fetchable); change of variables `u = 1, r = −b₂/12, s = −a₁/2, t = −a₃/2` |
| project | `HalfPeriods.lean` (ODE-uniqueness route replacing the argument principle), `RealAxis.lean` (`integral_inv_sqrt_eq_half`), `Existence.lean` (`PeriodPair.weierstrassCurve`), `PeriodLattice.lean` (`periodPair`, `periodPair_g₂/g₃`) | the technique for the two API gaps is the project's own |
| LeanBridge | `LeanBridge/NonSlop/uniformisation.lean` (`weierstrassCurve_equation`, `toPoint`), `work/inverse.lean` docstring (surjectivity plan) | reference implementations of the point map; the surjectivity sketch |

**Source-faithfulness note.** The textbook proofs of the two API gaps (surjectivity of ℘;
`(℘, ℘')` injective mod Λ) go through the order-counting theorem for elliptic functions
([WW1927] §20.13, [Pas2017] Thm 1.3, [Mil2006] Prop 2.1(b)), i.e. the argument principle, which
Mathlib does not have. The project already replaced that tool once, in `HalfPeriods.lean`, by
ODE uniqueness + the identity theorem + a pole-order comparison, and documented the substitution
in that file's docstring. This plan reuses exactly that route; the *statements* are transcribed
from the sources, the *proof* of the counting step is the project's established substitute.
Surjectivity uses the sources' own Liouville argument verbatim ([Pas2017] Thm 1.2 proof,
[Mil2006] Cor 2.2 proof), which Mathlib supports directly.

## Mathlib inventory

| Concept | Mathlib status | Action |
|---|---|---|
| integral of a 1-form along a path | `curveIntegral`, `curveIntegralFun`, `CurveIntegrable`, `curveIntegral_symm/refl/trans`, `curveIntegral_eq_intervalIntegral_deriv`, `ContinuousOn.curveIntegrable_of_contDiffOn` (`Mathlib.MeasureTheory.Integral.CurveIntegral.Basic`) | USE; add affine change of variables (`Map.lean`) |
| set of periods of a 1-form | absent | DEFINE `curveIntegralPeriods` + API (`Periods.lean`) |
| invariant differential as a 1-form on the plane | absent (Mathlib has `WeierstrassCurve` and `Affine.Equation`, `Ψ₂Sq`, `C_Ψ₂Sq`) | DEFINE `invariantDifferential`, `affineNonTwoTorsion` |
| short model / change of variables | `WeierstrassCurve.VariableChange` exists on curves, not as a map on points; `short` in project `Existence.lean` (ℂ only) | DEFINE `shortModel`, `toShortModel`, `toShortModelLinear` over a field; relate to `PeriodPair.weierstrassCurve` |
| ℘, ℘', `derivWeierstrassP_sq`, periodicity, parity, `order_weierstrassP`, `analyticOnNhd_*`, `compl_lattice_sdiff_singleton_mem_nhds`, `ω₁_div_two_notMem_lattice` | `Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass` | USE |
| ℘ surjective; `(℘,℘')` injective mod Λ; periods of ℘ = Λ | absent | API GAPS AG1, AG2 (own files) |
| inverse function theorem (1-dim) | `HasStrictDerivAt.localInverse`, `eventually_left/right_inverse`, `to_localInverse`, `to_local_left_inverse`; `HasStrictFDerivAt.localInverse_continuousAt`; `AnalyticAt.hasStrictDerivAt` | USE |
| continuous induction on `[0,1]` | `IsClosed.Icc_subset_of_forall_mem_nhdsWithin` | USE |
| equal derivative ⟹ equal | `eq_of_derivWithin_eq` | USE |
| Liouville; removable singularity; compact range of periodic maps | `Differentiable.apply_eq_apply_of_bounded`; `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`; `IsZLattice.isCompact_range_of_periodic` | USE |
| ODE uniqueness | `ODE_solution_unique_of_eventually` (already used in `HalfPeriods.lean`) | USE |
| point outside a countable set | `Set.Countable.dense_compl`, `Cardinal.not_countable_real`, `not_countable_complex` | USE |
| sign-locking of a continuous square root | absent | DEFINE general lemma `eventually_eq_of_sq_eq_sq` (`Topology/Algebra/Field.lean`) |

## File structure (all under `FormalConjecturesForMathlib/`, all written as `sorry` skeletons, `lake build` clean on 2026-09-10)

```
MeasureTheory/Integral/CurveIntegral/Map.lean          curve integral along x ↦ A x + c
MeasureTheory/Integral/CurveIntegral/Periods.lean      curveIntegralPeriods + API + affine image
MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean   FTC on Icc (added during
                                                       execution as sub-ticket T027a)
Topology/Algebra/Field.lean                            eventually_eq_of_sq_eq_sq
AlgebraicGeometry/EllipticCurve/InvariantDifferential.lean   ω, affineNonTwoTorsion, shortModel, toShortModel(Linear), pullback identity, eval_Ψ₂Sq_sub (general)
AlgebraicGeometry/EllipticCurve/IntegralPeriodLattice.lean   integralPeriodLattice (ℂ), API, invariance under toShortModel
Analysis/SpecialFunctions/Elliptic/Weierstrass/Surjective.lean   AG1: ℘ surjective
Analysis/SpecialFunctions/Elliptic/Weierstrass/Injective.lean    AG2: (℘,℘') injective mod Λ, periods of ℘
Analysis/SpecialFunctions/Elliptic/Weierstrass/Lift.lean         weierstrassPoint, lift, the elliptic integral inverts ℘ along paths
Analysis/SpecialFunctions/Elliptic/Weierstrass/Periods.lean      weierstrassLoop; integralPeriodLattice_weierstrassCurve
AlgebraicGeometry/EllipticCurve/ComplexPeriod.lean               integralPeriodLattice_eq (MILESTONE)
```
Refactors already done in the skeleton commit: `periodPair_g₂`, `periodPair_g₃` moved from
`RealPeriod.lean` to `PeriodLattice.lean`; `eval_Ψ₂Sq_sub` generalised from ℝ to any field with
`NeZero 2`, `NeZero 3` (now a sorried leaf in `InvariantDifferential.lean`; `RealPeriod.lean`
imports it and still builds).

## Dependency graph

(12 files, 1620 lines, 76 declarations; all proved, `lake build` clean, 2026-09-10.)

```
Field.lean (sign-lock) ─────────────────────────────┐
FundThmCalculus.lean (FTC on Icc) ──→ Lift.lean      │
Map.lean ──→ Periods.lean ─────────────┐             │
InvariantDifferential.lean ──→ IntegralPeriodLattice.lean ──→ Lift.lean ──→ Periods(W).lean ──→ ComplexPeriod.lean
Uniqueness.lean ──→ Surjective.lean (AG1) ──────────────────────↗            ↗
HalfPeriods.lean ──→ Injective.lean (AG2) ───────────────────────────────────┘
Existence.lean (weierstrassCurve) ──→ Lift.lean;  PeriodLattice.lean ──→ ComplexPeriod.lean
```
Parallel fronts at the start: {Map, Field, InvariantDifferential, Surjective, Injective} are
mutually independent (5 workers). `Lift` needs InvariantDifferential + IntegralPeriodLattice +
Surjective (only `tendsto_weierstrassP_cobounded`) + Field. `Periods(W)` needs Lift + Injective +
Surjective. `ComplexPeriod` needs everything.

## Generality decisions

- `curveIntegralPeriods`: any `RCLike 𝕜`, normed spaces `E`, `F` with `NormedSpace ℝ E` (as in
  Mathlib's `curveIntegral`); loops are `C¹` on `[0,1]` via `Path.extend` (Mathlib's convention).
  Concatenation is not provided: the concatenation of `C¹` loops is only piecewise `C¹`, and
  Mathlib has no piecewise-`C¹` predicate; the theorem does not need it.
- Invariant differential and change of variables: over any `NontriviallyNormedField F`
  (the 1-form) and any `Field F` (the algebra), with `[NeZero (2 : F)]`, `[NeZero (3 : F)]`
  exactly where division by 2, 12, 48, 216, 864 is used. `affineNonTwoTorsion` over any
  `CommRing`.
- The ℘-side statements are for an arbitrary `PeriodPair`; nothing assumes reality.
- Loops avoid `O` and the 2-torsion points: `x` is a local coordinate there, so `ω = dx/(2y+…)`
  literally. The theorem shows nothing is lost.

## Follow-ups surfaced by this development (not on this board — user decides)

1. **An intrinsic lattice-side real period.** When `nrRealComponents` was removed on 2026-09-10
   the lattice side kept only `leastRealPeriod = Ω₀`, and the BSD factor of 2 was left entirely
   to the integral side. With `PeriodPair.weierstrassP_eq_iff` now proved, the intrinsic form
   becomes reachable: for a real lattice, `2·Re ω ∈ Λ ∩ ℝ = Ω₀ℤ`, so `Re Λ` is `Ω₀ℤ`
   (rectangular, `Δ > 0`) or `(Ω₀/2)ℤ` (rhombic, `Δ < 0`), and in both cases

       BSD real period = least positive element of `{ω + conj ω : ω ∈ Λ}` = 2 · (least positive
       real part of a lattice element).

   The missing step is "Λ rectangular ⟺ Δ > 0", whose classical proof goes through the ℘-values
   at the three half-periods being real and distinct — and the distinctness is exactly
   `weierstrassP_eq_iff`. That would remove the last vestige of the unproved component count
   from the real-period development.

2. **`HalfPeriods` as corollaries of `Injective`.** `HalfPeriods.eventually_weierstrassP_add_eq_sub`,
   `weierstrassP_add_eq_sub_of_derivWeierstrassP_eq_zero` and
   `two_mul_mem_lattice_of_derivWeierstrassP_eq_zero` are the `(a, b) = (z₀, −z₀)` and `c = 2z₀`
   specialisations of `Injective.lean`'s three lemmas. Re-deriving them would remove ~110 lines,
   but `HalfPeriods.lean` is imported by the real-period development, so the change should be
   made deliberately rather than as part of a cleanup pass.

3. **Upstreaming.** `PeriodPair.exists_weierstrassP_eq`, `PeriodPair.weierstrassP_eq_iff` and
   `intervalIntegral.integral_hasDerivWithinAt_Icc` are the three declarations here that are
   mathlib-shaped and mathlib-missing. The first also closes the single remaining `sorry` of the
   LeanBridge uniformisation chain (`LeanBridge/LeanBridge/work/inverse.lean:72`), which is on
   mathlib v4.31.0 — the statement transfers verbatim, the proof needs porting.
