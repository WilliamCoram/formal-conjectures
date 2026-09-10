# Ticket Board: the period lattice of an elliptic curve over ℂ as integrals

Project root: `/Users/nkw24xru/Desktop/Lean/formal-conjectures` (branch `periods`).
Board: `.mathlib-quality/complex-period/` — plan: `plan.md`; decomposition with verbatim source
quotes, discharge citations and attack logs: `decomposition.md` (ticket sketches below refer to
its nodes, e.g. "L4.3", and quotes "Q6"). Build rule: build only the touched module, e.g.
`lake build FormalConjecturesForMathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass.Lift`
(never the whole library). Everything lives in `FormalConjecturesForMathlib`, a default target
under the module system (`module`, `public import`, `@[expose] public noncomputable section`); a
`sorry` is a build warning. Prior-B2 log (shared, empty): `.mathlib-quality/b2_log.jsonl`.

File abbreviations: M = `MeasureTheory/Integral/CurveIntegral/Map.lean`; P =
`MeasureTheory/Integral/CurveIntegral/Periods.lean`; T = `Topology/Algebra/Field.lean`; ID =
`AlgebraicGeometry/EllipticCurve/InvariantDifferential.lean`; IPL =
`AlgebraicGeometry/EllipticCurve/IntegralPeriodLattice.lean`; S, J, L, WP =
`Analysis/SpecialFunctions/Elliptic/Weierstrass/{Surjective,Injective,Lift,Periods}.lean`; CP =
`AlgebraicGeometry/EllipticCurve/ComplexPeriod.lean` (all under `FormalConjecturesForMathlib/`).

Notation: `℘[L]` = `PeriodPair.weierstrassP L`, `℘'[L]` = `PeriodPair.derivWeierstrassP L`
(scoped notation from Mathlib's `Weierstrass.lean`, needs `open PeriodPair`? — no, it is
available after `namespace PeriodPair`). `I` = `unitInterval` (`open scoped unitInterval`).
`∫ᶜ x in γ, ω x` = `curveIntegral ω γ`.

Sources (full citations in `plan.md`): [LMFDB-PL], [LMFDB-P], [DLMF], [Pas2017], [WW1927],
[Mil2006], [Sil2009]; local text files of the fetched references are in the session's
tool-results directory (`pastras.txt`, `ww.txt`, `milne.txt`).

## Status 2026-09-10

**All 41 proof/definition tickets are done** (T001–T040 plus the spawned T027a), including the
milestone T039 `WeierstrassCurve.integralPeriodLattice_eq`. 1620 lines of new Lean across 11
files; `lake build FormalConjecturesForMathlib` is clean with **no errors, no warnings and no
sorries**; `#print axioms` on the milestone, on `PeriodPair.exists_weierstrassP_eq` and on
`PeriodPair.sub_mem_lattice_of_weierstrassP_eq_of_derivWeierstrassP_eq` shows only `propext`,
`Classical.choice`, `Quot.sound`. Committed as `3f2e4b6a`. The four files under review on
PR #5370 were not touched.

One sub-ticket was spawned during execution: **T027a**, the fundamental theorem of calculus on a
closed interval — Mathlib's `intervalIntegral.integral_hasDerivWithinAt_right` is gated on the
`FTCFilter` class, which has instances only for `pure`, `𝓝`, `𝓝[≤]`, `𝓝[≥]`, and none for `Icc`.

Remaining: the `CLEANUP-*` tickets (dispatched to `/cleanup` subagents), then `CLEANUP-ALL-1`
and `CLEANUP-FINAL`.

## Summary
- Total: 59 tickets = 40 proof/definition tickets + 17 per-file cleanups + CLEANUP-ALL-1 +
  CLEANUP-FINAL.
- Open: 59 | In Progress: 0 | Done: 0.
- Parallel capacity: 5 workers at the start (T001, T004, T006, T007, T016, T020, T026, T032 are
  pairwise independent; files M, T, ID, S, J are independent fronts).
- Milestone: T039 `integralPeriodLattice_eq` (preceded by CLEANUP-ALL-1).

Generality defaults (apply to every ticket unless the ticket says otherwise): keep the skeleton's
typeclass assumptions exactly (they were chosen minimal: `RCLike 𝕜` + normed spaces for curve
integrals; `CommRing`/`Field`/`NontriviallyNormedField` with `NeZero 2`, `NeZero 3` only where
division occurs; arbitrary `PeriodPair`). Do not add `IsElliptic`/`CharZero`/reality
assumptions. If a proof needs an extra hypothesis, that is a B2 stop, not a reason to add it.

---

### [T001] `Path.extend_map'`
- **Status**: done (finished 2026-09-10)
- **Progress**: closed by `rfl` — `Path.extend = Set.IccExtend zero_le_one γ` and
  `(γ.map' h).toFun = f ∘ γ` make both sides definitionally equal; no `Set.IccExtend_apply`
  rewrite needed. File-level cleanup deferred to CLEANUP-1 (board cadence).
- **File**: M
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma extend_map' (γ : Path a b) (h : ContinuousOn f (range γ)) (t : ℝ) :
    (γ.map' h).extend t = f (γ.extend t) := by sorry
```
#### Proof sketch
1. `Path.extend` is `Set.IccExtend zero_le_one γ` and `(γ.map' h).toFun = f ∘ γ` (Mathlib
   `Path.lean:189, 335`), so both sides are `(f ∘ γ) (Set.projIcc 0 1 zero_le_one t)`.
2. `simp [Path.extend, Set.IccExtend_apply]` or `rfl` after `show`.
#### Mathlib lemmas needed
- `Set.IccExtend_apply` (`Order/Interval/Set/ProjIcc.lean:173`), `Path.map'` (def), `Path.extend` (def).
#### Sources
- Mathlib definitions (decomposition L2.1.3, Q17).
#### Generality decision
- Any topological spaces `X`, `Y`, any `f` continuous on `range γ` (the hypothesis of `map'`).

### [T002] `curveIntegralFun_map_add_const`
- **Status**: done (finished 2026-09-10)
- **Progress**: planning refinement — the sketch's chain rule needs `A` to be **ℝ**-linear, but
  `A : E →L[𝕜] E'` is only 𝕜-linear and `[NormedSpace ℝ E]` was declared independently of the
  𝕜-structure. Added `[IsScalarTower ℝ 𝕜 E] [IsScalarTower ℝ 𝕜 E']` to the file's variable line
  (satisfied at every use site: ℝ ⊆ ℂ on ℂ × ℂ) and used `A.restrictScalars ℝ`. Also added
  `[NormedSpace ℝ F]`, required by `curveIntegral_def` for T003. `Path.extend_map'` being `rfl`
  made the final step `rfl` rather than a rewrite.
- **File**: M
- **Depends on**: T001
- **Parallel**: yes (with T004–T032)
- **Type**: lemma

#### Statement
```lean
lemma curveIntegralFun_map_add_const (ω : E' → E' →L[𝕜] F) (A : E →L[𝕜] E') (c : E')
    (γ : Path a b) (hγ : DifferentiableOn ℝ γ.extend I) {t : ℝ} (ht : t ∈ I) :
    curveIntegralFun ω (γ.map' (f := fun x ↦ A x + c) (by fun_prop)) t =
      curveIntegralFun (fun x ↦ (ω (A x + c)).comp A) γ t := by sorry
```
#### Proof sketch
1. Unfold both sides with `curveIntegralFun_def` (irreducible_def lemma): LHS is
   `ω ((γ.map' _).extend t) (derivWithin (γ.map' _).extend I t)`.
2. Rewrite `(γ.map' _).extend = fun s ↦ A (γ.extend s) + c` by `funext` + T001.
3. Chain rule within `I`: from `(hγ t ht).hasDerivWithinAt` get
   `HasDerivWithinAt (fun s ↦ A (γ.extend s) + c) (A (derivWithin γ.extend I t)) I t` via
   `(A.hasFDerivAt.comp_hasDerivWithinAt _ _)` then `.const_add c` (or `.add_const`), and
   `HasDerivWithinAt.derivWithin` with `uniqueDiffOn_Icc zero_lt_one t ht` to identify
   `derivWithin`.
4. Both sides are now `ω (A (γ.extend t) + c) (A (derivWithin γ.extend I t))`; `rfl`/`simp
   [ContinuousLinearMap.comp_apply]`.
#### Mathlib lemmas needed
- `curveIntegralFun_def` (`CurveIntegral/Basic.lean:136`), `HasDerivWithinAt.derivWithin`
  (`Calculus/Deriv/Basic.lean:444`), `uniqueDiffOn_Icc` (`TangentCone/Real.lean:99`),
  `ContinuousLinearMap.hasFDerivAt`, `HasFDerivAt.comp_hasDerivWithinAt`,
  `HasDerivWithinAt.add_const`, `ContinuousLinearMap.comp_apply`.
#### Sources
- Q17 (Mathlib's definition of the curve integral via `derivWithin γ.extend I`).
#### Generality decision
- `A` a continuous linear map (not an equivalence); `hγ : DifferentiableOn ℝ γ.extend I` is
  necessary for a mere CLM (see decomposition L2.1.1 attack [3]).

### [T003] `curveIntegral_map_add_const`
- **Status**: done (finished 2026-09-10)
- **Progress**: `rw [curveIntegral_def, curveIntegral_def]` then
  `intervalIntegral.integral_congr` with T002, converting `t ∈ uIcc 0 1` to `t ∈ I` via
  `Set.uIcc_of_le zero_le_one`. Needed `[NormedSpace ℝ F]` on the variable line for
  `curveIntegral_def`; `omit`ted it in T002. Map.lean is sorry-free and warning-free.
- **File**: M
- **Depends on**: T002
- **Parallel**: yes
- **Type**: theorem

#### Statement
```lean
theorem curveIntegral_map_add_const (ω : E' → E' →L[𝕜] F) (A : E →L[𝕜] E') (c : E')
    (γ : Path a b) (hγ : DifferentiableOn ℝ γ.extend I) :
    ∫ᶜ x in γ.map' (f := fun x ↦ A x + c) (by fun_prop), ω x =
      ∫ᶜ x in γ, (ω (A x + c)).comp A := by sorry
```
#### Proof sketch
1. `simp only [curveIntegral_def']` (or `rw [curveIntegral_def', curveIntegral_def']`) to expose
   `∫ t in (0:ℝ)..1, curveIntegralFun … t` on both sides.
2. `intervalIntegral.integral_congr` (pointwise on `uIcc 0 1 = I`): for `t ∈ I` apply T002.
#### Mathlib lemmas needed
- `curveIntegral_def'` (from `irreducible_def curveIntegral (lemma := curveIntegral_def')`),
  `intervalIntegral.integral_congr`, `Set.uIcc_of_le zero_le_one`.
#### Sources
- Q17; decomposition L2.1.1.
#### Generality decision
- As T002.

### [CLEANUP-1] Run /cleanup on M
- **Status**: in_progress (dispatched to subagent 2026-09-10) · **File**: M · **Depends on**: T003 · **Parallel**: no · **Type**: cleanup
- **Description**: third and last proof ticket on M (T001–T003) → per-file cleanup + final
  cleanup for M in one pass. Check: `Path.extend_map'` could be a `@[simp]` lemma; consider a
  `ContinuousAffineMap` version of T003 only if free.

### [T004] `curveIntegralPeriods` API
- **Status**: done (finished 2026-09-10)
- **Progress**: all four as sketched. `Path.refl_extend`/`refl_range` and `symm_range` used as
  planned; `Path.extend_symm` gives `γ.extend ∘ (1 - ·)` so the `ContDiffOn` side needed
  `ContDiffOn.comp` with `MapsTo (1 - ·) I I`. Needed `public import
  Mathlib.Analysis.Calculus.ContDiff.Operations` — the CurveIntegral import chain does not
  bring in `ContDiff.add`/`sub`, so `fun_prop` could not see `HSub.hSub`.
- **File**: P
- **Depends on**: none
- **Parallel**: yes
- **Type**: API lemmas (definition `curveIntegralPeriods` is already in place)

#### Statement
```lean
lemma curveIntegral_mem_curveIntegralPeriods {p : E} (γ : Path p p)
    (hγ : ContDiffOn ℝ 1 γ.extend I) (hS : range γ ⊆ S) :
    ∫ᶜ x in γ, ω x ∈ curveIntegralPeriods ω S := by sorry

lemma curveIntegralPeriods_mono (h : S ⊆ T) :
    curveIntegralPeriods ω S ⊆ curveIntegralPeriods ω T := by sorry

lemma zero_mem_curveIntegralPeriods (hS : S.Nonempty) : 0 ∈ curveIntegralPeriods ω S := by sorry

lemma neg_mem_curveIntegralPeriods {w : F} (hw : w ∈ curveIntegralPeriods ω S) :
    -w ∈ curveIntegralPeriods ω S := by sorry
```
#### Proof sketch
- `curveIntegral_mem_…`: `exact ⟨p, γ, hγ, hS, rfl⟩`.
- `_mono`: `rintro w ⟨p, γ, hγ, hS, rfl⟩; exact ⟨p, γ, hγ, hS.trans h, rfl⟩`.
- `zero_mem`: `obtain ⟨p, hp⟩ := hS`; loop `Path.refl p`; `∫ᶜ = 0` by `curveIntegral_refl`;
  `(Path.refl p).extend = fun _ ↦ p` by `Path.refl_extend`, so `ContDiffOn` by
  `contDiffOn_const`; `range (Path.refl p) = {p} ⊆ S` (`Path.refl_range`).
- `neg_mem`: `obtain ⟨p, γ, hγ, hS, rfl⟩ := hw`; use `γ.symm`; `curveIntegral_symm` gives
  `∫ᶜ x in γ.symm = -∫ᶜ x in γ`; `Path.extend_symm : γ.symm.extend = γ.extend ∘ (1 - ·)` (check
  exact form at `Path.lean:251`), so `ContDiffOn ℝ 1 γ.symm.extend I` from
  `hγ.comp (contDiff_const.sub contDiff_id).contDiffOn` with `mapsTo` `1 - I ⊆ I`
  (`Set.MapsTo`, `unitInterval.symm`); `range γ.symm = range γ` (`Path.symm_range`).
#### Mathlib lemmas needed
- `curveIntegral_refl` (`Basic.lean:171`), `curveIntegral_symm` (`:213`), `Path.refl_extend`
  (`Path.lean:244`), `Path.extend_symm` (`:251`), `Path.refl_range` (`:146`), `Path.symm_range`
  (`:166`), `contDiffOn_const`, `ContDiffOn.comp`, `ContDiff.contDiffOn`.
#### Sources
- Q17 (`curveIntegral_refl/symm` are Mathlib's API for constant and reversed paths).
#### Generality decision
- General `𝕜, E, F`, arbitrary `S`; `zero_mem` needs `S.Nonempty` (attack-verified).

### [T005] `curveIntegralPeriods_image_add_const`
- **Status**: done (finished 2026-09-10)
- **Progress**: the sketch's `Path.ext`/`Path.cast` round-trip was avoided entirely. Proved the
  single forward inclusion as `private curveIntegralPeriods_subset_image_add_const` (push a loop
  forward by `x ↦ A x + c`, value by T003), then got the reverse by applying that same lemma to
  `A.symm`, `-(A.symm c)` and `(fun x ↦ A x + c) '' S`, rewriting the resulting form back to `ω`
  (`funext`/`ext v`/`simp`) and the resulting image back to `S` (`Set.image_image`, `simp`). No
  base-point casting needed. Extra typeclasses `[NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 E]
  [IsScalarTower ℝ 𝕜 E']` scoped by a second `variable` line so the T004 lemmas stay clean.
  Elaboration traps: `ContDiff` unfolds to an `∃`, so dot-notation `.add_const`/`.sub` on a
  `contDiff_const`/`ContinuousLinearMap.contDiff` term fails — bind a typed `have` first and
  apply `ContDiff.add` by name. `ContDiffOn.differentiableOn` now takes `n ≠ 0`, not `1 ≤ n`.
- **File**: P
- **Depends on**: T003, T004
- **Parallel**: yes (with ID, S, J fronts)
- **Type**: theorem

#### Statement
```lean
theorem curveIntegralPeriods_image_add_const (ω : E' → E' →L[𝕜] F) (A : E ≃L[𝕜] E') (c : E')
    (S : Set E) : curveIntegralPeriods ω ((fun x ↦ A x + c) '' S) =
      curveIntegralPeriods (fun x ↦ (ω (A x + c)).comp (A : E →L[𝕜] E')) S := by sorry
```
#### Proof sketch
Let `Φ x := A x + c`, `Ψ y := A.symm y + (-(A.symm c))` (so `Ψ (Φ x) = x`, `Φ (Ψ y) = y`, by
`A.symm_apply_apply`, `map_add`, `map_neg`).
1. `ext w; constructor`.
2. (⊆) `rintro ⟨q, γ, hγ, hS, rfl⟩`. Set `δ := γ.map' (f := Ψ) (by fun_prop)`, a loop at `Ψ q`.
   `ContDiffOn ℝ 1 δ.extend I`: rewrite `δ.extend = Ψ ∘ γ.extend` (T001, `funext`), and
   `Ψ` is `ContDiff` (`A.symm.contDiff.add contDiff_const`), so `ContDiff.comp_contDiffOn`.
   `range δ ⊆ S`: `range δ = Ψ '' range γ ⊆ Ψ '' (Φ '' S) = S` (`Set.image_image`,
   `Ψ ∘ Φ = id`). Now `γ = δ.map' (f := Φ) _` up to `Path.ext` (pointwise `Φ (Ψ (γ t)) = γ t`);
   the target base point is `Φ (Ψ q) = q` — use `Path.cast` or `Path.ext` after `subst`; then
   `∫ᶜ x in γ, ω x = ∫ᶜ x in δ.map' _, ω x = ∫ᶜ x in δ, (ω (A x + c)).comp A` by T003 with
   `hγ := (hδ).differentiableOn le_rfl`. Conclude with `⟨Ψ q, δ, hδ, hδS, this⟩`.
3. (⊇) symmetric: from `⟨p, γ, hγ, hS, rfl⟩` take `γ.map' (f := Φ) _`, a loop at `Φ p`;
   `ContDiffOn` as above with `Φ`; `range ⊆ Φ '' S` by `Set.image_subset`; T003 gives the value.
Bridging: `Path.ext`/`Path.cast` for base-point equalities; `Set.image_subset_iff`;
`ContinuousLinearEquiv.coe_coe`.
#### Mathlib lemmas needed
- T001, T003, `ContinuousLinearEquiv.symm_apply_apply`, `apply_symm_apply`,
  `ContinuousLinearEquiv.contDiff`, `ContDiff.comp_contDiffOn`, `ContDiffOn.differentiableOn`,
  `Set.image_image`, `Set.image_subset`, `Path.ext`, `Path.cast`, `curveIntegral_cast`
  (`Basic.lean:185`).
#### Sources
- decomposition L2.1 (composition attack recorded).
#### Generality decision
- `A` an equivalence (needed for the inverse direction); `c` arbitrary.

### [CLEANUP-2] Run /cleanup on P
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)
- **Description**: final per-file cleanup for P (2 proof tickets). Consider stating T005 for
  `E ≃ᴬ[𝕜] E'` (`ContinuousAffineEquiv`) if the API makes it shorter; otherwise leave.

### [T006] `eventually_eq_of_sq_eq_sq`
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched; `ContinuousAt.eventually_ne` + `linear_combination`. Needed `public import Mathlib.Tactic.LinearCombination`.
- **File**: T
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem

#### Statement
```lean
theorem eventually_eq_of_sq_eq_sq (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h : f a = g a)
    (h0 : f a ≠ 0) (hsq : ∀ᶠ x in 𝓝 a, f x ^ 2 = g x ^ 2) : ∀ᶠ x in 𝓝 a, f x = g x := by sorry
```
#### Proof sketch
1. `have hne : ∀ᶠ x in 𝓝 a, f x + g x ≠ 0 := (hf.add hg).eventually_ne (by rw [← h]; simpa
   using mul_ne_zero two_ne_zero h0)` — `f a + g a = 2 * f a ≠ 0` uses `NeZero (2 : 𝕜)`
   (`two_ne_zero`).
2. `filter_upwards [hsq, hne] with x hx hx'`; from `f x ^ 2 = g x ^ 2` get
   `(f x - g x) * (f x + g x) = 0` (`by ring_nf; linear_combination hx` or
   `sq_sub_sq`/`mul_self_eq_mul_self_iff`), so `f x - g x = 0` (`mul_eq_zero`, `hx'`), i.e.
   `sub_eq_zero.mp`.
#### Mathlib lemmas needed
- `ContinuousAt.add`, `ContinuousAt.eventually_ne` (`Topology/Separation/Basic.lean:710`),
  `two_ne_zero`, `sq_sub_sq` / `mul_self_eq_mul_self_iff`, `mul_eq_zero`, `sub_eq_zero`.
#### Sources
- decomposition L4.4 (attack log shows `h`, `h0` necessary).
#### Generality decision
- `[Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [T1Space 𝕜] [NeZero (2 : 𝕜)]`;
  `α` any topological space. (Could be `[DivisionRing]`; keep `Field` unless `ring` needs
  commutativity anyway — it does for step 2.)

### [CLEANUP-3] Run /cleanup on T
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)
- **Description**: final cleanup for T; check the name against Mathlib naming (`eventually_eq`
  vs `EventuallyEq`), consider `Filter.EventuallyEq` phrasing.

### [T007] `eval_Ψ₂Sq_eq_sq_of_equation`
- **Status**: done (finished 2026-09-10)
- **Progress**: `equation_iff` then `linear_combination (-4) * h` (the sketch's `4 * h` has the wrong sign).
- **File**: ID
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma eval_Ψ₂Sq_eq_sq_of_equation {x y : R} (h : W.toAffine.Equation x y) :
    W.Ψ₂Sq.eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by sorry
```
#### Proof sketch
1. `rw [WeierstrassCurve.Affine.equation_iff] at h` — `h : y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`.
2. `simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X, b₂, b₄, b₆]`.
3. `linear_combination 4 * h` (the identity `4x³ + (a₁²+4a₂)x² + 2(2a₄+a₁a₃)x + (a₃²+4a₆) −
   (2y+a₁x+a₃)² = 4·(RHS − LHS of h)`).
Alternative: evaluate Mathlib's `C_Ψ₂Sq` at `(x, y)` with `evalEval_polynomialY`.
#### Mathlib lemmas needed
- `WeierstrassCurve.Affine.equation_iff` (`Affine/Basic.lean:156`), `WeierstrassCurve.Ψ₂Sq`
  (def, `DivisionPolynomial/Basic.lean:117`), `WeierstrassCurve.b₂/b₄/b₆` (defs),
  `Polynomial.eval_add/mul/pow/C/X`, `linear_combination`.
#### Sources
- Q19 (`C_Ψ₂Sq`), decomposition L2.5.
#### Generality decision
- Any `CommRing R`, no division.

### [T008] `eval_Ψ₂Sq_sub` (general field)
- **Status**: done (finished 2026-09-10)
- **Progress**: `field_simp; ring` with `(12 : F) ≠ 0`, `(216 : F) ≠ 0` built from `NeZero.ne 2/3`.
- **File**: ID
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma eval_Ψ₂Sq_sub (x : F) :
    W.Ψ₂Sq.eval (x - W.b₂ / 12) = 4 * x ^ 3 - W.c₄ / 12 * x - W.c₆ / 216 := by sorry
```
#### Proof sketch
1. `have h2 : (2 : F) ≠ 0 := NeZero.ne 2; have h3 : (3 : F) ≠ 0 := NeZero.ne 3`.
2. `have h12 : (12 : F) ≠ 0 := by rw [show (12 : F) = 2 * 2 * 3 by norm_num]; exact
   mul_ne_zero (mul_ne_zero h2 h2) h3` and likewise `(216 : F) = 2 * 2 * 2 * 3 * 3 * 3 ≠ 0`.
3. `simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X, c₄, c₆, b₄]`.
4. `field_simp` then `ring` (the ℝ proof, sorry-free at commit 869ce0a2, was `simp only [...];
   ring`; over a general field `ring` needs the denominators cleared first).
#### Mathlib lemmas needed
- `NeZero.ne`, `mul_ne_zero`, `WeierstrassCurve.c₄`, `c₆`, `b₄` (defs), `field_simp`, `ring`.
#### Sources
- DLMF §23.6 / [Sil2009] III §1 ($g_2 = c_4/12$, $g_3 = c_6/216$); decomposition L2.4.
#### Generality decision
- `[Field F] [NeZero (2 : F)] [NeZero (3 : F)]` (exactly `12 ≠ 0`).

### [T009] `invariantDifferential` API
- **Status**: done (finished 2026-09-10)
- **Progress**: `invariantDifferential_apply` by `simp`; continuity needed `show` to eta-expand `W.invariantDifferential` before `ContinuousOn.smul` could match.
- **File**: ID
- **Depends on**: none
- **Parallel**: yes
- **Type**: API lemmas

#### Statement
```lean
@[simp]
lemma invariantDifferential_apply (p v : F × F) :
    W.invariantDifferential p v = v.1 / (2 * p.2 + W.a₁ * p.1 + W.a₃) := by sorry

lemma continuousOn_invariantDifferential :
    ContinuousOn W.invariantDifferential W.affineNonTwoTorsion := by sorry
```
#### Proof sketch
- `_apply`: `simp [invariantDifferential, div_eq_inv_mul]` (`ContinuousLinearMap.smul_apply`,
  `ContinuousLinearMap.fst_apply`, `smul_eq_mul`).
- `continuousOn`: `refine ContinuousOn.smul ?_ continuousOn_const`; the scalar
  `p ↦ (2 * p.2 + W.a₁ * p.1 + W.a₃)⁻¹` is `ContinuousOn.inv₀ (by fun_prop) (fun p hp ↦ hp.2)`.
  Topology on `→L` comes from `Mathlib.Analysis.Normed.Operator.Basic` (imported).
#### Mathlib lemmas needed
- `ContinuousLinearMap.smul_apply`, `ContinuousLinearMap.fst_apply`, `div_eq_inv_mul`,
  `ContinuousOn.smul`, `ContinuousOn.inv₀`, `continuousOn_const`.
#### Sources
- Q1 (the invariant differential $dx/(2y+a_1x+a_3)$); decomposition L2.9, L2.10.
#### Generality decision
- `NontriviallyNormedField F`; no characteristic assumption (note L2.10 attack: `Equation` is
  unused in `continuousOn` — keep the set as stated for downstream use).

### [CLEANUP-4] Run /cleanup on ID (after T007–T009)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)
  **Type**: cleanup
- **Description**: per-file cadence cleanup (3 proof tickets). Also: `toShortModel_apply` is
  `rfl` — decide `@[simp]` vs unfolding; check the `NeZero` section variables produce no
  "unused section variable" warnings (they did not in the skeleton build).

### [T010] `toShortModelLinear` and `toShortModel_eq`
- **Status**: done (finished 2026-09-10)
- **Progress**: def obligations and `_apply` by `ext <;> simp`; `toShortModel_eq` by `Prod.ext rfl` + `ring`. `[NeZero 2]` `omit`ted from both lemmas.
- **File**: ID
- **Depends on**: CLEANUP-4
- **Parallel**: yes (with T011)
- **Type**: def obligations + API lemmas

#### Statement
```lean
def toShortModelLinear : (F × F) ≃L[F] (F × F) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst F F F).prod
      (ContinuousLinearMap.snd F F F + (W.a₁ / 2) • ContinuousLinearMap.fst F F F))
    ((ContinuousLinearMap.fst F F F).prod
      (ContinuousLinearMap.snd F F F - (W.a₁ / 2) • ContinuousLinearMap.fst F F F))
    (fun p ↦ by sorry) (fun p ↦ by sorry)

@[simp]
lemma toShortModelLinear_apply (p : F × F) :
    W.toShortModelLinear p = (p.1, p.2 + W.a₁ / 2 * p.1) := by sorry

lemma toShortModel_eq (p : F × F) :
    W.toShortModel p = W.toShortModelLinear p + (W.b₂ / 12, W.a₃ / 2) := by sorry
```
#### Proof sketch
- Obligations: `Prod.ext` then `simp [ContinuousLinearMap.prod_apply, ContinuousLinearMap.add_apply,
  ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]` and `ring`
  (`(p.2 + a p.1) - a p.1 = p.2`, no characteristic needed).
- `_apply`: `ContinuousLinearEquiv.equivOfInverse_apply` + the same `simp`.
- `toShortModel_eq`: `Prod.ext` + `simp [toShortModel_apply, toShortModelLinear_apply]` + `ring`
  (`p.2 + (a₁ p.1 + a₃)/2 = (p.2 + a₁/2 * p.1) + a₃/2`).
#### Mathlib lemmas needed
- `ContinuousLinearEquiv.equivOfInverse_apply` (`Module/Equiv.lean:634`),
  `ContinuousLinearMap.prod_apply` (`PiProd.lean:96`), `ContinuousLinearMap.fst_apply/snd_apply/
  add_apply/sub_apply/smul_apply`, `Prod.ext`.
#### Sources
- [Sil2009] III §1 (change of variables with `u = 1`, `s = −a₁/2`); decomposition L2.7, L2.8.
#### Generality decision
- The section carries `[NeZero (2 : F)]`; the obligations do not use it — if the linter flags an
  unused instance, keep the def where it is (the downstream pullback needs `NeZero 2`) and `omit`
  in the `_apply`/`_eq` lemmas.

### [T011] `toShortModel_mem_affineNonTwoTorsion_iff`
- **Status**: done (finished 2026-09-10)
- **Progress**: **`ring` cannot cancel `12/12` in a general field** (char unknown), so the sketch's `linear_combination h1` fails. Restructured: prove `hdiff` (the two equations' LHS−RHS are *equal*, coefficient 1 — verified numerically first) by `field_simp; ring` with explicit `2,3,12,48,864 ≠ 0`, and `hden` for the non-torsion side, then `and_congr` + `← sub_eq_zero` + `hdiff`. `WeierstrassCurve.toAffine` must be in the `simp only` set or `W.toAffine.a₁` and `W.a₁` stay distinct atoms.
- **File**: ID
- **Depends on**: T007, T008, CLEANUP-4
- **Parallel**: yes (with T010)
- **Type**: lemma

#### Statement
```lean
lemma toShortModel_mem_affineNonTwoTorsion_iff {p : F × F} :
    W.toShortModel p ∈ W.shortModel.affineNonTwoTorsion ↔ p ∈ W.affineNonTwoTorsion := by sorry
```
#### Proof sketch
Write `p = (x, y)`, `X := x + b₂/12`, `Y := y + (a₁x + a₃)/2`.
1. `simp only [mem_affineNonTwoTorsion, toShortModel_apply, shortModel, Affine.equation_iff]` —
   the short equation reads `Y² + 0 + 0 = X³ + 0 + (-c₄/48) X + (-c₆/864)` and the
   non-torsion condition `2Y + 0·X + 0 ≠ 0`.
2. Non-torsion conjunct: `2Y = 2y + a₁x + a₃` by `ring` — `and_congr_right'`/`Iff.and`.
3. Equation conjunct: `4Y² = (2y + a₁x + a₃)²` (`ring`); `4(X³ − c₄/48 X − c₆/864) = 4X³ −
   c₄/12 X − c₆/216 = Ψ₂Sq.eval (X − b₂/12) = Ψ₂Sq.eval x` by T008 (`add_sub_cancel_right`).
   So the short equation ⟺ `(2y+a₁x+a₃)² = Ψ₂Sq.eval x` (multiply/divide by `4 ≠ 0`:
   `mul_right_cancel₀`, `NeZero 2`). Finally `(2y+a₁x+a₃)² = Ψ₂Sq.eval x ⟺ W.Equation x y`:
   `→` needs `4 * (curve polynomial) = Ψ₂Sq − ψ₂²` — from T007's identity in the form
   `Ψ₂Sq.eval x − (2y+a₁x+a₃)² = −4·(y² + a₁xy + a₃y − (x³ + …))` (`ring`), so `Equation` follows
   from `4 ≠ 0`; `←` is T007.
Bridging: `constructor <;> rintro ⟨h1, h2⟩`, `field_simp`, `linear_combination`.
#### Mathlib lemmas needed
- `WeierstrassCurve.Affine.equation_iff`, T007, T008, `mul_right_cancel₀`, `NeZero.ne`,
  `linear_combination`, `field_simp`.
#### Sources
- Q19; [Sil2009] III §1; decomposition L2.3.
#### Generality decision
- `[Field F] [NeZero 2] [NeZero 3]` (both used).

### [T012] `image_toShortModel_affineNonTwoTorsion`
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched; `(by rw [hqp]; exact hq)` rather than `hqp ▸ hq` (wrong rewrite direction).
- **File**: ID
- **Depends on**: T011
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma image_toShortModel_affineNonTwoTorsion :
    W.toShortModel '' W.affineNonTwoTorsion = W.shortModel.affineNonTwoTorsion := by sorry
```
#### Proof sketch
1. `ext q; constructor`.
2. `rintro ⟨p, hp, rfl⟩; exact W.toShortModel_mem_affineNonTwoTorsion_iff.mpr hp`.
3. `intro hq`; put `p := (q.1 - W.b₂ / 12, q.2 - (W.a₁ * (q.1 - W.b₂ / 12) + W.a₃) / 2)`;
   `have : W.toShortModel p = q := by ext <;> simp <;> ring`; `exact ⟨p, W.toShortModel_mem_…
   .mp (this ▸ hq), this⟩`.
#### Mathlib lemmas needed
- T011, `Set.ext`, `Set.mem_image`, `Prod.ext`.
#### Sources
- decomposition L2.2.
#### Generality decision
- As T011.

### [CLEANUP-5] Run /cleanup on ID (after T010–T012)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)
  **Type**: cleanup
- **Description**: per-file cadence cleanup (6 proof tickets on ID so far).

### [T013] `invariantDifferential_shortModel_comp`
- **Status**: done (finished 2026-09-10)
- **Progress**: `ContinuousLinearMap.ext fun v` — plain `ext` splits a `(F × F) →L[F] F` into `inl`/`inr` components instead. Denominator identity via `linear_combination hhalf`.
- **File**: ID
- **Depends on**: T009, T010, CLEANUP-5
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma invariantDifferential_shortModel_comp (p : F × F) :
    (W.shortModel.invariantDifferential (W.toShortModel p)).comp
      (W.toShortModelLinear : (F × F) →L[F] (F × F)) = W.invariantDifferential p := by sorry
```
#### Proof sketch
1. `ext v` (`ContinuousLinearMap.ext`), `simp only [ContinuousLinearMap.comp_apply,
   invariantDifferential_apply, toShortModelLinear_apply, toShortModel_apply, shortModel]`:
   LHS `= v.1 / (2 * (p.2 + (W.a₁ * p.1 + W.a₃) / 2) + 0 * (p.1 + W.b₂/12) + 0)`, RHS
   `= v.1 / (2 * p.2 + W.a₁ * p.1 + W.a₃)`.
2. `congr 1; ring` after `mul_div_cancel₀`-style normalisation: `2 * (a/2) = a` needs
   `(2 : F) ≠ 0` (`NeZero.ne 2`); `field_simp` then `ring`. Note both sides are `v.1 / 0 = 0`
   when the denominator vanishes; the identity of denominators handles that uniformly.
#### Mathlib lemmas needed
- `ContinuousLinearMap.ext`, `ContinuousLinearMap.comp_apply`, T009, T010, `field_simp`, `ring`.
#### Sources
- [Sil2009] III §1 (ω preserved when `u = 1`); decomposition L2.6.
#### Generality decision
- `NontriviallyNormedField F`, `NeZero 2`.

### [CLEANUP-6] Run /cleanup on ID (final)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)
- **Description**: final per-file cleanup for ID. Naming review: `affineNonTwoTorsion`,
  `toShortModel`, `toShortModelLinear`, `shortModel` — align with Mathlib's `VariableChange`
  vocabulary if a reviewer would expect it; keep unless clearly better.

### [T014] `integralPeriodLattice` API
- **Status**: done (finished 2026-09-10)
- **Progress**: `Polynomial.finite_setOfPred_isRoot` + `Set.Finite.infinite_compl` for a non-root `x`, `IsAlgClosed.exists_pow_nat_eq` for `s`, then `linear_combination hs / 4`. Needed `public import` of `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree` (for `Ψ₂Sq_ne_zero`) and `Mathlib.Analysis.Complex.Polynomial.Basic` (for `IsAlgClosed ℂ`).
- **File**: IPL
- **Depends on**: T004, T007
- **Parallel**: yes
- **Type**: API lemmas

#### Statement
```lean
lemma affineNonTwoTorsion_nonempty : W.affineNonTwoTorsion.Nonempty := by sorry

lemma zero_mem_integralPeriodLattice : 0 ∈ W.integralPeriodLattice := by sorry

lemma neg_mem_integralPeriodLattice {w : ℂ} (hw : w ∈ W.integralPeriodLattice) :
    -w ∈ W.integralPeriodLattice := by sorry
```
#### Proof sketch
- `nonempty`: `Ψ₂Sq ≠ 0` (`W.Ψ₂Sq_ne_zero four_ne_zero`, Mathlib `Degree.lean:89`) so by
  `Polynomial.exists_eval_ne_zero` (`Roots.lean:772`, needs `[Infinite ℂ]`) pick `x` with
  `W.Ψ₂Sq.eval x ≠ 0`; `IsAlgClosed.exists_pow_nat_eq (W.Ψ₂Sq.eval x) two_pos` gives `s` with
  `s ^ 2 = W.Ψ₂Sq.eval x`; set `y := (s - W.a₁ * x - W.a₃) / 2`; then `2y + a₁x + a₃ = s ≠ 0`
  (`pow_ne_zero_iff`) and `W.toAffine.Equation x y`: by `equation_iff` and the T007 identity
  run backwards (`Ψ₂Sq.eval x − (2y+a₁x+a₃)² = −4·(polynomial)` by `ring` after `simp [Ψ₂Sq, b₂,
  b₄, b₆]`, so `polynomial = 0` as `4 ≠ 0`).
- `zero_mem`: `zero_mem_curveIntegralPeriods W.affineNonTwoTorsion_nonempty`.
- `neg_mem`: `neg_mem_curveIntegralPeriods hw`.
#### Mathlib lemmas needed
- `WeierstrassCurve.Ψ₂Sq_ne_zero`, `Polynomial.exists_eval_ne_zero`,
  `IsAlgClosed.exists_pow_nat_eq` (`IsAlgClosed/Basic.lean:81`), `pow_ne_zero_iff`,
  `WeierstrassCurve.Affine.equation_iff`, T004.
#### Sources
- Q17/Q19; decomposition "Definition/API leaves".
#### Generality decision
- `W : WeierstrassCurve ℂ` (the definition is over ℂ); `nonempty` could be stated over any
  algebraically closed infinite field — do so only if free.

### [T015] `integralPeriodLattice_shortModel`
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched: `Set.image_congr` to swap `toShortModel` for its affine form, T005, then `funext` + T013.
- **File**: IPL
- **Depends on**: T005, T010, T012, T013
- **Parallel**: yes
- **Type**: theorem

#### Statement
```lean
theorem integralPeriodLattice_shortModel :
    W.shortModel.integralPeriodLattice = W.integralPeriodLattice := by sorry
```
#### Proof sketch
1. `unfold integralPeriodLattice`.
2. `rw [← W.image_toShortModel_affineNonTwoTorsion]` (T012), then rewrite the map:
   `W.toShortModel = fun p ↦ W.toShortModelLinear p + (W.b₂ / 12, W.a₃ / 2)` (`funext`, T010's
   `toShortModel_eq`), so `Set.image` is of the form required by T005.
3. `rw [curveIntegralPeriods_image_add_const W.shortModel.invariantDifferential
   W.toShortModelLinear (W.b₂ / 12, W.a₃ / 2)]` (T005).
4. The pulled-back form is `fun p ↦ (W.shortModel.invariantDifferential (W.toShortModelLinear p
   + (…))).comp ↑W.toShortModelLinear = fun p ↦ W.invariantDifferential p` by `funext p` and T013
   (rewrite `W.toShortModelLinear p + (…) = W.toShortModel p` with T010 backwards); `congr`.
#### Mathlib lemmas needed
- T005, T010, T012, T013, `funext`, `Set.image_congr`/`congrArg`.
#### Sources
- decomposition L2 (composition attack recorded).
#### Generality decision
- ℂ (definition site); `NeZero (2:ℂ)`, `NeZero (3:ℂ)` are instances.

### [CLEANUP-7] Run /cleanup on IPL
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)
  **Type**: cleanup
- **Description**: final per-file cleanup for IPL (2 proof tickets).

### [T016] `tendsto_weierstrassP_cobounded`
- **Status**: done (finished 2026-09-10)
- **Progress**: **one line** — Mathlib has `tendsto_cobounded_of_meromorphicOrderAt_neg`, so the pole behaviour follows directly from `order_weierstrassP`. The sketch's Laurent/`weierstrassP_eq` route is unnecessary.
- **File**: S
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma tendsto_weierstrassP_cobounded {l : ℂ} (hl : l ∈ L.lattice) :
    Tendsto ℘[L] (𝓝[≠] l) (Bornology.cobounded ℂ) := by sorry
```
#### Proof sketch
1. Reduce to `l = 0`: `℘[L] z = ℘[L] (z - l)` (`L.weierstrassP_sub_coe z ⟨l, hl⟩`), and
   `z ↦ z - l` maps `𝓝[≠] l` to `𝓝[≠] 0` (`tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`
   with `sub_ne_zero`), so `Tendsto.comp`.
2. At `0`: `rw [tendsto_norm_atTop_iff_cobounded.symm]`… precisely use
   `tendsto_norm_atTop_iff_cobounded : Tendsto f l (cobounded E) ↔ Tendsto (‖f ·‖) l atTop`
   (`Normed/Group/Bounded.lean:46`; check direction/name). Write `℘ z = ℘[L - 0] z + 1 / z ^ 2`
   (`L.weierstrassP_eq z`, project `Uniqueness.lean:62`). `℘[L - 0]` is continuous at `0`
   (`L.analyticAt_weierstrassPExcept 0` … `.continuousAt`), hence bounded near `0`; and
   `‖1 / z ^ 2‖ = ‖z‖⁻¹ ^ 2 → ∞` (`NormedField.tendsto_norm_inv_nhdsNE_zero_atTop`,
   `Field/Lemmas.lean:202`, composed with `pow` via `Filter.Tendsto.atTop_pow`/`tendsto_pow_atTop`,
   `norm_pow`, `norm_inv`, `one_div`). Then `‖a + b‖ ≥ ‖b‖ − ‖a‖` (`norm_sub_norm_le`,
   `norm_add_eq_...`) gives `Tendsto (‖℘ ·‖) (𝓝[≠] 0) atTop` by `Filter.tendsto_atTop_add_left_of_le`
   / `tendsto_atTop_mono` with the eventual bound.
Bridging: `Filter.Eventually.mono`, `Metric.tendsto_nhdsWithin_nhds`.
#### Mathlib lemmas needed
- `PeriodPair.weierstrassP_sub_coe`, `PeriodPair.weierstrassP_eq` (project),
  `PeriodPair.analyticAt_weierstrassPExcept`, `tendsto_norm_atTop_iff_cobounded`,
  `NormedField.tendsto_norm_inv_nhdsNE_zero_atTop`, `tendsto_pow_atTop`, `norm_sub_norm_le`,
  `Filter.tendsto_atTop_mono`, `ContinuousAt.eventually`-style boundedness (`Metric.continuousAt_iff`).
#### Sources
- Q18 (`order_weierstrassP`), Q4 ("a pole … congruent"); decomposition AG1.1.
#### Generality decision
- Arbitrary `PeriodPair`; `hl` necessary.

### [T017] `differentiable_inv_weierstrassP_sub`
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched. `Filter.Tendsto.congr'` needs the equality in the direction `(Inv.inv ∘ f) =ᶠ indicator`. `ContinuousAt` at the pole assembled from `nhdsNE_sup_pure` + `Filter.tendsto_sup`; the cobounded shift `℘ − c` via `tendsto_atTop_mono` with `norm_sub_norm_le` and `tendsto_atTop_add_const_right`.
- **File**: S
- **Depends on**: T016
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma differentiable_inv_weierstrassP_sub (c : ℂ) (hc : ∀ z, z ∉ L.lattice → ℘[L] z ≠ c) :
    Differentiable ℂ ((L.lattice : Set ℂ)ᶜ.indicator fun z ↦ (℘[L] z - c)⁻¹) := by sorry
```
#### Proof sketch
Let `g := (Λᶜ).indicator fun z ↦ (℘ z − c)⁻¹`. `intro z; by_cases hz : z ∈ L.lattice`.
1. `z ∉ Λ`: `g =ᶠ[𝓝 z] fun w ↦ (℘ w − c)⁻¹` on the open set `Λᶜ`
   (`L.isClosed_lattice.isOpen_compl.mem_nhds hz`, `Set.indicator_of_mem`), and the latter is
   `DifferentiableAt` by `((L.analyticOnNhd_weierstrassP z hz).differentiableAt.sub_const c).inv
   (sub_ne_zero.mpr (hc z hz))`; transfer with `DifferentiableAt.congr_of_eventuallyEq`.
2. `z ∈ Λ`: apply `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`:
   - `∀ᶠ w in 𝓝[≠] z, DifferentiableAt ℂ g w`: `L.compl_lattice_sdiff_singleton_mem_nhds z`
     (Weierstrass.lean:140: `(L.latticeᶜ ∪ {z})`-type neighbourhood; on it minus `z` the points
     are off `Λ`, so step 1 applies) — `filter_upwards [mem_nhdsWithin_of_mem_nhds …,
     self_mem_nhdsWithin]`.
   - `ContinuousAt g z`: `g z = 0` (`Set.indicator_of_notMem`, `hz`), and `g w → 0` as `w → z`:
     on `𝓝[≠] z`, `g w = (℘ w − c)⁻¹` eventually (off Λ, again by
     `compl_lattice_sdiff_singleton_mem_nhds`), and `℘ w − c → cobounded` (T016 +
     `Filter.Tendsto.sub_const`… use `tendsto_norm_atTop_iff_cobounded` and `norm_sub_norm_le`),
     so `(℘ w − c)⁻¹ → 0` (`tendsto_inv_atTop_zero` on norms / `Filter.Tendsto.inv_tendsto_atTop`
     + `tendsto_zero_iff_norm_tendsto_zero`); combine with the value at `z` via
     `continuousAt_iff_continuous_left_right`-free route: `ContinuousAt` from
     `tendsto_nhdsWithin_iff`/`ContinuousAt` ⟺ `Tendsto g (𝓝[≠] z) (𝓝 (g z))`
     (`continuousAt_iff_punctured_nhds`? — use `tendsto_nhds_iff`… simplest:
     `ContinuousWithinAt.continuousAt`-free: `continuousAt_update_same`-style; or
     `Filter.Tendsto.congr'` and `tendsto_nhdsWithin_of_tendsto_nhds`). Then
     `.differentiableAt`.
#### Mathlib lemmas needed
- `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
  (`RemovableSingularity.lean:36`), `PeriodPair.compl_lattice_sdiff_singleton_mem_nhds`
  (`Weierstrass.lean:140`), `PeriodPair.isClosed_lattice`, `PeriodPair.analyticOnNhd_weierstrassP`,
  `Set.indicator_of_mem`, `Set.indicator_of_notMem`, `DifferentiableAt.congr_of_eventuallyEq`,
  `DifferentiableAt.inv`, T016, `tendsto_norm_atTop_iff_cobounded`,
  `Filter.Tendsto.inv_tendsto_atTop`, `tendsto_zero_iff_norm_tendsto_zero`,
  `continuousAt_iff_punctured_nhds`?? (verify; fallback `Metric.continuousAt_iff` +
  `Metric.tendsto_nhdsWithin_nhds`).
#### Sources
- Q4 ("such a function is not just meromorphic, but rather it is analytic"), Q12;
  decomposition AG1.2.
#### Generality decision
- Arbitrary `PeriodPair`, any `c`.

### [T018] `exists_weierstrassP_eq` (℘ is surjective)
- **Status**: done (finished 2026-09-10)
- **Progress**: **closes the only `sorry` in the LeanBridge uniformisation chain** (`LeanBridge/work/inverse.lean:72`, same statement and same name). Exactly as sketched: Liouville on the indicator of `(℘ − c)⁻¹`, periodicity, `IsZLattice.isCompact_range_of_periodic`, evaluate at `ω₁/2` vs `0`.
- **File**: S
- **Depends on**: T017
- **Parallel**: yes
- **Type**: theorem (API gap AG1)

#### Statement
```lean
theorem exists_weierstrassP_eq (c : ℂ) : ∃ z, z ∉ L.lattice ∧ ℘[L] z = c := by sorry
```
#### Proof sketch
1. `by_contra! hc` — `hc : ∀ z, z ∉ L.lattice → ℘[L] z ≠ c`.
2. `set g := (L.lattice : Set ℂ)ᶜ.indicator fun z ↦ (℘[L] z - c)⁻¹`;
   `have hg : Differentiable ℂ g := L.differentiable_inv_weierstrassP_sub c hc` (T017).
3. Periodicity: `have hper : ∀ z w, w ∈ L.lattice → g (z + w) = g z`: `intro z w hw`; `by_cases
   hz : z ∈ L.lattice` — then `z + w ∈ Λ` (`add_mem`) and both sides `0`; else `z + w ∉ Λ`
   (`fun h ↦ hz (by simpa using sub_mem h hw)`) and both sides are `(℘ (z + w) − c)⁻¹ =
   (℘ z − c)⁻¹` by `L.weierstrassP_add_coe z ⟨w, hw⟩`.
4. Bounded: `have hb : IsBounded (range g) := (IsZLattice.isCompact_range_of_periodic L.lattice
   g hg.continuous hper).isBounded` (instances `DiscreteTopology L.lattice`, `IsZLattice ℝ
   L.lattice` are in Mathlib's `Weierstrass.lean:118–120`; same pattern as `Weierstrass.lean:1070`).
5. Liouville: `have h := hg.apply_eq_apply_of_bounded hb (L.ω₁ / 2) 0` — `g (ω₁/2) = g 0`.
6. `g 0 = 0` (`Set.indicator_of_notMem`, `zero_mem`), `g (ω₁/2) = (℘ (ω₁/2) − c)⁻¹`
   (`Set.indicator_of_mem`, `L.ω₁_div_two_notMem_lattice`), nonzero by
   `inv_ne_zero (sub_ne_zero.mpr (hc _ L.ω₁_div_two_notMem_lattice))`. Contradiction.
#### Mathlib lemmas needed
- T017, `IsZLattice.isCompact_range_of_periodic` (`ZLattice/Basic.lean:788`),
  `IsCompact.isBounded`, `Differentiable.apply_eq_apply_of_bounded` (`Liouville.lean:114`),
  `Differentiable.continuous`, `PeriodPair.weierstrassP_add_coe`, `PeriodPair.ω₁_div_two_notMem_lattice`
  (`Weierstrass.lean:103`), `Set.indicator_of_mem/notMem`, `inv_ne_zero`, `sub_ne_zero`,
  `Submodule.add_mem`, `Submodule.sub_mem`.
#### Sources
- Q4 (Pastras Thm 1.2, verbatim proof), Q12 (Milne Cor 2.2 proof), Q9 (W&W §20.12 (IV));
  LeanBridge `work/inverse.lean` docstring. Source length: 6 lines (Q4) / 4 lines (Q12) →
  expect ~40 LOC on top of T016–T017 (~120 LOC total for AG1).
#### Generality decision
- Arbitrary `PeriodPair`.

### [CLEANUP-8] Run /cleanup on S (after T016–T018)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)
- **Description**: per-file cadence cleanup (3 proof tickets). Candidate for Mathlib upstreaming:
  `exists_weierstrassP_eq` — record in the file docstring.

### [T019] `exists_weierstrassP_eq_and_derivWeierstrassP_eq`
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched, first try.
- **File**: S
- **Depends on**: T018, CLEANUP-8
- **Parallel**: yes
- **Type**: theorem (shared-witness existential — documented exception)

#### Statement
```lean
theorem exists_weierstrassP_eq_and_derivWeierstrassP_eq {x y : ℂ}
    (h : y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃) :
    ∃ z, z ∉ L.lattice ∧ ℘[L] z = x ∧ ℘'[L] z = y := by sorry
```
#### Proof sketch
1. `obtain ⟨z, hz, hzx⟩ := L.exists_weierstrassP_eq x` (T018).
2. `have hsq : ℘'[L] z ^ 2 = y ^ 2 := by rw [L.derivWeierstrassP_sq z hz, hzx, h]`.
3. `rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hy | hy`.
   - `exact ⟨z, hz, hzx, hy⟩`.
   - `refine ⟨-z, fun h' ↦ hz (by simpa using neg_mem h'), by rw [L.weierstrassP_neg, hzx],
     by rw [L.derivWeierstrassP_neg, hy, neg_neg]⟩`.
#### Mathlib lemmas needed
- T018, `PeriodPair.derivWeierstrassP_sq` (`Weierstrass.lean:1075`), `sq_eq_sq_iff_eq_or_eq_neg`
  (`Ring/Commute.lean:219`), `PeriodPair.weierstrassP_neg` (`:310`),
  `PeriodPair.derivWeierstrassP_neg` (`:561`), `Submodule.neg_mem_iff`.
#### Sources
- Q13 ("well-defined map … 2:1"), LeanBridge `work/inverse.lean` docstring (sign fix via
  parity); decomposition AG1'.
#### Generality decision
- Arbitrary `PeriodPair`; the witness is shared by the three conjuncts (exception per
  `statement-splitting.md`: shared-witness existential).

### [CLEANUP-9] Run /cleanup on S (final)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)

### [T020] `eventually_weierstrassP_add_eq_add`
- **Status**: done (finished 2026-09-10)
- **Progress**: transcription of `HalfPeriods.eventually_weierstrassP_add_eq_sub` with `g t := (℘(b+t), ℘'(b+t))` (no sign flips). `L.isClosed_lattice.isOpen_compl.mem_nhds` must be applied, not partially applied.
- **File**: J
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma eventually_weierstrassP_add_eq_add {a b : ℂ} (ha : a ∉ L.lattice) (hb : b ∉ L.lattice)
    (h₁ : ℘[L] a = ℘[L] b) (h₂ : ℘'[L] a = ℘'[L] b) :
    ∀ᶠ t : ℝ in 𝓝 0, ℘[L] (a + t) = ℘[L] (b + t) := by sorry
```
#### Proof sketch
Transcribe `PeriodPair.eventually_weierstrassP_add_eq_sub` (`HalfPeriods.lean:136–178`,
sorry-free) verbatim with these replacements: `z₀ + t ↦ a + t` for `f`, and
`g t := (℘[L] (b + t), ℘'[L] (b + t))` (no minus signs) for `g`; the vector field
`v _ p := (p.2, 6 * p.1 ^ 2 - L.g₂ / 2)` is unchanged.
1. Lipschitz set `S ∈ 𝓝 (℘ a, ℘' a)` from `ContDiffAt.exists_lipschitzOnWith` of the `C¹` field.
2. Both curves stay off `Λ` near `0` (open complement, continuity of `t ↦ a + t`, `t ↦ b + t`).
3. `hfd`, `hgd`: `HasDerivAt` of the pairs via `hasDerivAt_weierstrassP`, `hasDerivAt_derivWeierstrassP`
   (project), `.comp_const_add`, `.comp_ofReal`, `.prodMk` — for `g` the derivative of
   `℘'(b + t)` is `6 ℘(b+t)² − g₂/2` exactly as for `f`.
4. Initial values: `f 0 = (℘ a, ℘' a) = (℘ b, ℘' b) = g 0` by `h₁, h₂` (`simp`).
5. `ODE_solution_unique_of_eventually` and `congrArg Prod.fst`.
#### Mathlib lemmas needed
- `ODE_solution_unique_of_eventually` (`ODE/ExistUnique.lean:312`),
  `ContDiffAt.exists_lipschitzOnWith`, `PeriodPair.hasDerivAt_weierstrassP`,
  `PeriodPair.hasDerivAt_derivWeierstrassP` (project HalfPeriods), `HasDerivAt.comp_const_add`,
  `HasDerivAt.comp_ofReal` (`Complex/RealDeriv.lean:97`), `HasDerivAt.prodMk` (`Deriv/Prod.lean:51`),
  `PeriodPair.isClosed_lattice`.
#### Sources
- Q6 (uniqueness for the Weierstrass ODE), Q20; the existing proof is the template. Source
  length: HalfPeriods.lean proof is 42 lines → expect ~45 LOC.
#### Generality decision
- Arbitrary `a, b ∉ Λ`; `h₂` is essential (attack in decomposition AG2.1).

### [T021] `weierstrassP_add_eq_add_of_eq`
- **Status**: done (finished 2026-09-10)
- **Progress**: transcription of `HalfPeriods.weierstrassP_add_eq_sub_of_derivWeierstrassP_eq_zero` with `U := {w | a + w ∉ Λ ∧ b + w ∉ Λ}`; both images are `(· - a)`, `(· - b)`.
- **File**: J
- **Depends on**: T020
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma weierstrassP_add_eq_add_of_eq {a b : ℂ} (ha : a ∉ L.lattice) (hb : b ∉ L.lattice)
    (h₁ : ℘[L] a = ℘[L] b) (h₂ : ℘'[L] a = ℘'[L] b) {z : ℂ} (hz : a + z ∉ L.lattice)
    (hz' : b + z ∉ L.lattice) : ℘[L] (a + z) = ℘[L] (b + z) := by sorry
```
#### Proof sketch
Transcribe `PeriodPair.weierstrassP_add_eq_sub_of_derivWeierstrassP_eq_zero`
(`HalfPeriods.lean:182–222`) with `U := {w | a + w ∉ L.lattice ∧ b + w ∉ L.lattice}`:
1. `U = ((fun l ↦ l - a) '' Λ ∪ (fun l ↦ l - b) '' Λ)ᶜ` (both images: `a + w ∈ Λ ↔ w ∈ (· - a) '' Λ`),
   hence preconnected by `Complex.isPreconnected_compl_of_countable` and
   `L.countable_lattice.image`.
2. `F w := ℘ (a + w)`, `G w := ℘ (b + w)` are `AnalyticOnNhd ℂ … U` (`analyticOnNhd_weierstrassP`
   composed with `fun_prop`-affine maps).
3. They agree frequently at `0` within `𝓝[≠] 0`: from T020 along the real axis (same
   `Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0)` trick as in the template).
4. `0 ∈ U` (`ha`, `hb`); `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` and evaluate at `z`.
#### Mathlib lemmas needed
- `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, `Complex.isPreconnected_compl_of_countable`
  (project HalfPeriods.lean), `PeriodPair.countable_lattice` (project), `Set.Countable.image`,
  `PeriodPair.analyticOnNhd_weierstrassP`, `AnalyticOnNhd.comp`, T020,
  `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`, `Filter.Tendsto.frequently`.
#### Sources
- Q6/Q20 (identity theorem step); template proof 40 lines → ~45 LOC.
#### Generality decision
- As stated (both non-membership hypotheses necessary).

### [T022] `mem_lattice_of_forall_weierstrassP_add_eq` (periods of ℘ are Λ)
- **Status**: done (finished 2026-09-10)
- **Progress**: transcription of `HalfPeriods.two_mul_mem_lattice_of_derivWeierstrassP_eq_zero` with `c` for `2 * z₀`; the symmetry input is `h (-w)` plus `weierstrassP_neg`.
- **File**: J
- **Depends on**: none
- **Parallel**: yes
- **Type**: theorem

#### Statement
```lean
theorem mem_lattice_of_forall_weierstrassP_add_eq {c : ℂ}
    (h : ∀ z, z ∉ L.lattice → z + c ∉ L.lattice → ℘[L] (z + c) = ℘[L] z) : c ∈ L.lattice := by
  sorry
```
#### Proof sketch
Transcribe `PeriodPair.two_mul_mem_lattice_of_derivWeierstrassP_eq_zero`
(`HalfPeriods.lean:227–247`) with `c` in place of `2 * z₀` and `h` in place of the symmetry:
1. `by_contra hc`.
2. `hnear : {w | c - w ∉ L.lattice} ∈ 𝓝 0` (continuity of `w ↦ c - w`, open complement, `hc`
   at `w = 0`: `c - 0 = c ∉ Λ`).
3. `hev : ℘[L] =ᶠ[𝓝[≠] 0] fun w ↦ ℘[L] (c - w)`: for `w ∉ Λ` (`eventually_notMem_lattice`,
   project Uniqueness.lean:56) with `c - w ∉ Λ`, apply `h (-w) (neg_mem_iff…) (by
   simpa [neg_add_eq_sub] using …)` and `weierstrassP_neg`: `℘ (c - w) = ℘ (-w + c) = ℘ (-w) = ℘ w`.
4. `meromorphicOrderAt ℘ 0 = -2` (`L.order_weierstrassP 0 (zero_mem _)`) versus
   `0 ≤ meromorphicOrderAt (fun w ↦ ℘ (c - w)) 0` (`AnalyticAt.meromorphicOrderAt_nonneg`, from
   `analyticOnNhd_weierstrassP _ hc` composed with `fun_prop`); `meromorphicOrderAt_congr hev`;
   `decide`/`absurd`.
#### Mathlib lemmas needed
- `PeriodPair.order_weierstrassP` (`Weierstrass.lean:921`), `meromorphicOrderAt_congr`
  (`Meromorphic/Order.lean:277`), `AnalyticAt.meromorphicOrderAt_nonneg` (`:308`),
  `PeriodPair.eventually_notMem_lattice` (project), `PeriodPair.weierstrassP_neg`,
  `PeriodPair.analyticOnNhd_weierstrassP`, `Submodule.neg_mem_iff`.
#### Sources
- Q18 (pole of order 2), Q20; statement classical (Q1: "periodic with respect to a lattice Λ").
  Template proof 21 lines → ~25 LOC.
#### Generality decision
- As stated; `c = 0` handled by the same proof (`0 ∈ Λ` makes `by_contra` immediate).

### [CLEANUP-10] Run /cleanup on J (after T020–T022)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)
  **Type**: cleanup
- **Description**: per-file cadence cleanup. Check whether `HalfPeriods.lean`'s three specific
  lemmas can now be one-line corollaries of T020–T022 (`a := z₀`, `b := -z₀`); if so, record a
  follow-up (do not edit HalfPeriods.lean in this ticket).

### [T023] `sub_mem_lattice_of_weierstrassP_eq_of_derivWeierstrassP_eq` (AG2)
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched, three lines.
- **File**: J
- **Depends on**: T021, T022, CLEANUP-10
- **Parallel**: yes
- **Type**: theorem (API gap AG2)

#### Statement
```lean
theorem sub_mem_lattice_of_weierstrassP_eq_of_derivWeierstrassP_eq {a b : ℂ} (ha : a ∉ L.lattice)
    (hb : b ∉ L.lattice) (h₁ : ℘[L] a = ℘[L] b) (h₂ : ℘'[L] a = ℘'[L] b) :
    a - b ∈ L.lattice := by sorry
```
#### Proof sketch
1. `apply L.mem_lattice_of_forall_weierstrassP_add_eq` (T022); `intro z hz hz'`.
2. `have := L.weierstrassP_add_eq_add_of_eq ha hb h₁ h₂ (z := z - b) ?_ ?_` (T021) with
   `a + (z - b) = z + (a - b)` and `b + (z - b) = z` (`ring`-rewrites), hence the two
   non-membership side goals are `hz'` and `hz` after `rw`.
3. `simpa [show a + (z - b) = z + (a - b) by ring, show b + (z - b) = z by ring] using this`.
#### Mathlib lemmas needed
- T021, T022, `ring_nf`/`show … by ring`.
#### Sources
- Q11 (statement: zeros of ℘(z) − ℘(y) are z ≡ ±y; with ℘′ equal, the sign is +), Q13, Q20.
#### Generality decision
- Arbitrary `PeriodPair`.

### [T024] `weierstrassP_eq_iff`
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched; `sq_eq_sq_iff_eq_or_eq_neg` exists and applies over ℂ.
- **File**: J
- **Depends on**: T023
- **Parallel**: yes
- **Type**: theorem

#### Statement
```lean
theorem weierstrassP_eq_iff {a b : ℂ} (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) :
    ℘[L] a = ℘[L] b ↔ a - b ∈ L.lattice ∨ a + b ∈ L.lattice := by sorry
```
#### Proof sketch
- (→) `intro h`; `have hsq : ℘'[L] a ^ 2 = ℘'[L] b ^ 2 := by rw [L.derivWeierstrassP_sq a ha,
  L.derivWeierstrassP_sq b hb, h]`; `rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'`;
  left: `exact Or.inl (L.sub_mem_lattice_of_… ha hb h h')`; right: `℘ a = ℘ (-b)`
  (`weierstrassP_neg`), `℘' a = ℘' (-b)` (`derivWeierstrassP_neg`, `h'`), `-b ∉ Λ`
  (`neg_mem_iff`), so `a - (-b) = a + b ∈ Λ` by T023: `Or.inr (by simpa [sub_neg_eq_add] using …)`.
- (←) `rintro (h | h)`: `℘ a = ℘ (b + (a - b)) = ℘ b` (`weierstrassP_add_coe b ⟨_, h⟩` after
  `show a = b + (a - b) by ring`); or `℘ a = ℘ (-b + (a + b)) = ℘ (-b) = ℘ b`.
#### Mathlib lemmas needed
- T023, `PeriodPair.derivWeierstrassP_sq`, `sq_eq_sq_iff_eq_or_eq_neg`, `PeriodPair.weierstrassP_neg`,
  `PeriodPair.derivWeierstrassP_neg`, `PeriodPair.weierstrassP_add_coe`, `Submodule.neg_mem_iff`.
#### Sources
- Q11 verbatim; Q8; decomposition AG2.4.
#### Generality decision
- Arbitrary `PeriodPair`.

### [CLEANUP-11] Run /cleanup on J (final)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)

### [T025] `weierstrassPoint` API
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched; `linear_combination (derivWeierstrassP_sq …) / 4` for the equation.
- **File**: L
- **Depends on**: T009
- **Parallel**: yes
- **Type**: API lemmas (definition `weierstrassPoint` in place)

#### Statement
```lean
lemma weierstrassPoint_add_coe (z : ℂ) (l : L.lattice) :
    L.weierstrassPoint (z + l) = L.weierstrassPoint z := by sorry

lemma weierstrassPoint_mem_affineNonTwoTorsion {z : ℂ} (hz : 2 * z ∉ L.lattice) :
    L.weierstrassPoint z ∈ L.weierstrassCurve.affineNonTwoTorsion := by sorry

lemma hasDerivAt_weierstrassPoint {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassPoint (℘'[L] z, (6 * ℘[L] z ^ 2 - L.g₂ / 2) / 2) z := by sorry

lemma invariantDifferential_weierstrassPoint (z : ℂ) (v : ℂ × ℂ) :
    L.weierstrassCurve.invariantDifferential (L.weierstrassPoint z) v = v.1 / ℘'[L] z := by
  sorry
```
#### Proof sketch
- `_add_coe`: `simp [weierstrassPoint, L.weierstrassP_add_coe, L.derivWeierstrassP_add_coe]`.
- `_mem_…`: `have hz' : z ∉ L.lattice := fun h ↦ hz (by simpa [two_mul] using add_mem h h)`;
  `refine ⟨?_, ?_⟩`; equation: `rw [Affine.equation_iff]; simp [weierstrassCurve,
  weierstrassPoint]; linear_combination (L.derivWeierstrassP_sq z hz') / 4` (LeanBridge
  `weierstrassCurve_equation`); non-torsion: `simp [weierstrassCurve, weierstrassPoint]` reduces
  to `℘'[L] z ≠ 0`, i.e. `(L.derivWeierstrassP_eq_zero_iff hz').not.mpr hz`.
- `hasDerivAt`: `(L.hasDerivAt_weierstrassP hz).prodMk ((L.hasDerivAt_derivWeierstrassP hz).div_const 2)`.
- `invariantDifferential_…`: `simp [invariantDifferential_apply, weierstrassCurve,
  weierstrassPoint]`; the denominator is `2 * (℘' z / 2) + 0 * ℘ z + 0 = ℘' z`
  (`mul_div_cancel₀`, `two_ne_zero`), `congr 1; ring`.
#### Mathlib lemmas needed
- `PeriodPair.weierstrassP_add_coe`, `derivWeierstrassP_add_coe`, `derivWeierstrassP_sq`,
  `WeierstrassCurve.Affine.equation_iff`, `PeriodPair.derivWeierstrassP_eq_zero_iff` (project
  HalfPeriods), `PeriodPair.hasDerivAt_weierstrassP`, `hasDerivAt_derivWeierstrassP` (project),
  `HasDerivAt.prodMk`, `HasDerivAt.div_const`, T009, `mul_div_cancel₀`.
#### Sources
- Q13 ("It is certainly a well-defined map"), Q7, Q6; LeanBridge `NonSlop/uniformisation.lean`
  (`weierstrassCurve_equation`, `toPoint`); decomposition L3a.7–L3a.10.
#### Generality decision
- Arbitrary `PeriodPair`; `_mem_…` needs `2z ∉ Λ` (exactly the non-2-torsion condition).

### [T026] `hasStrictDerivAt_weierstrassP`
- **Status**: done (finished 2026-09-10)
- **Progress**: `AnalyticAt.hasStrictDerivAt` then `rwa [(hasDerivAt_weierstrassP hz).deriv]`.
- **File**: L
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma hasStrictDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasStrictDerivAt ℘[L] (℘'[L] z) z := by sorry
```
#### Proof sketch
1. `have h := (L.analyticOnNhd_weierstrassP z hz).hasStrictDerivAt` — a `HasStrictDerivAt ℘ (deriv ℘ z) z`.
2. Identify the derivative: `(L.hasDerivAt_weierstrassP hz).deriv ▸ h` or
   `h.hasDerivAt.unique (L.hasDerivAt_weierstrassP hz) ▸ h`.
#### Mathlib lemmas needed
- `AnalyticAt.hasStrictDerivAt` (`FDeriv/Analytic.lean:147`), `PeriodPair.analyticOnNhd_weierstrassP`,
  `PeriodPair.hasDerivAt_weierstrassP` (project), `HasDerivAt.unique`, `HasDerivAt.deriv`.
#### Sources
- Q18 (analytic off the lattice); decomposition L4.0f.
#### Generality decision
- Arbitrary `PeriodPair`.

### [T027] `lift` basics
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched once T027a existed; `Path.extend_range` gives `γ.extend u ∈ range γ`.
- **Depends on**: T009, T027a
- **Progress**: 2026-09-10: spawned T027a — the sketch's `integral_hasDerivWithinAt_right` is
  gated on an `FTCFilter` instance for `Icc`, and Mathlib has only four instances (`pure`, `𝓝`,
  `𝓝[≤]`, `𝓝[≥]`), none for a closed interval. Paused at the `hasDerivWithinAt_lift` step.
- **File**: L
- **Depends on**: T009
- **Parallel**: yes
- **Type**: API lemmas (definition `lift` in place)

#### Statement
```lean
@[simp]
lemma lift_zero (z₀ : ℂ) : L.lift γ z₀ 0 = z₀ := by sorry

lemma lift_one (z₀ : ℂ) :
    L.lift γ z₀ 1 = z₀ + ∫ᶜ x in γ, L.weierstrassCurve.invariantDifferential x := by sorry

lemma continuousOn_curveIntegralFun_invariantDifferential :
    ContinuousOn (curveIntegralFun L.weierstrassCurve.invariantDifferential γ) I := by sorry

lemma hasDerivWithinAt_lift (z₀ : ℂ) {t : ℝ} (ht : t ∈ I) : HasDerivWithinAt (L.lift γ z₀)
    (curveIntegralFun L.weierstrassCurve.invariantDifferential γ t) I t := by sorry

lemma continuousOn_lift (z₀ : ℂ) : ContinuousOn (L.lift γ z₀) I := by sorry
```
(the last three are under `variable (hγ : ContDiffOn ℝ 1 γ.extend I) (hS : range γ ⊆
L.weierstrassCurve.affineNonTwoTorsion)` with `include hγ hS`.)
#### Proof sketch
- `lift_zero`: `simp [lift, intervalIntegral.integral_same]`.
- `lift_one`: `rw [lift, curveIntegral_def']` (definitional; `rfl` after unfolding).
- `continuousOn_curveIntegralFun_…`: copy Mathlib's proof of
  `ContinuousOn.curveIntegrable_of_contDiffOn` (`Basic.lean:334`) minus the last step:
  `simp only [funext (curveIntegralFun_def _ γ)]; apply ContinuousOn.clm_apply`;
  `· exact (L.weierstrassCurve.continuousOn_invariantDifferential).comp (by fun_prop :
  ContinuousOn γ.extend I)?` — the form is continuous on the locus (T009) and `γ.extend t ∈
  locus` for `t ∈ I` (`hS`, `Path.extend_extends'`/`extend_range`), use `ContinuousOn.comp` with
  `MapsTo`; `· exact hγ.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl`.
- `hasDerivWithinAt_lift`: `lift γ z₀ = fun t ↦ z₀ + ∫ u in 0..t, f u`;
  `(intervalIntegral.integral_hasDerivWithinAt_right (hf.intervalIntegrable …)
  (hf.stronglyMeasurableAtFilter …) (hf t ht).continuousWithinAt).const_add z₀` — check the exact
  hypotheses of `integral_hasDerivWithinAt_right` (`FundThmCalculus.lean:867`): it needs
  `IntervalIntegrable f volume 0 t`, a `StronglyMeasurableAtFilter f (𝓝[I] t)` and
  `ContinuousWithinAt f I t`; all follow from `ContinuousOn f I` (`ContinuousOn.intervalIntegrable`
  on `uIcc 0 t ⊆ I`, `ContinuousOn.stronglyMeasurableAtFilter`).
- `continuousOn_lift`: `fun t ht ↦ (L.hasDerivWithinAt_lift γ hγ hS z₀ ht).continuousWithinAt`.
#### Mathlib lemmas needed
- `intervalIntegral.integral_same` (`IntervalIntegral/Basic.lean:681`), `curveIntegral_def'`,
  `curveIntegralFun_def`, `ContinuousOn.clm_apply` (`BoundedLinearMaps.lean:475`),
  `ContDiffOn.continuousOn_derivWithin` (`ContDiff/Deriv.lean:72`), `uniqueDiffOn_Icc`,
  `intervalIntegral.integral_hasDerivWithinAt_right` (`FundThmCalculus.lean:867`),
  `ContinuousOn.intervalIntegrable`, `ContinuousOn.stronglyMeasurableAtFilter`,
  `HasDerivWithinAt.const_add`, `HasDerivWithinAt.continuousWithinAt`, `Path.extend_extends'`.
#### Sources
- Q17 (definition of the curve integral), Q6 (the lift is the elliptic integral); decomposition L4.0.
#### Generality decision
- Any path `γ : Path p q` (not only loops), arbitrary `PeriodPair`.

### [T027a] Fundamental theorem of calculus on a closed interval
- **Status**: done (finished 2026-09-10)
- **Progress**: proved as planned: three branches (`t = a` via `Icc =ᶠ Ici`, `t = b` via `Icc =ᶠ Iic`, interior via `Icc ∈ 𝓝 t`). Note `integral_hasDerivWithinAt_left` differentiates in the **lower** limit — both endpoint branches use `_right` and differ only in the set. Needs `[CompleteSpace E]`.
- **File**: `FormalConjecturesForMathlib/MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean` (new)
- **Depends on**: none
- **Parent**: T027
- **Parallel**: no
- **Type**: lemma

#### Statement
```lean
theorem intervalIntegral.integral_hasDerivWithinAt_Icc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Set.Icc a b))
    {t : ℝ} (ht : t ∈ Set.Icc a b) :
    HasDerivWithinAt (fun u ↦ ∫ x in a..u, f x) (f t) (Set.Icc a b) t := by sorry
```

#### Proof sketch
Mathlib's `intervalIntegral.integral_hasDerivWithinAt_right` is gated on the `FTCFilter` class,
which has only four real instances (`pure`, `𝓝`, `𝓝[≤]`, `𝓝[≥]`) — **none for `Icc`**. Assemble
the closed-interval form by case-splitting on `t`, using that `HasDerivWithinAt` depends on `s`
only through `𝓝[s] t`:

1. `t = a`: `Icc a b =ᶠ[𝓝 a] Ici a` (they agree on `Iio b ∈ 𝓝 a`), so `hasDerivWithinAt_congr_set`
   reduces to the `𝓝[≥]` instance.
2. `t = b`: `Icc a b =ᶠ[𝓝 b] Iic b`, reducing to the `𝓝[≤]` instance.
3. `a < t < b`: `Icc a b ∈ 𝓝 t`, so `𝓝[Icc a b] t = 𝓝 t` and the `𝓝` instance applies;
   `ContinuousWithinAt f (Icc a b) t` upgrades by `ContinuousWithinAt.continuousAt`.

Side conditions per branch: `IntervalIntegrable f volume a t` (`ContinuousOn.intervalIntegrable`
after `Set.uIcc_subset_Icc`), a `StronglyMeasurableAtFilter` obligation
(`ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin` plus `nhdsWithin_le_iff` to move from
`𝓝[Icc a b] t` to the one-sided filter), and a `ContinuousWithinAt` obligation
(`ContinuousWithinAt.mono_of_mem_nhdsWithin`).

#### Mathlib lemmas needed
- `intervalIntegral.integral_hasDerivWithinAt_right`, `hasDerivWithinAt_congr_set`,
  `ContinuousOn.intervalIntegrable`, `Set.uIcc_subset_Icc`,
  `ContinuousOn.stronglyMeasurableAtFilter_nhdsWithin`, `nhdsWithin_le_iff`,
  `ContinuousWithinAt.mono_of_mem_nhdsWithin`, `ContinuousWithinAt.continuousAt`,
  `Ioo_mem_nhdsGT`, `Ioo_mem_nhdsLT`, `Icc_mem_nhds`.

#### Sources
- Inherited from T027 (Q17); a pure Mathlib-gap bridge, no external source.

#### Generality decision
- Any real Banach space `E` (matches `intervalIntegral`); `a < b` is needed for the endpoint
  `=ᶠ` arguments. Minimal — exactly the use site in T027.

### [CLEANUP-12] Run /cleanup on L (after T025–T027)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)
  **Type**: cleanup

### [T028] `isClosed_setOf_weierstrassPoint_lift_eq`
- **Status**: done (finished 2026-09-10)
- **Progress**: filter proof rather than sequences: `closure_subset_iff_isClosed`, `mem_closure_iff_nhdsWithin_neBot`, then `not_tendsto_nhds_of_tendsto_atTop` for the pole contradiction and `tendsto_nhds_unique` for the equation.
- **File**: L
- **Depends on**: T016, T025, T027, CLEANUP-12
- **Parallel**: yes (with T029)
- **Type**: lemma

#### Statement
```lean
lemma isClosed_setOf_weierstrassPoint_lift_eq (z₀ : ℂ) : IsClosed
    ({t | L.lift γ z₀ t ∉ L.lattice ∧ L.weierstrassPoint (L.lift γ z₀ t) = γ.extend t} ∩ I) := by
  sorry
```
#### Proof sketch
Sequential closedness in `ℝ`: `rw [← isSeqClosed_iff_isClosed]; intro u t hu hut` (or
`isClosed_of_closure_subset` + `mem_closure_iff_seq_limit`). Let `hu n : u n ∈ s ∩ I`.
1. `t ∈ I`: `isClosed_Icc.mem_of_tendsto hut (Eventually.of_forall fun n ↦ (hu n).2)`.
2. `lift u n → lift t`: `((L.continuousOn_lift γ hγ hS z₀).continuousWithinAt ht).tendsto.comp`
   with `tendsto_nhdsWithin_iff.mpr ⟨hut, Eventually.of_forall (fun n ↦ (hu n).2)⟩`.
3. `lift t ∉ Λ`: `by_contra hmem`; then `℘ (lift (u n)) → cobounded` by T016 (`hmem`) composed
   with the sequence (which is eventually `≠ lift t`? — careful: if `lift (u n) = lift t ∈ Λ` for
   some `n` that contradicts `(hu n).1.1`; so `lift (u n) ≠ lift t` for all `n`, and
   `tendsto_nhdsWithin_iff` applies). But `℘ (lift (u n)) = (γ.extend (u n)).1 → (γ.extend t).1`
   (from `(hu n).1.2` and `Path.continuous_extend`), a convergent hence bounded sequence: contradiction
   via `tendsto_norm_atTop_iff_cobounded` and `Filter.Tendsto.isBoundedUnder_le`/
   `not_tendsto_atTop_of_tendsto_nhds`.
4. Equation at `t`: `weierstrassPoint` is continuous at `lift t` (T025 `hasDerivAt_weierstrassPoint
   … |>.continuousAt`), so `weierstrassPoint (lift (u n)) → weierstrassPoint (lift t)`; also
   `= γ.extend (u n) → γ.extend t`; `tendsto_nhds_unique`.
#### Mathlib lemmas needed
- `isSeqClosed_iff_isClosed` / `IsSeqClosed`, `isClosed_Icc`, `IsClosed.mem_of_tendsto`,
  `tendsto_nhdsWithin_iff`, `Filter.Tendsto.comp`, T016, `tendsto_norm_atTop_iff_cobounded`,
  `not_tendsto_atTop_of_tendsto_nhds`, `Path.continuous_extend`, `tendsto_nhds_unique`, T025, T027.
#### Sources
- Q13 (properness of the covering), Q18 (pole); decomposition L4.1.
#### Generality decision
- Any path; `hγ`, `hS` via `continuousOn_lift`.

### [T029] `exists_localLift`
- **Status**: done (finished 2026-09-10)
- **Progress**: the big one. Traps: (i) `HasStrictDerivAt` unfolds to `HasFDerivAtFilter`, so `.continuousAt` needs `.hasDerivAt.continuousAt`; (ii) `ContinuousAt.comp` mis-unifies `g ∘ f` — pin with `(f := …) (x := …)`; (iii) goals from `Tendsto.eventually` are beta-unreduced — use `show`; (iv) the curve-equation coefficient is `-4`, not `4`; (v) the composite's `NormedSpace ℝ ℂ` instance came out on a different path from the goal's (`InnerProductSpace.complexToReal` vs `NormedAlgebra`) — fixed by ascribing the type in a `have` so the defeq check runs at default transparency.
- **File**: L
- **Depends on**: T006, T025, T026, T027, CLEANUP-12
- **Parallel**: yes (with T028)
- **Type**: lemma (shared-witness existential — documented exception)

#### Statement
```lean
lemma exists_localLift {t : ℝ} (ht : t ∈ I) {w : ℂ} (hw : w ∉ L.lattice)
    (heq : L.weierstrassPoint w = γ.extend t) : ∃ v : ℝ → ℂ, v t = w ∧
      ∀ᶠ u in 𝓝 t, (v u ∉ L.lattice ∧ L.weierstrassPoint (v u) = γ.extend u) ∧
        ∀ hu : u ∈ I, HasDerivWithinAt v
          (curveIntegralFun L.weierstrassCurve.invariantDifferential γ u) I u := by sorry
```
#### Proof sketch
Let `X u := (γ.extend u).1`, `Y u := (γ.extend u).2` (continuous, `Path.continuous_extend`).
1. `℘' w ≠ 0`: from `heq`, `℘' w / 2 = Y t` and `Y t ≠ 0`… more precisely `γ.extend t ∈ locus`
   (`hS`, `Path.extend_extends'` with `ht`), whose second conjunct is `2 * Y t + 0 + 0 ≠ 0`
   (`simp [weierstrassCurve]`), so `℘' w = 2 * Y t ≠ 0`.
2. `hs := L.hasStrictDerivAt_weierstrassP hw` (T026); `ψ := hs.localInverse ℘[L] (℘'[L] w) w h0`;
   `refine ⟨fun u ↦ ψ (X u), ?_, ?_⟩`.
3. `v t = ψ (℘ w) = w`: `heq ▸`? — `X t = ℘ w` from `heq` (`Prod.mk.inj`), and
   `HasStrictFDerivAt.localInverse_apply_image` (`FDeriv.lean:161`; the `HasStrictDerivAt` abbrev
   unfolds to the FDeriv version: `hs.hasStrictFDerivAt_equiv h0`).
4. Eventual properties — assemble with `Filter.Eventually.and`, each from `𝓝 t`:
   (a) `℘ (v u) = X u` and `v u` near `w`: `hs.eventually_right_inverse` pulled back by
       `(continuous_fst.comp γ.continuous_extend).continuousAt.tendsto` (`Tendsto.eventually`),
       plus `Tendsto (fun u ↦ ψ (X u)) (𝓝 t) (𝓝 w)` from `HasStrictFDerivAt.localInverse_continuousAt`
       (`FDeriv.lean:169`) composed with `X u → X t = ℘ w`.
   (b) `v u ∉ Λ`: `(L.isClosed_lattice.isOpen_compl.mem_nhds hw)` pulled back along (a)'s tendsto.
   (c) sign-lock: apply T006 with `f u := ℘'[L] (v u)`, `g u := 2 * Y u`, at `a := t`:
       `hf` (continuity of `℘'` at `w` — `(L.hasDerivAt_derivWeierstrassP hw).continuousAt`
       composed with the tendsto of `v`), `hg` (continuity), `h : ℘' w = 2 * Y t` (from `heq`),
       `h0`, and `hsq : ∀ᶠ u, ℘' (v u) ^ 2 = (2 Y u) ^ 2`: for `u` with (a),(b) and `γ.extend u ∈
       locus` (need `u ∈ I`?? — `hS` only gives points of the *range*, i.e. `γ.extend u` for
       `u ∈ I`; for `u ∉ I`, `γ.extend u = γ.extend (projIcc …)` is still in the range
       (`Path.extend_range : range γ.extend = range γ`, `Path.lean:226`) ✓ so `∀ u`, `γ.extend u ∈
       locus`): `℘'(v u)² = 4℘(v u)³ − g₂℘(v u) − g₃ = 4X³ − g₂X − g₃ = (2Y)²` using
       `derivWeierstrassP_sq` (with (b)), (a), and the short-curve `Equation` at `(X u, Y u)`
       (`Affine.equation_iff`, `simp [weierstrassCurve]`, `linear_combination 4 * hEq`).
       Conclude `∀ᶠ u, ℘' (v u) = 2 * Y u`.
   (d) derivative: for `u` near `t` with `hu : u ∈ I`: `HasStrictDerivAt ψ (℘' (v u))⁻¹ (X u)`
       by `HasStrictDerivAt.to_local_left_inverse` applied to
       `L.hasStrictDerivAt_weierstrassP (v u ∉ Λ)` with `hg : ∀ᶠ x in 𝓝 (v u), ψ (℘ x) = x`
       (from `hs.eventually_left_inverse`, valid near `w`, and `v u` near `w` by (a) — use
       `Filter.Eventually.filter_mono`/`eventually_nhds_iff` to transport; then note
       `℘ (v u) = X u` by (a) to place the derivative at `X u`). Chain rule with
       `HasDerivWithinAt X (derivWithin γ.extend I u).1 I u` (from
       `(hγ.differentiableOn le_rfl u hu).hasDerivWithinAt` and `HasDerivWithinAt.fst`?? — use
       `hasDerivWithinAt_fst`/`ContinuousLinearMap.fst.hasFDerivAt.comp_hasDerivWithinAt`):
       `(hψ.hasDerivAt.comp_hasDerivWithinAt u hX)` gives derivative
       `(℘' (v u))⁻¹ * (derivWithin γ.extend I u).1`; rewrite with (c) and
       `curveIntegralFun_def`, `invariantDifferential_apply`, `weierstrassCurve` coefficients:
       `curveIntegralFun ω γ u = (derivWithin γ.extend I u).1 / (2 * Y u + 0 + 0)`; `field_simp`/
       `div_eq_inv_mul`.
#### Mathlib lemmas needed
- T006, T026, T025, `HasStrictDerivAt.localInverse`, `.eventually_right_inverse`,
  `.eventually_left_inverse`, `.to_local_left_inverse` (`InverseFunctionTheorem/Deriv.lean:33–60`),
  `HasStrictFDerivAt.localInverse_apply_image` (`FDeriv.lean:161`),
  `HasStrictFDerivAt.localInverse_continuousAt` (`:169`), `Path.continuous_extend`,
  `Path.extend_range` (`Path.lean:226`), `PeriodPair.derivWeierstrassP_sq`,
  `PeriodPair.hasDerivAt_derivWeierstrassP`, `PeriodPair.isClosed_lattice`,
  `HasStrictDerivAt.hasDerivAt`, `HasDerivAt.comp_hasDerivWithinAt`, `ContDiffOn.differentiableOn`,
  `HasDerivWithinAt.fst`?? (verify; else `hasFDerivWithinAt` + `ContinuousLinearMap.fst`),
  `curveIntegralFun_def`, `WeierstrassCurve.Affine.equation_iff`.
#### Sources
- Q13 ("a local isomorphism except at the four listed points"), Q6 (the ODE and the `±`
  ambiguity resolved by continuity), Q7/Q16 (℘′ ≠ 0 off half-periods); decomposition L4.3
  (composition attack recorded: derivative of the local inverse at nearby points needs
  `to_local_left_inverse`). Source length: Q13 proof 8 lines, Q6 10 lines → this is the largest
  leaf; expect ~120 LOC.
#### Generality decision
- Any path `γ : Path p q`; the witness `v` is shared by all conjuncts (documented exception).

### [T030] `eventually_weierstrassPoint_lift_eq`
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched; `eq_of_derivWithin_eq` on `Icc t (t + d)` with `d := min (ε/2) ((1-t)/2)`, derivatives `mono`'d down from `I`.
- **File**: L
- **Depends on**: T027, T029
- **Parallel**: no
- **Type**: lemma

#### Statement
```lean
lemma eventually_weierstrassPoint_lift_eq (z₀ : ℂ) {t : ℝ} (ht : t ∈ I) (ht1 : t < 1)
    (hlift : L.lift γ z₀ t ∉ L.lattice) (heq : L.weierstrassPoint (L.lift γ z₀ t) = γ.extend t) :
    ∀ᶠ u in 𝓝[>] t, L.lift γ z₀ u ∉ L.lattice ∧
      L.weierstrassPoint (L.lift γ z₀ u) = γ.extend u := by sorry
```
#### Proof sketch
1. `obtain ⟨v, hvt, hv⟩ := L.exists_localLift γ hγ hS ht hlift heq` (T029).
2. From `hv : ∀ᶠ u in 𝓝 t, …` and `ht1` get `ε > 0` with `t + ε ≤ 1` and the properties on
   `Icc t (t + ε)` (`Metric.eventually_nhds_iff` / `eventually_nhds_iff`, shrink `ε`).
3. On `Icc t (t+ε) ⊆ I`, apply `eq_of_derivWithin_eq (a := t) (b := t + ε)` to `f := L.lift γ z₀`
   and `g := v`: `DifferentiableOn ℝ _ (Icc t (t+ε))` for both from the `HasDerivWithinAt … I u`
   facts (T027 `hasDerivWithinAt_lift`, T029's (d)) via `HasDerivWithinAt.mono` (`Icc t (t+ε) ⊆ I`)
   and `.differentiableWithinAt`; `EqOn (derivWithin f _) (derivWithin g _) (Ico t (t+ε))`: both
   equal `curveIntegralFun ω γ u` by `HasDerivWithinAt.derivWithin` with
   `uniqueDiffOn_Icc (by linarith)`; `f t = g t`: `hvt`.
4. Conclude on `Ioc t (t + ε) ∈ 𝓝[>] t` (`Ioc_mem_nhdsGT`): for such `u`, `lift u = v u`, so the
   two properties are T029's (a)/(b) for `u`.
#### Mathlib lemmas needed
- T029, T027, `eq_of_derivWithin_eq` (`Calculus/MeanValue.lean:386`), `HasDerivWithinAt.mono`,
  `HasDerivWithinAt.derivWithin`, `uniqueDiffOn_Icc`, `HasDerivWithinAt.differentiableWithinAt`,
  `Ioc_mem_nhdsGT`, `Metric.eventually_nhds_iff`.
#### Sources
- Q6 (uniqueness); decomposition L4.2 (attack: `ht1` needed).
#### Generality decision
- Any path.

### [CLEANUP-13] Run /cleanup on L (after T028–T030)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)
  **Type**: cleanup

### [T031] `weierstrassPoint_lift` and `lift_notMem_lattice`
- **Status**: done (finished 2026-09-10)
- **Progress**: `IsClosed.Icc_subset_of_forall_mem_nhdsWithin` with T028 and T030; both public lemmas project a `private lift_spec` conjunction.
- **File**: L
- **Depends on**: T028, T030, CLEANUP-13
- **Parallel**: no
- **Type**: theorem (assembly by continuous induction) + corollary

#### Statement
```lean
theorem weierstrassPoint_lift {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) (hp : L.weierstrassPoint z₀ = p)
    {t : ℝ} (ht : t ∈ I) : L.weierstrassPoint (L.lift γ z₀ t) = γ.extend t := by sorry

lemma lift_notMem_lattice {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) (hp : L.weierstrassPoint z₀ = p)
    {t : ℝ} (ht : t ∈ I) : L.lift γ z₀ t ∉ L.lattice := by sorry
```
#### Proof sketch
Prove one `private`/auxiliary statement `∀ t ∈ I, lift t ∉ Λ ∧ weierstrassPoint (lift t) =
γ.extend t` (or prove `weierstrassPoint_lift` with the conjunction inside and project):
1. `have key : Icc (0:ℝ) 1 ⊆ {t | L.lift γ z₀ t ∉ L.lattice ∧ L.weierstrassPoint (L.lift γ z₀ t)
   = γ.extend t} := IsClosed.Icc_subset_of_forall_mem_nhdsWithin
   (L.isClosed_setOf_weierstrassPoint_lift_eq γ hγ hS z₀) ⟨by simpa using hz₀, by simp [hp]⟩
   (fun x hx ↦ L.eventually_weierstrassPoint_lift_eq γ hγ hS z₀ hx.2.1?? …)` — the base point:
   `lift 0 = z₀` (`lift_zero`), `γ.extend 0 = p` (`Path.extend_zero`); the step: `x ∈ s ∩ Ico 0 1`
   gives `x ∈ I`, `x < 1`, and the two properties.
2. `exact (key ht).2` / `(key ht).1`.
#### Mathlib lemmas needed
- `IsClosed.Icc_subset_of_forall_mem_nhdsWithin` (`Order/IntermediateValue.lean:408`), T028, T030,
  T027 (`lift_zero`), `Path.extend_zero` (`Path.lean:218`).
#### Sources
- Q6, Q3 (23.6.36), Q16 ("the extension of u⁻¹ … equals the ℘-function"); decomposition L4.
#### Generality decision
- Any path; `hz₀`, `hp` exactly the data of a starting point over `γ 0`.

### [CLEANUP-14] Run /cleanup on L (final)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)
- **Description**: final cleanup for L; if `weierstrassPoint_lift`/`lift_notMem_lattice` share a
  private conjunction, keep it `private`.

### [T032] `exists_forall_two_mul_add_mul_notMem_lattice`
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched: `H := (·/2) '' Λ` countable; for `l ≠ 0` the ℝ-functional `φ z = (conj l * z).im` is constant along `z₀ + ℝl` because `(conj l * l).im = 0`, and `z₀ := I * c * l / (conj l * l)` realises any `c ∉ φ '' H`.
- **File**: WP
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma exists_forall_two_mul_add_mul_notMem_lattice (l : ℂ) :
    ∃ z₀ : ℂ, ∀ t : ℝ, 2 * (z₀ + t * l) ∉ L.lattice := by sorry
```
#### Proof sketch
`rcases eq_or_ne l 0 with rfl | hl`.
- `l = 0`: need `z₀` with `2 z₀ ∉ Λ`, i.e. `z₀ ∉ (fun z ↦ z / 2) '' Λ`; that image is countable
  (`L.countable_lattice.image _`), so `((L.countable_lattice.image _).dense_compl ℂ).nonempty`
  (`Set.Countable.dense_compl` with `𝕜 := ℂ`, `E := ℂ`; `Dense.nonempty`) gives `z₀`; unpack
  `Set.mem_image` (`z₀ = z/2 ↔ 2 z₀ = z`).
- `l ≠ 0`: `φ : ℂ → ℝ := fun z ↦ (conj l * z).im`; `S := φ '' ((fun z ↦ z / 2) '' Λ)` countable;
  pick `c ∉ S` (`(hS.dense_compl ℝ).nonempty`); `z₀ := Complex.I * c * l / ‖l‖ ^ 2`
  (so `conj l * z₀ = I * c * (conj l * l) / ‖l‖² = I * c`, using `Complex.mul_conj`/
  `Complex.normSq_eq_norm_sq`… `conj l * l = ‖l‖²` as complex: `Complex.conj_mul'`);
  then `φ (z₀ + t * l) = c + t * (conj l * l).im = c` (`(conj l * l).im = 0`, `Complex.mul_im`,
  `conj` lemmas); if `2 (z₀ + t l) ∈ Λ` then `z₀ + t l ∈ (·/2) '' Λ` and `c = φ (…) ∈ S`,
  contradiction.
#### Mathlib lemmas needed
- `PeriodPair.countable_lattice` (project), `Set.Countable.image`, `Set.Countable.dense_compl`
  (`Module/Cardinality.lean:131`), `Dense.nonempty`, `Complex.conj_mul'`/`Complex.mul_conj`,
  `Complex.normSq_eq_norm_sq`, `Complex.mul_im`, `Complex.conj_re/conj_im`, `Set.mem_image`.
#### Sources
- Q12/Q13 genericity ("fundamental domain … such that f has no zeros or poles on the boundary");
  decomposition L3a.1 (attack: `l = 0` separate).
#### Generality decision
- Arbitrary `l`, arbitrary `PeriodPair`.

### [T033] `weierstrassLoop` and its properties
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched. `AnalyticOnNhd.contDiffOn` needs a `UniqueDiffOn` argument — supplied by `IsOpen.uniqueDiffOn` on `Λᶜ`. `ContinuousAt.comp` again needed `(f := …) (x := …)`.
- **File**: WP
- **Depends on**: T025
- **Parallel**: yes
- **Type**: def obligations + API

#### Statement
```lean
def weierstrassLoop (z₀ l : ℂ) (h : ∀ t : ℝ, 2 * (z₀ + t * l) ∉ L.lattice) (hl : l ∈ L.lattice) :
    Path (L.weierstrassPoint z₀) (L.weierstrassPoint z₀) where
  toFun t := L.weierstrassPoint (z₀ + t * l)
  continuous_toFun := by sorry
  source' := by sorry
  target' := by sorry

lemma weierstrassLoop_extend (t : ℝ) (ht : t ∈ I) :
    (L.weierstrassLoop z₀ l h hl).extend t = L.weierstrassPoint (z₀ + t * l) := by sorry

lemma contDiffOn_weierstrassLoop_extend :
    ContDiffOn ℝ 1 (L.weierstrassLoop z₀ l h hl).extend I := by sorry

lemma range_weierstrassLoop_subset :
    range (L.weierstrassLoop z₀ l h hl) ⊆ L.weierstrassCurve.affineNonTwoTorsion := by sorry
```
#### Proof sketch
- `hz : ∀ t : ℝ, z₀ + t * l ∉ L.lattice := fun t hm ↦ h t (by simpa [two_mul] using add_mem hm hm)`.
- `continuous_toFun`: `continuous_iff_continuousAt.2 fun t ↦ ((L.hasDerivAt_weierstrassPoint
  (hz t)).continuousAt.comp (by fun_prop : Continuous fun t : I ↦ z₀ + (t : ℝ) * l).continuousAt)`
  — coercions `I → ℝ → ℂ` via `Complex.ofReal`.
- `source'`: `simp` (`(0:I) = 0`, `0 * l = 0`, `add_zero`).
- `target'`: `simp [L.weierstrassPoint_add_coe z₀ ⟨l, hl⟩]` after `one_mul`.
- `_extend`: `Path.extend_extends'`/`Set.IccExtend_of_mem` with `ht`.
- `contDiffOn`: `refine (ContDiffOn.congr ?_ fun t ht ↦ (L.weierstrassLoop_extend h hl t ht).symm)`
  hmm — direction: `ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : ∀ x ∈ s, f₁ x = f x) :
  ContDiffOn 𝕜 n f₁ s`. Smoothness of `t ↦ weierstrassPoint (z₀ + t l)` on `I`: `℘` and `℘'` are
  `AnalyticOnNhd ℂ` off Λ (Mathlib) hence `ContDiffOn ℂ ⊤` (`AnalyticOnNhd.contDiffOn`), restrict
  scalars (`ContDiffOn.restrict_scalars ℝ`), compose with the `ContDiff ℝ` map
  `t ↦ z₀ + (t : ℂ) * l` (`Complex.ofRealCLM.contDiff` + arithmetic, `fun_prop`), landing in
  `Λᶜ` (`hz`), then `ContDiffOn.prodMk` and `.div_const`; finally `.of_le le_top`.
- `range_subset`: `rintro _ ⟨t, rfl⟩; exact L.weierstrassPoint_mem_affineNonTwoTorsion (h t)`.
#### Mathlib lemmas needed
- T025, `Path.extend_extends'`, `Set.IccExtend_of_mem`, `ContDiffOn.congr` (`ContDiff/Defs.lean:565`),
  `AnalyticOnNhd.contDiffOn` (`:718`), `ContDiffOn.restrict_scalars` (`Operations.lean:1049`),
  `ContDiffOn.comp`, `ContDiffOn.prodMk`, `ContDiffOn.div_const`, `Complex.ofRealCLM`
  (`Complex/Basic.lean:321`), `PeriodPair.analyticOnNhd_weierstrassP`, `analyticOnNhd_derivWeierstrassP`.
#### Sources
- Q3, Q18; decomposition L3a.2–L3a.5.
#### Generality decision
- Arbitrary `PeriodPair`, any `l ∈ Λ`, any admissible `z₀`.

### [T034] `curveIntegral_weierstrassLoop`
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched: `EventuallyEq.deriv_eq` on `Ioo 0 1` to replace the loop's `extend` by the explicit line, `HasDerivAt.scomp` for the chain rule (derivative `l • (℘', …)`), then `Prod.smul_fst` + `div_self`. Integral via `integral_Ioc_eq_integral_Ioo` + `setIntegral_congr_fun`.
- **File**: WP
- **Depends on**: T033, T025
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma curveIntegral_weierstrassLoop :
    ∫ᶜ x in L.weierstrassLoop z₀ l h hl, L.weierstrassCurve.invariantDifferential x = l := by
  sorry
```
#### Proof sketch
1. `rw [curveIntegral_eq_intervalIntegral_deriv]` (`Basic.lean:144`): the integral is
   `∫ t in 0..1, ω (γ.extend t) (deriv γ.extend t)`.
2. Replace the integrand by the constant `l` on `Ioo 0 1` (`intervalIntegral.integral_congr_ae`
   restricted to `Ioo`, or `intervalIntegral.integral_congr` on `Ioo` via
   `integral_Ioc_eq_integral_Ioo`): for `t ∈ Ioo 0 1`, `γ.extend =ᶠ[𝓝 t] fun s ↦ weierstrassPoint
   (z₀ + s l)` (T033 `_extend` on the open set `Ioo 0 1 ∈ 𝓝 t`), so `deriv γ.extend t = deriv (fun
   s ↦ weierstrassPoint (z₀ + s l)) t` (`Filter.EventuallyEq.deriv_eq`, `Deriv/Basic.lean:641`)
   `= (℘' (z₀ + t l) * l, …)` by `(L.hasDerivAt_weierstrassPoint (hz t)).comp_ofReal`-style chain
   rule (`HasDerivAt.comp` with `t ↦ z₀ + t * l`, derivative `l`; `HasDerivAt.comp_ofReal`
   for the ℝ-parametrisation) and `HasDerivAt.deriv`. Then
   `ω (weierstrassPoint _) v = v.1 / ℘' _` (T025) `= ℘' _ * l / ℘' _ = l` (`mul_div_cancel_left₀`,
   `℘' ≠ 0` from `derivWeierstrassP_eq_zero_iff` and `h`).
3. `simp [intervalIntegral.integral_const]` — `(1 - 0) • l = l`.
#### Mathlib lemmas needed
- `curveIntegral_eq_intervalIntegral_deriv`, `intervalIntegral.integral_congr_ae` /
  `intervalIntegral.integral_Ioc_eq_integral_Ioo`, `Filter.EventuallyEq.deriv_eq`,
  `HasDerivAt.deriv`, `HasDerivAt.comp_ofReal`, `HasDerivAt.comp`, T025, T033,
  `PeriodPair.derivWeierstrassP_eq_zero_iff`, `mul_div_cancel_left₀`, `intervalIntegral.integral_const`.
#### Sources
- Q6 ($(dy/dz)^2 = 4y^3 - g_2 y - g_3$, so $d\wp/\wp' = dz$), Q3; decomposition L3a.6.
#### Generality decision
- As T033.

### [CLEANUP-15] Run /cleanup on WP (after T032–T034)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)
  **Type**: cleanup

### [T035] `mem_integralPeriodLattice_of_mem_lattice`
- **Status**: done (finished 2026-09-10)
- **Progress**: three lines, as sketched.
- **File**: WP
- **Depends on**: T004, T032, T034, CLEANUP-15
- **Parallel**: yes (with T036)
- **Type**: theorem

#### Statement
```lean
theorem mem_integralPeriodLattice_of_mem_lattice {l : ℂ} (hl : l ∈ L.lattice) :
    l ∈ L.weierstrassCurve.integralPeriodLattice := by sorry
```
#### Proof sketch
1. `obtain ⟨z₀, h⟩ := L.exists_forall_two_mul_add_mul_notMem_lattice l` (T032).
2. `rw [← L.curveIntegral_weierstrassLoop h hl]` (T034).
3. `exact curveIntegral_mem_curveIntegralPeriods _ (L.contDiffOn_weierstrassLoop_extend h hl)
   (L.range_weierstrassLoop_subset h hl)` (T004, T033) — `integralPeriodLattice` unfolds to
   `curveIntegralPeriods` (`WeierstrassCurve.integralPeriodLattice`, `Iff.rfl`).
#### Mathlib lemmas needed
- T004, T032, T033, T034.
#### Sources
- Q3, Q1; decomposition L3a.
#### Generality decision
- Arbitrary `PeriodPair`.

### [T036] `mem_lattice_of_mem_integralPeriodLattice`
- **Status**: done (finished 2026-09-10)
- **Progress**: as sketched. Trap: `rw [← hpt] at h1` fails with *motive is not type correct* because `p` occurs in `γ : Path p p`; use `h1.trans hpt.symm` instead. Curve-equation coefficient is `+4` here (the equation is being consumed, not produced).
- **File**: WP
- **Depends on**: T019, T023, T031, CLEANUP-15
- **Parallel**: yes (with T035)
- **Type**: theorem

#### Statement
```lean
theorem mem_lattice_of_mem_integralPeriodLattice {w : ℂ}
    (hw : w ∈ L.weierstrassCurve.integralPeriodLattice) : w ∈ L.lattice := by sorry
```
#### Proof sketch
1. `obtain ⟨p, γ, hγ, hS, rfl⟩ := hw` (`mem_integralPeriodLattice_iff`).
2. `have hp : p ∈ L.weierstrassCurve.affineNonTwoTorsion := hS ⟨0, γ.source⟩`
   (`Path.source_mem_range`, `Path.lean:124`).
3. From `hp`: `(2 * p.2) ^ 2 = 4 * p.1 ^ 3 - L.g₂ * p.1 - L.g₃`: `rw [mem_affineNonTwoTorsion,
   Affine.equation_iff] at hp; simp [weierstrassCurve] at hp; linear_combination 4 * hp.1`.
4. `obtain ⟨z₀, hz₀, hx, hy⟩ := L.exists_weierstrassP_eq_and_derivWeierstrassP_eq this` (T019);
   `have hpt : L.weierstrassPoint z₀ = p := Prod.ext hx (by simp [hy])` (`℘' z₀ / 2 = p.2`).
5. `have h1 := L.weierstrassPoint_lift γ hγ hS hz₀ hpt (t := 1) (by simp)` (T031):
   `weierstrassPoint (lift 1) = γ.extend 1 = p` (`Path.extend_one`); `have h1' :=
   L.lift_notMem_lattice γ hγ hS hz₀ hpt (t := 1) (by simp)`.
6. `have := L.sub_mem_lattice_of_weierstrassP_eq_of_derivWeierstrassP_eq h1' hz₀ ?_ ?_` (T023)
   with `℘ (lift 1) = ℘ z₀` and `℘' (lift 1) = ℘' z₀` read off from `h1 ▸ hpt.symm`
   (`Prod.mk.inj`, `div_left_inj' two_ne_zero`).
7. `rwa [L.lift_one, add_sub_cancel_left] at this` (T027 `lift_one`: `lift 1 − z₀ = ∫ᶜ`).
#### Mathlib lemmas needed
- T019, T023, T027, T031, `Path.source_mem_range`, `Path.extend_one` (`Path.lean:220`),
  `WeierstrassCurve.Affine.equation_iff`, `Prod.ext`, `Prod.mk.inj`, `add_sub_cancel_left`.
#### Sources
- Q13 (loops lift), Q6 (the lift is the integral), Q11 (endpoints congruent), Q4/Q12
  (starting point exists); decomposition L3b (composition attack recorded).
#### Generality decision
- Arbitrary `PeriodPair`.

### [T037] `integralPeriodLattice_weierstrassCurve` (assembly)
- **Status**: done (finished 2026-09-10)
- **Progress**: `Set.ext` assembly.
- **File**: WP
- **Depends on**: T035, T036
- **Parallel**: no
- **Type**: theorem (assembly)

#### Statement
```lean
theorem integralPeriodLattice_weierstrassCurve :
    L.weierstrassCurve.integralPeriodLattice = (L.lattice : Set ℂ) := by sorry
```
#### Proof sketch
`Set.ext fun w ↦ ⟨L.mem_lattice_of_mem_integralPeriodLattice, L.mem_integralPeriodLattice_of_mem_lattice⟩`
(coercion `SetLike.mem_coe`).
#### Mathlib lemmas needed
- T035, T036, `Set.ext`, `SetLike.mem_coe`.
#### Sources
- Q1, Q13; decomposition L3.
#### Generality decision
- Arbitrary `PeriodPair`.

### [CLEANUP-16] Run /cleanup on WP (final)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)

### [T038] `periodPair_weierstrassCurve`
- **Status**: done (finished 2026-09-10)
- **Progress**: `ext` on `WeierstrassCurve` then `simp only [weierstrassCurve, shortModel, periodPair_g₂, periodPair_g₃]` and `ring`.
- **File**: CP
- **Depends on**: none
- **Parallel**: yes
- **Type**: lemma

#### Statement
```lean
lemma periodPair_weierstrassCurve : W.periodPair.weierstrassCurve = W.shortModel := by sorry
```
#### Proof sketch
1. `ext` (`WeierstrassCurve.ext`) — five coefficient goals; `simp [PeriodPair.weierstrassCurve,
   shortModel]` closes `a₁ a₂ a₃`.
2. `a₄`: `rw [W.periodPair_g₂]; ring` (`-(W.c₄ / 12) / 4 = -W.c₄ / 48`); `a₆`: `rw
   [W.periodPair_g₃]; ring`.
#### Mathlib lemmas needed
- `WeierstrassCurve.ext`, `WeierstrassCurve.periodPair_g₂`, `periodPair_g₃` (project
  `PeriodLattice.lean`), `PeriodPair.weierstrassCurve` (project `Existence.lean`), `ring`.
#### Sources
- definitions (decomposition L1).
#### Generality decision
- `W : WeierstrassCurve ℂ`, `[W.IsElliptic]` (for `periodPair`).

### [CLEANUP-ALL-1] Run /cleanup-all on the project so far
- **Status**: open · **File**: all new files · **Depends on**: CLEANUP-1, -2, -3, -6, -7, -9,
  -11, -14, -16, T038 · **Parallel**: no · **Type**: cleanup-all
- **Description**: project-wide pass before the milestone: naming consistency across the ten
  files (`affineNonTwoTorsion`, `weierstrassPoint`, `weierstrassLoop`, `lift`,
  `integralPeriodLattice`), docstring cross-references (each file's module docstring names the
  others correctly), import minimisation, `#print axioms` on T019, T023, T031, T037.

### [T039] `integralPeriodLattice_eq` — MILESTONE
- **Status**: done (finished 2026-09-10)
- **Progress**: **MILESTONE** — three rewrites exactly as planned. `#print axioms WeierstrassCurve.integralPeriodLattice_eq` → propext, Classical.choice, Quot.sound.
- **File**: CP
- **Depends on**: T015, T037, T038, CLEANUP-ALL-1
- **Parallel**: no
- **Type**: theorem (milestone)

#### Statement
```lean
theorem integralPeriodLattice_eq : W.integralPeriodLattice = (W.periodPair.lattice : Set ℂ) := by
  sorry
```
#### Proof sketch
`rw [← W.integralPeriodLattice_shortModel, ← W.periodPair_weierstrassCurve,
W.periodPair.integralPeriodLattice_weierstrassCurve]` (T015, T038, T037).
Verify: `#print axioms WeierstrassCurve.integralPeriodLattice_eq` → only `propext`,
`Classical.choice`, `Quot.sound`.
#### Mathlib lemmas needed
- T015, T037, T038.
#### Sources
- Q1 (statement), Q13/Q16 (uniformisation), Q3/Q6 (periods as integrals); decomposition R.
#### Generality decision
- `W : WeierstrassCurve ℂ`, `[W.IsElliptic]`; equality of **sets** (not of period pairs — see
  `plan.md`).

### [T040] `exists_curveIntegral_eq_of_mem_lattice`
- **Status**: done (finished 2026-09-10)
- **Progress**: `mem_integralPeriodLattice_iff.mp` after rewriting with T039.
- **File**: CP
- **Depends on**: T039
- **Parallel**: no
- **Type**: theorem (corollary)

#### Statement
```lean
theorem exists_curveIntegral_eq_of_mem_lattice {l : ℂ} (hl : l ∈ W.periodPair.lattice) :
    ∃ (p : ℂ × ℂ) (γ : Path p p), ContDiffOn ℝ 1 γ.extend I ∧
      range γ ⊆ W.affineNonTwoTorsion ∧ ∫ᶜ x in γ, W.invariantDifferential x = l := by sorry
```
#### Proof sketch
`exact W.mem_integralPeriodLattice_iff.mp (W.integralPeriodLattice_eq ▸ hl)` (with
`SetLike.mem_coe`).
#### Mathlib lemmas needed
- T039, `WeierstrassCurve.mem_integralPeriodLattice_iff`, `SetLike.mem_coe`.
#### Sources
- Q3 (the two periods are integrals over two loops), Q2 (why nothing finer is needed).
#### Generality decision
- As T039. This is a shared-witness existential by nature (a loop and its properties).

### [CLEANUP-17] Run /cleanup on CP (final)
- **Status**: in_progress (dispatched to a /cleanup subagent 2026-09-10)

### [CLEANUP-FINAL] Run /cleanup-all on the whole project
- **Status**: open · **Depends on**: every other ticket · **Type**: cleanup-all
- **Description**: final pass; then `/pre-submit`. Also decide whether `HalfPeriods.lean`'s
  specialised lemmas should be re-derived from `Injective.lean` (follow-up recorded at
  CLEANUP-10), and whether the four PR #5370 files must stay byte-identical (they are untouched
  by this board; keep it so).

---

## Cadence check
Proof/definition tickets per file: M 3 (CLEANUP-1 after 3rd = final) · P 2 (CLEANUP-2 final) ·
T 1 (CLEANUP-3 final) · ID 7 (CLEANUP-4 after T009, CLEANUP-5 after T012, CLEANUP-6 final) ·
IPL 2 (CLEANUP-7) · S 4 (CLEANUP-8 after T018, CLEANUP-9 final) · J 5 (CLEANUP-10 after T022,
CLEANUP-11 final) · L 7 (CLEANUP-12 after T027, CLEANUP-13 after T030, CLEANUP-14 final) ·
WP 6 (CLEANUP-15 after T034, CLEANUP-16 after T037 = final) · CP 3 (CLEANUP-17 after T040 =
final). 40 proof tickets → ⌈40/3⌉ = 14 ≤ 17 per-file cleanups ✓; CLEANUP-ALL-1 before the
milestone T039 ✓; CLEANUP-FINAL last ✓.
