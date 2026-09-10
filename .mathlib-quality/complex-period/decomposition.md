# Decomposition: the period lattice of an elliptic curve over ℂ as integrals

## Skeleton location
Every lemma below exists as a `:= by sorry` declaration (file:line as of the skeleton commit on
2026-09-10). `lake build FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.ComplexPeriod
FormalConjecturesForMathlib.AlgebraicGeometry.EllipticCurve.RealPeriod` succeeded (3515 jobs) with
only `declaration uses 'sorry'` warnings — 61 sorries in 10 files:

| file (under `FormalConjecturesForMathlib/`) | lines | sorries |
|---|---|---|
| `MeasureTheory/Integral/CurveIntegral/Map.lean` (M) | 63 | 3 |
| `MeasureTheory/Integral/CurveIntegral/Periods.lean` (P) | 74 | 5 |
| `Topology/Algebra/Field.lean` (T) | 39 | 1 |
| `AlgebraicGeometry/EllipticCurve/InvariantDifferential.lean` (ID) | 163 | 10 |
| `AlgebraicGeometry/EllipticCurve/IntegralPeriodLattice.lean` (IPL) | 77 | 4 |
| `Analysis/SpecialFunctions/Elliptic/Weierstrass/Surjective.lean` (S) | 72 | 4 |
| `Analysis/SpecialFunctions/Elliptic/Weierstrass/Injective.lean` (J) | 86 | 5 |
| `Analysis/SpecialFunctions/Elliptic/Weierstrass/Lift.lean` (L) | 151 | 15 |
| `Analysis/SpecialFunctions/Elliptic/Weierstrass/Periods.lean` (WP) | 109 | 11 |
| `AlgebraicGeometry/EllipticCurve/ComplexPeriod.lean` (CP) | 82 | 3 |

Tool note: the `lean_loogle` / `lean_local_search` MCP tools were not available to the planner;
every "verified" citation below was checked by grepping the Mathlib v4.33.1 source under
`.lake/packages/mathlib` for the declaration, and every "counterexample search" is a grep of the
Mathlib and project sources for statements of the negated shape.

## Verbatim source quotes (referenced as Q1–Q20 below)

- **Q1** [LMFDB `ec.q.period_lattice`]: "For $E$ an elliptic curve defined over $\C$ by a
  Weierstrass equation with coefficients $a_1,a_2,a_3,a_4,a_6$, the period lattice of $E$ is the
  set $\Lambda$ of periods of the invariant differential $dx/(2y+a_1x+a_3)$, which is a discrete
  lattice of rank $2$ in $\C$. There is an isomorphism (of complex Lie groups)
  $\C/\Lambda \cong E(\C)$ defined in terms of the Weierstrass $\wp$-function."
- **Q2** [LMFDB `ec.period`]: "For a complex place given by an embedding $v:K\to\C$, we define
  $\Omega_v(E_v) = \int_{E_v(\C)} \omega_E\wedge\overline{\omega_E}$. In terms of a basis
  $[w_1,w_2]$ of the period lattice of $E_v$, where $\Im(w_2/w_1)>0$, we have
  $\Omega_v(E_v)=2\Im(\overline{w_1}w_2)$, which is double the covolume of the period lattice."
- **Q3** [DLMF 23.6.34–36]: "2ω₁ = ∫[e₁ to ∞] du/√[(u-e₁)(u-e₂)(u-e₃)] = ∫[e₃ to e₂]
  du/√[(e₁-u)(e₂-u)(u-e₃)]"; "2ω₃ = i∫[e₂ to e₁] du/√[(e₁-u)(u-e₂)(u-e₃)] = i∫[-∞ to e₃]
  du/√[(e₁-u)(e₂-u)(e₃-u)]"; "w = ∫[z to ∞] du/√(4u³-g₂u-g₃) = ½∫[z to ∞]
  du/√[(u-e₁)(u-e₂)(u-e₃)]" (23.6.36, with $z = \wp(w)$).
- **Q4** [Pas2017 Thm 1.2 and proof, p. 7]: "Theorem 1.2. An elliptic function with an empty
  irreducible set of poles is a constant function. An elliptic function with no poles in a cell,
  necessarily has no poles at all, as a pole outside a cell necessarily would have a congruent pole
  within the cell. Consequently, such a function is not just meromorphic, but rather it is
  analytic. Furthermore, an analytic function in a cell is necessarily bounded within the cell. A
  direct consequence of property (1.1) is that an analytic elliptic function is bounded everywhere.
  But a bounded analytic function is necessarily a constant function."
- **Q5** [Pas2017 Thm 1.3, p. 8]: "Theorem 1.3. the number of roots of the equation f(z) = z₀ in
  a cell is equal to the number of poles of f in a cell (weighted by their multiplicity),
  independently of the value of z₀."
- **Q6** [Pas2017 (1.30)–(1.32), pp. 12–13]: "In the following, we will deduce an integral
  formula for the inverse function of ℘. In order to do so, we define the function z(y) as
  z(y) := ∫_y^∞ 1/√(4t³−g₂t−g₃) dt. (1.31) Differentiating with respect to z one gets
  1 = −(dy/dz)·1/√(4y³−g₂y−g₃) ⇒ (dy/dz)² = 4y³−g₂y−g₃. We just showed that the general solution
  of this equation is y = ℘(z + z₀). … Substituting the above into the equation (1.31) yields the
  integral formula for Weierstrass elliptic function, z = ∫_{℘(z)}^∞ 1/√(4t³−g₂t−g₃) dt. (1.32)"
- **Q7** [Pas2017 (1.34)–(1.36), pp. 13–14]: "e₁ := ℘(ω₁), e₂ := ℘(ω₃), e₃ := ℘(ω₂). (1.34) …
  ℘′(ω₁) = ℘′(ω₂) = ℘′(ω₃) = 0. (1.35) Substituting a half-period into Weierstrass equation
  (1.29), we yield 4e_i³ − g₂e_i − g₃ = 0. (1.36)"
- **Q8** [Pas2017 p. 14]: "Since ℘ is an order two elliptic function, the complex numbers e₁, e₂
  and e₃ are the only ones appearing only once in a cell, whereas all other complex numbers appear
  twice."
- **Q9** [WW1927 §20.12 (IV)]: "(IV) Liouville's theorem. An elliptic function, f(z), with no
  poles in a cell is merely a constant. For if f(z) has no poles inside the cell, it is analytic
  (and consequently bounded) inside and on the boundary of the cell (§3·61 corollary ii); that is
  to say, there is a number K such that |f(z)| < K when z is inside or on the boundary of the
  cell. From the periodic properties of f(z) it follows that …"
- **Q10** [WW1927 §20.13]: "hence the number of zeros of f(z) − c is equal to the number of poles
  of f(z), which is independent of c; the required result is therefore established."
- **Q11** [WW1927, footnote to §20.31]: "The function ℘(z) − ℘(y), qua function of z, has double
  poles at points congruent to z = 0, and no other singularities; it therefore (§20·13) has only
  two irreducible zeros; and the points congruent to z = ±y therefore give all the zeros of
  ℘(z) − ℘(y)."
- **Q12** [Mil2006 Cor 2.2 and proof, p. 83]: "COROLLARY 2.2 A nonconstant doubly periodic
  function has at least two poles (or one double pole). PROOF. A holomorphic doubly periodic
  function is bounded on the closure of any fundamental domain (by compactness), and hence on the
  entire plane (by periodicity). It is therefore constant by Liouville's theorem."
- **Q13** [Mil2006 Prop 3.7 and proof, pp. 92–93]: "PROPOSITION 3.7 The map z ↦ (℘(z) : ℘′(z) :
  1), z ≠ 0; 0 ↦ (0 : 1 : 0) is an isomorphism of Riemann surfaces ℂ/Λ → E(Λ)(ℂ). PROOF. It is
  certainly a well-defined map. The function ℘(z) : ℂ/Λ → ℙ¹(ℂ) is 2 : 1 in a fundamental domain
  containing 0, except at the points ω₁/2, ω₂/2, (ω₁+ω₂)/2, where it is one-to-one. Therefore, ℘
  realizes ℂ/Λ as a covering of degree 2 of the Riemann sphere, and it is a local isomorphism
  except at the four listed points. Similarly, x/z realizes E(Λ)(ℂ) as a covering of degree 2 of
  the Riemann sphere, and it is a local isomorphism except at (0 : 1 : 0) and the three points
  where y = 0. It follows that ℂ/Λ → E(Λ)(ℂ) is an isomorphism outside the two sets of four
  points. A similar argument shows that it is a local isomorphism at the remaining four points."
- **Q14** [Mil2006 p. 88]: "Now ℘(z) − ℘(zᵢ) is also an even doubly periodic function. Since it
  has exactly two poles in a fundamental domain, it must have exactly two zeros there."
- **Q15** [Mil2006 III §1, p. 81]: "A lattice in ℂ is the subgroup generated by two complex
  numbers that are linearly independent over ℝ."
- **Q16** [Wikipedia, *Weierstrass elliptic function*]: "Now the map φ is bijective and
  parameterizes the elliptic curve" (§Relation to elliptic curves); "Then the extension of u⁻¹ to
  the complex plane equals the ℘-function" (§Motivation, $u(z) = \int_z^\infty ds/\sqrt{4s^3-g_2s-g_3}$);
  "℘ is an even function. That means ℘(z) = ℘(−z) for all z ∈ ℂ ∖ Λ" (§Properties); "the
  half-periods are zeros of ℘′" (§The constants e₁, e₂ and e₃).
- **Q17** [Mathlib `Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean`, module docstring]:
  "The integral `∫ᶜ x in γ, ω x` is defined as $\int_0^1 \omega(\gamma(t))(\gamma'(t))$. More
  precisely, we use `Path.extend γ t` instead of `γ t`, because both derivatives and
  `intervalIntegral` expect globally defined functions; `derivWithin γ.extend (Set.Icc 0 1) t`,
  not `deriv γ.extend t`, for the derivative, so that it takes meaningful values at `t = 0` and
  `t = 1`, even though this does not affect the integral." Also: "The definitions in this file
  make sense if the path is a piecewise $C^1$ curve."
- **Q18** [Mathlib `Weierstrass.lean` header]: "`PeriodPair.derivWeierstrassP_sq` :
  `℘'(z)² = 4 ℘(z)³ - g₂ ℘(z) - g₃`"; "`PeriodPair.order_weierstrassP`: `℘` has a pole of
  order 2 at each of the lattice points."; "`PeriodPair.analyticOnNhd_weierstrassP`: `℘` is
  analytic away from the lattice points."; "`PeriodPair.weierstrassP_add_coe`: The Weierstrass
  `℘`-function is periodic."; "`PeriodPair.weierstrassP_neg`: The Weierstrass `℘`-function is
  even."
- **Q19** [Mathlib `DivisionPolynomial/Basic.lean`, `Affine/Basic.lean`]:
  `lemma C_Ψ₂Sq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial` with `ψ₂ := W.toAffine.polynomialY`
  and "The univariate polynomial `Ψ₂Sq` congruent to `ψ₂²`"; `lemma evalEval_polynomialY (x y : R) :
  W.polynomialY.evalEval x y = 2 * y + W.a₁ * x + W.a₃`; `lemma equation_iff (x y : R) :
  W.Equation x y ↔ y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆`.
- **Q20** [project `HalfPeriods.lean` docstring]: "Classically the converse is proved by counting:
  $\wp'$ is an elliptic function of order $3$, so it has exactly three zeros in a period
  parallelogram [DLMF 23.3, Pastras §1]. That count needs the argument principle for elliptic
  functions, which is not in Mathlib, so the converse is proved here from the second-order
  differential equation instead."

## Prior-B2 log consultation
`.mathlib-quality/b2_log.jsonl` is empty (0 bytes, checked 2026-09-10). No leaf matches a prior
B2 by name or shape. Every leaf below is clean of prior B2 history; the per-leaf line is omitted.

## Result R: `WeierstrassCurve.integralPeriodLattice_eq` (CP:71)

### Plain-English proof (Step 1)
Sources: Q1 for the statement (the period lattice is the set of periods of $dx/(2y+a_1x+a_3)$,
and $\mathbb{C}/\Lambda \cong E(\mathbb{C})$ via $\wp$), Q13/Q16 for the uniformisation, Q3/Q6 for
the elliptic integral inverting $\wp$. The sources prove "$\Lambda$ = periods" by the
uniformisation $z \mapsto (\wp(z), \wp'(z))$ (Q13): under it $\omega$ pulls back to $dz$
(Q6: $(dy/dz)^2 = 4y^3 - g_2y - g_3$, i.e. $d\wp = \wp'\,dz$), so a loop on $E(\mathbb{C})$ lifts
to a path in $\mathbb{C}$ whose endpoints differ by the integral of $\omega$ and lie over the same
point, hence differ by an element of $\Lambda$ (Q11/Q13: $\wp$ is injective mod $\pm$, $(\wp,\wp')$
mod $\Lambda$); conversely $\lambda \in \Lambda$ is the integral over the image of the segment
$[z_0, z_0 + \lambda]$ (Q3 is this for $\lambda = 2\omega_1, 2\omega_3$).

Our route (mirroring the sources' chain, with the counting step replaced by the project's ODE
substitute per Q20): (1) reduce $W$ to its short model by the affine change of variables
$(x,y) \mapsto (x + b_2/12, y + (a_1x+a_3)/2)$, which preserves $\omega$ (Sil2009 III §1;
checkable from Q19: $\Psi_2^2 = \psi_2^2 - 4\cdot\text{(curve)}$ and `eval_Ψ₂Sq_sub`); (2) the short
model is the curve $E_\Lambda$ of the period lattice $\Lambda = $ `W.periodPair.lattice`
($g_2 = c_4/12$, $g_3 = c_6/216$: `periodPair_g₂/g₃`); (3) for $E_\Lambda$, periods $= \Lambda$:
$\supseteq$ by the $\wp$-loop (Q3), $\subseteq$ by lifting (Q6/Q13) + surjectivity (Q4/Q12 via
Liouville) + injectivity mod $\Lambda$ (Q11, proved by the ODE route Q20).

### Tree

- **R** (internal, CP:71) `integralPeriodLattice_eq`. Proof plan: `rw [← W.integralPeriodLattice_shortModel, ← W.periodPair_weierstrassCurve, W.periodPair.integralPeriodLattice_weierstrassCurve]`. Composition attack: the three rewrites are equalities of sets/curves with no hypotheses beyond `[W.IsElliptic]` (needed by `periodPair`); could the children hold and R fail? Only if the two occurrences of "short model" differed — L1 states they are the same curve (`WeierstrassCurve` equality), so the sets are definitionally the same. SURVIVED.
  - **L1** (leaf, project) `periodPair_weierstrassCurve` (CP:66): `W.periodPair.weierstrassCurve = W.shortModel`.
    - Source: definitions — `PeriodPair.weierstrassCurve` (Existence.lean: `a₄ := -L.g₂ / 4, a₆ := -L.g₃ / 4`, docstring "The (short) Weierstrass curve `y² = x³ - (g₂/4) x - (g₃/4)`"), `shortModel` (ID:86: `a₄ := -W.c₄ / 48, a₆ := -W.c₆ / 864`), `periodPair_g₂ : W.periodPair.g₂ = W.c₄ / 12`, `periodPair_g₃ : … = W.c₆ / 216` (PeriodLattice.lean, proved). Verbatim (PeriodLattice.lean docstring of `shortModel_discr_ne_zero`): "The short model $y^2 = x^3 + A x + B$ of an elliptic curve, with $A = -\frac{c_4}{48}$ and $B = -\frac{c_6}{864}$".
    - Lean ↔ source: $-g_2/4 = -(c_4/12)/4 = -c_4/48$ and $-g_3/4 = -(c_6/216)/4 = -c_6/864$; all other coefficients are $0$ on both sides.
    - Discharged by: `WeierstrassCurve.ext` (Mathlib, `@[ext] structure`), `periodPair_g₂`, `periodPair_g₃`, `ring`. (≤ 3 lemmas ✓)
    - Attacks: [2] edge case: none — a pure coefficient identity, no hypotheses beyond `IsElliptic` (needed for `periodPair` to exist). [3] hypothesis test: `IsElliptic` cannot be dropped (no `periodPair` otherwise); nothing hidden. [4] drift: compared field by field with the two definitions above. [5] discharge: `periodPair_g₂/g₃` are in `PeriodLattice.lean` (sorry-free, moved in the skeleton commit; build clean). SURVIVED.
  - **L2** (internal, IPL:72) `integralPeriodLattice_shortModel`: `W.shortModel.integralPeriodLattice = W.integralPeriodLattice`.
    - Source: Sil2009 III §1 (statement: the invariant differential is invariant under a change of variables with $u = 1$); the computation is Q19 + `eval_Ψ₂Sq_sub`. Structural: composition of L2.1–L2.10.
    - Proof plan: unfold both sides to `curveIntegralPeriods`; rewrite `W.shortModel.affineNonTwoTorsion` as `(fun p ↦ W.toShortModelLinear p + (b₂/12, a₃/2)) '' W.affineNonTwoTorsion` (L2.2 + L2.7); apply L2.1 (`curveIntegralPeriods_image_add_const` with `A := W.toShortModelLinear`); the pulled-back form is `W.invariantDifferential` pointwise by L2.6, so the two `curveIntegralPeriods` agree (`congrArg`/`funext`).
    - Composition attack: could the periods of the pullback form differ from the periods of `ω_W` although the forms agree pointwise on all of `ℂ × ℂ`? No — L2.6 is an equality of functions after `funext` (it holds at every `p`, including where the denominator vanishes: both sides are `0 • fst`… check: at `2y + a₁x + a₃ = 0` LHS is `(2·(y + (a₁x+a₃)/2))⁻¹ • fst ∘ A = 0⁻¹ • … = 0`, RHS `0⁻¹ • fst = 0` ✓). SURVIVED.
    - **L2.1** (internal, P:70) `curveIntegralPeriods_image_add_const` (`A : E ≃L[𝕜] E'`): periods of `ω` on `(fun x ↦ A x + c) '' S` = periods of `fun x ↦ (ω (A x + c)).comp A` on `S`.
      - Source: Q17 (definition) — the statement is the change-of-variables formula for curve integrals, i.e. L2.1.1 applied to loops in both directions.
      - Proof plan: `Set.ext w`; (⊆) given `p, γ` in the image set, `γ` maps into `Φ '' S` — but we need a loop *in* `S`: use `Φ⁻¹ ∘ γ = (γ.map' …)` with `Φ⁻¹ x = A.symm (x - c) = A.symm x + (-(A.symm c))`, itself of the form `x ↦ A' x + c'`; `ContDiffOn` of the composite via `ContDiff.comp_contDiffOn` with `Path.extend_map'` (L2.1.3); its range lies in `S`; then rewrite `γ = (Φ⁻¹∘γ).map' Φ` (`Path.ext`, `A.apply_symm_apply`) and apply L2.1.1. (⊇) symmetric with `Φ`.
      - Composition attack: does `Path.map'` of a `C¹` path stay `C¹`? Yes since `Φ` is smooth and `extend_map'` identifies the extension. Does `range (γ.map' h) ⊆ Φ '' S` follow from `range γ ⊆ S`? Yes, `Set.image_subset`. Base point bookkeeping: `Path (Φ p) (Φ p)` ✓. SURVIVED.
      - **L2.1.1** (leaf, mathlib) `curveIntegral_map_add_const` (M:58).
        - Source: Q17 (the integral is $\int_0^1 \omega(\gamma(t))(\gamma'(t))$) — chain rule $(\Phi\circ\gamma)' = A\gamma'$.
        - Lean ↔ source: `∫ᶜ x in γ.map' _, ω x = ∫ t in 0..1, ω (A (γ.extend t) + c) (A (derivWithin γ.extend I t))` = RHS by L2.1.2 pointwise on `I` (interval integral only sees `Ioc 0 1 ⊆ I`).
        - Discharged by: `curveIntegral_def'` (Mathlib, from `irreducible_def curveIntegral (lemma := curveIntegral_def')`, verified at CurveIntegral/Basic.lean), `intervalIntegral.integral_congr` (uIcc-pointwise congruence; verified standard), L2.1.2. (≤ 3 ✓)
        - Attacks: [2] `γ` constant: both sides 0 ✓; `A = 0`: LHS integrand `ω(c)(0) = 0`, RHS `(ω c).comp 0 = 0` ✓. [3] `DifferentiableOn ℝ γ.extend I` is needed: without it `derivWithin` is junk `0` on one side but `A 0 = 0` on the other — actually both sides would be `0` at such `t`, so the hypothesis could be weakened to nothing? Attack succeeds partially: at a non-differentiable `t`, `derivWithin (Φ∘γ.extend) I t` is `0` only if `Φ∘γ.extend` is also non-differentiable there, which holds since `Φ` is an affine *bijection* (`A` equiv) — but the lemma is stated for a mere CLM `A`, where `Φ∘γ` could be differentiable while `γ` is not (e.g. `A = 0`). So for a general CLM the hypothesis is necessary; keep it. Not over-specified for the equiv case either (harmless). [4] drift: matches Q17's formula. [5] `curveIntegral_def'` exists (irreducible_def lemma name) ✓; `intervalIntegral.integral_congr` ✓. SURVIVED.
      - **L2.1.2** (leaf, mathlib) `curveIntegralFun_map_add_const` (M:51).
        - Source: Q17 ("`derivWithin γ.extend (Set.Icc 0 1) t`") + chain rule.
        - Lean ↔ source: `curveIntegralFun ω (γ.map' _) t = ω ((γ.map' _).extend t) (derivWithin (γ.map' _).extend I t)`; by L2.1.3 the extension is `Φ ∘ γ.extend`; `derivWithin (Φ ∘ γ.extend) I t = A (derivWithin γ.extend I t)` by the chain rule at a point of differentiability within `I` (`uniqueDiffOn_Icc`).
        - Discharged by: `curveIntegralFun_def` (Mathlib, Basic.lean:136), `HasDerivWithinAt.derivWithin` + `uniqueDiffOn_Icc` (Deriv/Basic.lean:444; TangentCone/Real.lean:99), `ContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt` / `HasDerivWithinAt.const_add` (standard). (composition of 3 ✓ plus L2.1.3)
        - Attacks: [2] `t = 0`, `t = 1`: `derivWithin` on `I` is one-sided there; `uniqueDiffOn_Icc` covers endpoints ✓. [3] `ht : t ∈ I` needed (outside `I`, `uniqueDiffWithinAt` fails and `derivWithin` may be junk on one side) ✓ necessary. [4] drift: none. [5] names verified by grep. SURVIVED.
      - **L2.1.3** (leaf, mathlib) `Path.extend_map'` (M:39): `(γ.map' h).extend t = f (γ.extend t)`.
        - Source: Mathlib `Path.extend := IccExtend zero_le_one γ` and `Path.map'` `toFun := f ∘ γ` (Path.lean:189, 335; quoted from source).
        - Lean ↔ source: `IccExtend h (f ∘ γ) t = f (IccExtend h γ t)` by `Set.IccExtend_apply` (both sides are `(f ∘ γ) (projIcc 0 1 _ t)`).
        - Discharged by: `Set.IccExtend_apply` (ProjIcc.lean:173) or `rfl`. (1 ✓)
        - Attacks: [2] `t ∉ I`: `projIcc` clamps on both sides identically ✓. [3] no hypotheses beyond `h` (needed to form `map'`). [4] none. [5] `IccExtend_apply` verified. SURVIVED.
    - **L2.2** (leaf, project) `image_toShortModel_affineNonTwoTorsion` (ID:113).
      - Source: Sil2009 III §1 (the change of variables is a bijection of the plane); statement from definitions. Verbatim source for the algebra: Q19.
      - Lean ↔ source: `⊆` by L2.3 (`→`); `⊇`: a point `q` of the short locus is `toShortModel p` for `p := (q.1 - b₂/12, q.2 - (a₁ (q.1 - b₂/12) + a₃)/2)` (explicit inverse), and `p ∈ W.affineNonTwoTorsion` by L2.3 (`←`).
      - Discharged by: L2.3, `Set.ext`/`Set.mem_image`, `Prod.ext` + `ring` (for the inverse). (≤ 3 ✓)
      - Attacks: [2] char 2 or 3: excluded by `NeZero 2`, `NeZero 3` (the inverse divides by 2 and 12) — necessary. [3] `NeZero 3` is needed only through `b₂/12`; cannot drop. [4] none. [5] L2.3 is a sibling leaf. SURVIVED.
    - **L2.3** (leaf, mathlib+project) `toShortModel_mem_affineNonTwoTorsion_iff` (ID:110).
      - Source: Q19 (Mathlib's completing the square) and L2.4. Sil2009 III §1 for the statement.
      - Lean ↔ source: with $X = x + b_2/12$, $Y = y + (a_1x+a_3)/2$: short equation $Y^2 = X^3 - \frac{c_4}{48}X - \frac{c_6}{864}$ ⟺ $4Y^2 = 4X^3 - \frac{c_4}{12}X - \frac{c_6}{216} = \Psi_2^2(X - b_2/12) = \Psi_2^2(x)$ (L2.4) and $4Y^2 = (2y+a_1x+a_3)^2 = \psi_2(x,y)^2$; by Q19 `4·polynomial = ψ₂² − Ψ₂Sq`, so (with $4 \ne 0$) this is exactly `W.toAffine.Equation x y`. Non-2-torsion: $2Y + 0 = 2y + a_1x + a_3$ ✓.
      - Discharged by: `Affine.equation_iff` (Q19), L2.4, L2.5 (or `C_Ψ₂Sq` evaluated), `field_simp`/`linear_combination`. (≤ 3 ✓)
      - Attacks: [1] grep for a Mathlib lemma contradicting invariance of `Equation` under this substitution: none (Mathlib's `VariableChange` acts on curves; consistent). [2] `p` with `2y+a₁x+a₃ = 0`: both sides false ✓ (the `≠ 0` conjunct). [3] `NeZero 2`: needed for `4 ≠ 0` in the `⟸` direction ✓; `NeZero 3` via `12`, `48`, `864` ✓. [4] drift: none. [5] names verified. SURVIVED.
    - **L2.4** (leaf, mathlib) `eval_Ψ₂Sq_sub` (ID:107) — the general form of the ℝ lemma already proved in `RealPeriod.lean` (proof `simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X, c₄, c₆, b₄]; ring`, sorry-free in git history at commit 869ce0a2).
      - Source: DLMF §23.6 / Sil2009 III.1 ($g_2 = c_4/12$, $g_3 = c_6/216$); verbatim from Mathlib: `Ψ₂Sq := C 4 * X ^ 3 + C W.b₂ * X ^ 2 + C (2 * W.b₄) * X + C W.b₆`, `c₄ = b₂ ^ 2 - 24 * b₄`, `c₆ = -b₂ ^ 3 + 36 * b₂ * b₄ - 216 * b₆`.
      - Lean ↔ source: polynomial identity in $b_2, b_4, b_6$ after clearing the denominators $12, 216$.
      - Discharged by: `simp only [Ψ₂Sq, eval_…, c₄, c₆, b₄]`, `field_simp`, `ring`. (≤ 3 ✓)
      - Attacks: [2] char 2/3 excluded by hypotheses; over ℝ it reduces to the proved lemma. [3] `NeZero 2 ∧ NeZero 3` ⟺ `12 ≠ 0` — minimal. [4] none. [5] the ℝ proof exists in history. SURVIVED.
    - **L2.5** (leaf, mathlib) `eval_Ψ₂Sq_eq_sq_of_equation` (ID:67): at an affine point, `Ψ₂Sq.eval x = (2y + a₁x + a₃)²`.
      - Source: Q19 verbatim (`C_Ψ₂Sq`).
      - Lean ↔ source: evaluate `C_Ψ₂Sq` at `(x, y)`: `Ψ₂Sq x = ψ₂(x,y)² − 4·polynomial(x,y)` and `polynomial(x,y) = 0` by `Equation`; `ψ₂(x,y) = 2y + a₁x + a₃` by `evalEval_polynomialY`.
      - Discharged by: `Affine.equation_iff` + `simp [Ψ₂Sq, b₂, b₄, b₆]` + `linear_combination 4 * h` (direct), or `C_Ψ₂Sq` + `evalEval_polynomialY`. (≤ 3 ✓)
      - Attacks: [2] any `CommRing`, no division ✓. [3] no extra hypotheses. [4] none. [5] verified. SURVIVED.
    - **L2.6** (leaf, mathlib) `invariantDifferential_shortModel_comp` (ID:155).
      - Source: Sil2009 III §1 (invariance of $\omega$ for $u = 1$); computation: $dX = dx$, $2Y = 2y + a_1x + a_3$.
      - Lean ↔ source: `ContinuousLinearMap.ext v`; LHS `= v.1 / (2 (y + (a₁x+a₃)/2) + 0·X + 0)` (L2.8, L2.9), RHS `= v.1 / (2y + a₁x + a₃)`; equal since `2·(…/2)` cancels (`NeZero 2`).
      - Discharged by: `ContinuousLinearMap.ext`, `invariantDifferential_apply`, `toShortModelLinear_apply` + `ring_nf`/`field_simp`. (≤ 3 ✓)
      - Attacks: [2] denominator zero: both sides `v.1 / 0 = 0` ✓ (Lean division). [3] `NeZero 2` needed to cancel `2·(1/2)` ✓. [4] none. [5] `ContinuousLinearMap.ext` standard. SURVIVED.
    - **L2.7** (leaf) `toShortModel_eq` (ID:150): `Prod.ext` + `ring` (with L2.8). SURVIVED (pure algebra; [2]/[3]/[4] trivial: no hypotheses; both components are polynomial identities).
    - **L2.8** (leaf, mathlib) `toShortModelLinear_apply` (ID:147) and the two inverse obligations in the `def` (ID:138).
      - Source: definition. Discharged by: `ContinuousLinearEquiv.equivOfInverse_apply` (Equiv.lean:634), `ContinuousLinearMap.prod_apply` (PiProd.lean:96), `ContinuousLinearMap.add_apply/smul_apply/fst_apply/snd_apply`; obligations: `Prod.ext` + `ring`. Attacks: [2] `a₁ = 0`: identity map ✓. [3] no hypotheses ([NeZero 2] carried by the section is unused here — `omit` at cleanup). [5] verified. SURVIVED.
    - **L2.9** (leaf, mathlib) `invariantDifferential_apply` (ID:128): `ContinuousLinearMap.smul_apply`, `fst_apply`, `div_eq_inv_mul`. SURVIVED ([2] denominator `0`: `0⁻¹ • fst v = 0 = v.1 / 0` ✓).
    - **L2.10** (leaf, mathlib) `continuousOn_invariantDifferential` (ID:131): `ContinuousOn.smul` of `(ContinuousOn.inv₀ (by fun_prop) (fun p hp ↦ hp.2))` and `continuousOn_const`. Attacks: [2] on the locus the denominator is nonzero by definition ✓. [3] `Equation` conjunct unused — could be weakened to `{p | 2y+a₁x+a₃ ≠ 0}`; keep the stated set (it is what `curveIntegrable_of_contDiffOn` consumes), note for cleanup. [5] `ContinuousOn.inv₀` standard. SURVIVED.
  - **L3** (internal, WP:104) `PeriodPair.integralPeriodLattice_weierstrassCurve`: `Set.ext w; exact ⟨L.mem_lattice_of_mem_integralPeriodLattice, L.mem_integralPeriodLattice_of_mem_lattice⟩`. Assembly of L3a, L3b. Source: Q1, Q13. Composition attack: both directions are stated for exactly the set `L.weierstrassCurve.integralPeriodLattice` and `L.lattice`; coercion `(L.lattice : Set ℂ)` matches `Submodule` membership ✓. SURVIVED.
    - **L3a** (internal, WP:95) `mem_integralPeriodLattice_of_mem_lattice`.
      - Source: Q3 (2ω₁, 2ω₃ as integrals along paths on which $x = \wp$), Q6 ($d\wp = \wp'\,dz$). Proof plan: obtain `z₀` from L3a.1; `exact curveIntegral_mem_curveIntegralPeriods (L.weierstrassLoop z₀ l h hl) (L.contDiffOn_weierstrassLoop_extend h hl) (L.range_weierstrassLoop_subset h hl) ▸ … ` after rewriting with L3a.6.
      - Composition attack: `curveIntegral_mem_curveIntegralPeriods` needs `ContDiffOn ℝ 1 γ.extend I` and `range γ ⊆ S` — supplied by L3a.4, L3a.5; the value is `l` by L3a.6. SURVIVED.
      - **L3a.1** (leaf, mathlib) `exists_forall_two_mul_add_mul_notMem_lattice` (WP:60).
        - Source: standard (any countable set misses some line); no textbook states it — it is a routine measure/countability fact used in the proof of Q13-type statements ("choose the fundamental domain so that…" in Q12/Q13: "such that f has no zeros or poles on the boundary of D"). Verbatim from Milne Prop 2.1: "let D be a fundamental domain for Λ such that f has no zeros or poles on the boundary of D." — same genericity argument.
        - Lean ↔ source: we need a line $z_0 + \mathbb{R}\lambda$ disjoint from $\tfrac12\Lambda$ (countable).
        - Discharged by: for `l ≠ 0`: `φ z := (conj l * z).im` is ℝ-linear continuous, `φ '' (½Λ)` countable (`countable_lattice.image`), pick `c ∉ φ '' ½Λ` via `Set.Countable.dense_compl ℝ` (`.nonempty`) or `Cardinal.not_countable_real`; `z₀ := I * c * l / ‖l‖²` has `φ z₀ = c` and `φ (z₀ + t l) = c`. For `l = 0`: pick `z₀ ∉ ½Λ` via `not_countable_complex`/`Set.Countable.dense_compl ℂ` on `½Λ = (fun z ↦ z/2) '' Λ`. (3 lemmas ✓)
        - Attacks: [2] `l = 0`: handled separately ✓ (the functional argument breaks there — found by the attack; the statement still holds). [3] no hypotheses on `l` — correct. [4] n/a. [5] `Set.Countable.dense_compl` (Cardinality.lean:131) ✓, `not_countable_complex` ✓, `countable_lattice` (project) ✓. SURVIVED.
      - **L3a.2** (leaf, mathlib+project) `weierstrassLoop` fields (WP:66): `continuous_toFun` (℘, ℘' continuous off Λ: `hasDerivAt_weierstrassPoint`.continuousAt composed with `t ↦ z₀ + t l`), `source'` (`simp`), `target'` (L3a.7 with `l : L.lattice`). Source: Q3/Q16 ("℘ is periodic"). Attacks: [2] `t = 0,1` endpoints are the `source'/target'` fields ✓. [3] `h` needed for continuity (off Λ) — `2 z ∉ Λ ⟹ z ∉ Λ` since `Λ` is closed under doubling (`Submodule.smul_mem`/`add_mem`). [5] verified. SURVIVED.
      - **L3a.3** (leaf, mathlib) `weierstrassLoop_extend` (WP:80): `Path.extend_extends'`/`Set.IccExtend_of_mem`. SURVIVED.
      - **L3a.4** (leaf, mathlib) `contDiffOn_weierstrassLoop_extend` (WP:83): `ContDiffOn.congr` (Defs.lean:565) with L3a.3 of `(L.analyticOnNhd_weierstrassP.contDiffOn …).restrict_scalars ℝ` composed with the ℝ-affine map `t ↦ z₀ + t * l` (`ContDiff` via `Complex.ofRealCLM`), similarly for `℘'` and the pair. Source: Q18 (analytic off the lattice). Attacks: [2] the whole line avoids Λ by `h` ✓. [3] `ContDiffOn … I` needs only `I ⊆ line ⊆ Λᶜ` ✓. [5] `AnalyticOnNhd.contDiffOn` (Defs.lean:718), `ContDiffOn.restrict_scalars` (Operations.lean:1049) ✓. SURVIVED.
      - **L3a.5** (leaf, project) `range_weierstrassLoop_subset` (WP:86): `rintro _ ⟨t, rfl⟩; exact L.weierstrassPoint_mem_affineNonTwoTorsion (h t)`. SURVIVED.
      - **L3a.6** (leaf, mathlib+project) `curveIntegral_weierstrassLoop` (WP:91).
        - Source: Q6 ($(d\wp/dz)^2 = 4\wp^3 - g_2\wp - g_3$, so $d\wp/\wp' = dz$) and Q3 (the period is the integral over the loop).
        - Lean ↔ source: `curveIntegral_eq_intervalIntegral_deriv` gives `∫ t in 0..1, ω (γ.extend t) (deriv γ.extend t)`; on `Ioo 0 1`, `deriv γ.extend t = (℘'(z₀+tl)·l, …)` (`Filter.EventuallyEq.deriv_eq` with L3a.3 on a neighbourhood + `hasDerivAt_weierstrassPoint` + chain rule); `ω (weierstrassPoint z) v = v.1 / ℘' z` (L4.0d); so the integrand is `l` a.e. and the integral is `l`.
        - Discharged by: `curveIntegral_eq_intervalIntegral_deriv` (Basic.lean:144), `intervalIntegral.integral_congr_ae`/`integral_congr` on `Ioo`, `intervalIntegral.integral_const`; `div_self` with `℘' ≠ 0` (`derivWeierstrassP_eq_zero_iff`, `h`). (composition ✓)
        - Attacks: [2] `l = 0`: integrand `0`, integral `0 = l` ✓. [2'] endpoints `t = 0, 1`: `deriv γ.extend` may differ (one-sided); measure-zero, handled by `Ioo` congruence ✓. [3] `h` needed for `℘' ≠ 0` ✓. [4] drift: Q6's identity is used with `Y = ℘'/2`, `ω = dX/(2Y) = dX/℘'` ✓. [5] names verified. SURVIVED.
      - **L3a.7** (leaf, mathlib) `weierstrassPoint_add_coe` (L:73): `weierstrassP_add_coe`, `derivWeierstrassP_add_coe` (Q18). SURVIVED.
      - **L3a.8** (leaf, mathlib+project) `weierstrassPoint_mem_affineNonTwoTorsion` (L:78).
        - Source: Q13 ("It is certainly a well-defined map") and Q7 (the only zeros of ℘′ off Λ are half-periods); LeanBridge `PeriodPair.weierstrassCurve_equation` (proof: `rw [equation_iff, weierstrassCurve]; linear_combination (L.derivWeierstrassP_sq z hz) / 4`).
        - Lean ↔ source: `Equation (℘ z) (℘' z / 2)` ⟺ `(℘'/2)² = ℘³ − (g₂/4)℘ − g₃/4` ⟺ `derivWeierstrassP_sq`; `2·(℘'/2) + 0 + 0 = ℘' ≠ 0` ⟺ `2z ∉ Λ` by `derivWeierstrassP_eq_zero_iff` (project HalfPeriods).
        - Discharged by: `Affine.equation_iff`, `derivWeierstrassP_sq`, `derivWeierstrassP_eq_zero_iff` (+ `z ∉ Λ` from `2z ∉ Λ`). (3 ✓)
        - Attacks: [2] `z` a half-period: excluded by `hz` — and indeed then `℘' = 0`, the point is 2-torsion, so the hypothesis is exactly right. [3] `hz : 2z ∉ Λ` cannot be weakened to `z ∉ Λ` (fails at half-periods). [4] matches Q13. [5] verified. SURVIVED.
      - **L3a.9** (leaf, mathlib+project) `hasDerivAt_weierstrassPoint` (L:81): `HasDerivAt.prodMk` (Deriv/Prod.lean:51) of `hasDerivAt_weierstrassP` and `(hasDerivAt_derivWeierstrassP hz).div_const 2` (both project HalfPeriods). SURVIVED ([3] `hz` necessary: no derivative at poles).
      - **L3a.10** (leaf) `invariantDifferential_weierstrassPoint` (L:85): `invariantDifferential_apply`, `weierstrassCurve` has `a₁ = a₃ = 0` (`simp [weierstrassCurve]`), `mul_div_cancel₀`. SURVIVED ([2] `℘' z = 0`: both sides `v.1/0 = 0` ✓).
    - **L3b** (internal, WP:100) `mem_lattice_of_mem_integralPeriodLattice`.
      - Source: Q13 (isomorphism ⟹ loops lift), Q6/Q3 (the lift is the elliptic integral), Q11 (injectivity mod Λ), Q4/Q12 (surjectivity). Proof plan: `obtain ⟨p, γ, hγ, hS, rfl⟩ := hw`; `p ∈ locus` (`hS (source_mem_range)`), so with `x := p.1`, `y := 2 p.2`: `y² = 4x³ − g₂x − g₃` (from `Equation` of the short curve, `weierstrassCurve` coefficients); AG1' gives `z₀ ∉ Λ` with `℘ z₀ = x`, `℘' z₀ = y`, i.e. `weierstrassPoint z₀ = p`; L4 at `t = 1`: `weierstrassPoint (lift 1) = γ.extend 1 = p`; `lift 1 ∉ Λ` (L4.9); AG2 with `a := lift 1`, `b := z₀`: `lift 1 − z₀ ∈ Λ`; `lift_one` rewrites `lift 1 − z₀ = ∫ᶜ`.
      - Composition attack: could the lift end over `p` but at a point *not* congruent to `z₀`? Only if `(℘,℘')` failed injectivity mod Λ — AG2 excludes. Could `∫ᶜ ≠ lift 1 − z₀`? `lift_one` is definitional. SURVIVED.
      - Discharged by: AG1', L4 (`weierstrassPoint_lift`, `lift_notMem_lattice`), AG2 (`sub_mem_lattice_of_…`), `lift_one`, `Affine.equation_iff`.
  - **L4** (internal, L:143) `weierstrassPoint_lift` + **L4.9** `lift_notMem_lattice` (L:146; extracted from the same induction).
    - Source: Q6 ("the integral formula for the inverse function of ℘": $z = \int_{\wp(z)}^\infty$), Q3 (23.6.36), Q13 ("℘ … is a local isomorphism except at the four listed points" — the local inverse). Q16 ("the extension of u⁻¹ to the complex plane equals the ℘-function").
    - Lean ↔ source: Q6 differentiates the integral $z(y)$ and identifies its inverse with $\wp$ via the ODE; our `lift` is $z_0 + \int_0^t \gamma'_X/(2Y)$, and the claim `weierstrassPoint (lift t) = γ.extend t` is "$\wp(z(t)) = X(t)$, $\wp'(z(t)) = 2Y(t)$", the path-wise form of $\wp \circ z = \mathrm{id}$. The source's proof (uniqueness for $(dy/dz)^2 = 4y^3 - g_2 y - g_3$, Q6) is what the local step L4.3 does.
    - Proof plan: continuous induction with `IsClosed.Icc_subset_of_forall_mem_nhdsWithin (a := 0) (b := 1)` on `s := {t | lift t ∉ Λ ∧ weierstrassPoint (lift t) = γ.extend t}`: `hs` = L4.1; `ha`: `lift 0 = z₀` (L4.0a), `hz₀`, `hp`, `Path.extend_zero`; `hgt` = L4.2. Conclude both conjuncts for `t ∈ I`.
    - Composition attack: `Icc_subset_of_forall_mem_nhdsWithin` needs `s ∈ 𝓝[>] x` for `x ∈ s ∩ Ico 0 1` — L4.2 provides exactly that with `ht1 : t < 1`. The closedness hypothesis is `IsClosed (s ∩ Icc 0 1)` — L4.1 matches. SURVIVED.
    - **L4.0** leaves (L:102–117): (a) `lift_zero`: `intervalIntegral.integral_same` (Basic.lean:681) ✓. (b) `lift_one`: `curveIntegral_def'` (rfl after unfolding) ✓. (c) `continuousOn_curveIntegralFun_invariantDifferential`: transcription of Mathlib's proof of `ContinuousOn.curveIntegrable_of_contDiffOn` (Basic.lean:334: `simp only [funext (curveIntegralFun_def ω γ)]; apply ContinuousOn.clm_apply; · exact hω.comp (by fun_prop) …; · exact hγ.continuousOn_derivWithin …`) with `hω := continuousOn_invariantDifferential`; discharged by `curveIntegralFun_def`, `ContinuousOn.clm_apply` (BoundedLinearMaps.lean:475), `ContDiffOn.continuousOn_derivWithin` (ContDiff/Deriv.lean:72). (d) `hasDerivWithinAt_lift`: `intervalIntegral.integral_hasDerivWithinAt_right` (FundThmCalculus.lean:867) with integrability from (c) (`ContinuousOn.intervalIntegrable`) and continuity within `I` at `t` ✓. (e) `continuousOn_lift`: `(hasDerivWithinAt_lift …).continuousWithinAt` ✓. (f) `hasStrictDerivAt_weierstrassP` (L:89): `(L.analyticOnNhd_weierstrassP z hz).hasStrictDerivAt` (FDeriv/Analytic.lean:147) and `HasStrictDerivAt.hasDerivAt.unique (hasDerivAt_weierstrassP hz)` to identify the derivative ✓. Attacks on (c)–(e): [2] endpoints `t = 0, 1`: `integral_hasDerivWithinAt_right` handles one-sided derivatives within `I` ✓; [3] `hγ`, `hS` needed for continuity of the integrand (the form is discontinuous off the locus) ✓; [5] all names verified. SURVIVED.
    - **L4.1** (leaf, mathlib+AG1.1) `isClosed_setOf_weierstrassPoint_lift_eq` (L:121).
      - Source: Q13 (properness of the covering: "℘ realizes ℂ/Λ as a covering of degree 2 of the Riemann sphere" — the lift over a bounded set of $x$ stays away from the poles), Q18 (`order_weierstrassP`: pole of order 2).
      - Lean ↔ source: closedness in `Icc`: if `tₙ → t` with `tₙ ∈ s`, then `lift tₙ → lift t` (L4.0e); if `lift t ∈ Λ` then `℘ (lift tₙ) → ∞` (AG1.1, `Bornology.cobounded`) while `℘ (lift tₙ) = (γ.extend tₙ).1 → (γ.extend t).1` is bounded — contradiction (`tendsto_norm_atTop_iff_cobounded`, Bounded.lean:46); so `lift t ∉ Λ`, and continuity of `weierstrassPoint` at `lift t` (L3a.9) gives the equation by uniqueness of limits (`tendsto_nhds_unique`).
      - Discharged by: `isClosed_iff_clusterPt`/`IsClosed.mem_of_tendsto` on `ℝ` via sequences (`isClosed_of_closure_subset` + `mem_closure_iff_seq_limit`), AG1.1, `Path.continuous_extend`, `tendsto_nhds_unique`. (composition ✓)
      - Attacks: [2] `t` an endpoint: intersection with `I` keeps it inside; sequences in `I` ✓. [3] `hγ`,`hS` used only through `continuousOn_lift` ✓. [4] the source's properness is used only in the form AG1.1 (pole) ✓. [5] verified. SURVIVED.
    - **L4.2** (leaf-ish, mathlib+L4.3) `eventually_weierstrassPoint_lift_eq` (L:136).
      - Source: Q6 (uniqueness for the ODE), Q13 (local isomorphism).
      - Lean ↔ source: from L4.3 get `v` with `v t = lift t`, and `∀ᶠ u in 𝓝 t`: good at `v u` and `HasDerivWithinAt v (curveIntegralFun …) I u` for `u ∈ I`. Pick `ε > 0` with `t + ε ≤ 1` and the eventual statement on `Icc t (t+ε)`. On `Icc t (t+ε) ⊆ I`, both `v` and `lift` have `derivWithin` equal to the integrand (L4.0d), so `eq_of_derivWithin_eq` (MeanValue.lean:386: `DifferentiableOn ℝ f (Icc a b)`, `EqOn (derivWithin f (Icc a b)) (derivWithin g (Icc a b)) (Ico a b)`, `f a = g a` ⟹ equal on `Icc a b`) gives `lift = v` on `Icc t (t+ε)`, hence the good properties for `u ∈ Ioc t (t+ε) ∈ 𝓝[>] t` (`Ioc_mem_nhdsGT`).
      - Attacks: [2] `t = 0`: `Icc 0 ε ⊆ I` ✓; `t` near `1`: `ht1 : t < 1` gives room ✓ (attack found the need for `ht1` — present). [3] `hlift`, `heq` needed to start L4.3 ✓. [5] `eq_of_derivWithin_eq` verified; note `derivWithin` on `Icc t (t+ε)` vs on `I`: for `u ∈ Ico t (t+ε)`, `𝓝[Icc t (t+ε)] u = 𝓝[I] u`?? — at `u = t` the right-neighbourhoods agree (`Icc t (t+ε) ∩ (t, ∞) = Ioc t (t+ε)`), and for `u ∈ Ioo`, `Icc t (t+ε) ∈ 𝓝 u`... use `HasDerivWithinAt.mono` to the subset `Icc t (t+ε) ⊆ I` and `HasDerivWithinAt.derivWithin` with `uniqueDiffOn_Icc` — sound. SURVIVED.
    - **L4.3** (internal, L:129) `exists_localLift`.
      - Source: Q13 ("it is a local isomorphism except at the four listed points"), Q6 (the ODE and its uniqueness), Q7/Q16 (℘′ ≠ 0 off the half-lattice).
      - Lean ↔ source: with `hw' : ℘' w ≠ 0` (from `heq`: `℘' w / 2 = (γ.extend t).2 ≠ 0` by `hS`), `ψ := (hasStrictDerivAt_weierstrassP hw).localInverse ℘ (℘' w) w hw'` and `v u := ψ (γ.extend u).1`. Then `v t = ψ (℘ w) = w` (`localInverse_apply_image`); `℘ (v u) = (γ.extend u).1` near `t` (`eventually_right_inverse` pulled back along the continuous `u ↦ (γ.extend u).1`); `v u ∉ Λ` near `t` (`v` continuous at `t` via `HasStrictFDerivAt.localInverse_continuousAt`, `Λ` closed); sign-locking (L4.4): `f u := ℘' (v u)`, `g u := 2 (γ.extend u).2` are continuous at `t`, `f t = g t` (`heq`), `f t ≠ 0`, `f² = g²` near `t` (`derivWeierstrassP_sq` + the short-curve `Equation` at `γ u` from `hS`), so `℘' (v u) = 2 (γ.extend u).2` near `t`; derivative: `HasStrictDerivAt ψ (℘' (v u))⁻¹ ((γ.extend u).1)` for `u` near `t` via `HasStrictDerivAt.to_local_left_inverse` (Deriv.lean) applied at `v u` with `eventually_left_inverse` transported (`v u` near `w`), then `HasStrictDerivAt.comp_hasDerivWithinAt`/`HasDerivWithinAt` chain rule with `(hγ.differentiableOn le_rfl u hu).hasDerivWithinAt` giving `v' = (derivWithin γ.extend I u).1 / ℘' (v u) = (…).1 / (2 (γ.extend u).2) = curveIntegralFun ω γ u` (`curveIntegralFun_def`, `invariantDifferential_apply`, `weierstrassCurve` coefficients).
      - Discharged by: `HasStrictDerivAt.localInverse`, `.eventually_right_inverse`, `.eventually_left_inverse`, `.to_local_left_inverse` (InverseFunctionTheorem/Deriv.lean:20–60, verified), `HasStrictFDerivAt.localInverse_continuousAt` (FDeriv.lean), L4.4, L4.0f, `derivWeierstrassP_sq`, `HasStrictDerivAt.comp` (Deriv/Comp.lean:271) / `HasDerivWithinAt.comp`.
      - Attacks (composition): could the local inverse's derivative be taken at the wrong point? `to_localInverse` gives the derivative only at `℘ w`; the attack found that nearby points need `to_local_left_inverse` at `v u` — recorded above, not a gap. Could `℘' (v u) = −2Y(u)` on a sequence accumulating at `t`? No: L4.4 gives an eventual equality from continuity + nonvanishing. Could `v u` hit `Λ`? Excluded eventually by continuity and closedness of `Λ`. [3] `ht : t ∈ I` is needed only for `hu`-conditioned derivative claims; fine. SURVIVED.
    - **L4.4** (leaf, mathlib) `eventually_eq_of_sq_eq_sq` (T:36).
      - Source: elementary; the sources use it implicitly ("the sign is fixed by continuity", cf. Q6's "±z" in (1.33)). Statement is self-contained.
      - Lean ↔ source: `f² = g²` ⟹ `(f − g)(f + g) = 0`; `f + g` is continuous at `a` with value `2 f a ≠ 0` (`NeZero 2`), hence nonzero near `a` (`ContinuousAt.eventually_ne`, Separation/Basic.lean:710); so `f = g` near `a`.
      - Discharged by: `ContinuousAt.eventually_ne`, `sq_eq_sq_iff_eq_or_eq_neg` (Ring/Commute.lean:219) or `mul_self_eq_mul_self_iff`, `eq_neg_iff_add_eq_zero`. (3 ✓)
      - Attacks: [1] counterexample search: `f = id`, `g = |·|` on ℝ at `a = 0`: `f 0 = g 0 = 0` — excluded by `h0`; at `a = 1`: `f = g` near 1 ✓; `f = id, g = −id` at `a ≠ 0`: `f a ≠ g a` — excluded by `h` ✓. Attack confirms both `h` and `h0` are necessary. [2] char 2: `f + g = 2f = 0` — excluded by `NeZero 2`; necessary (in char 2, `f² = g²` ⟺ `f = g` anyway, so the lemma is true there too but the proof differs — hypothesis is not over-specified for the proof; acceptable). [3] `T1Space` needed for `eventually_ne` ✓. [5] verified. SURVIVED.
  - **AG1** (API gap, S:62) `exists_weierstrassP_eq` — sub-tree:
    - Source: Q4 (Pastras Thm 1.2 with proof), Q12 (Milne Cor 2.2 with proof), Q9 (W&W §20.12(IV)); statement Q5/Q10 (every value is taken, `order` times). LeanBridge `work/inverse.lean` docstring: "if it had no zero then 1/(℘ − c) would be a lattice-periodic entire function, bounded on a period parallelogram hence bounded, hence constant by Liouville — contradiction."
    - Lean ↔ source: Q4's proof verbatim, applied to $f = 1/(\wp - c)$: "no poles in a cell" = AG1.2 (entire); "bounded everywhere" by periodicity = `IsZLattice.isCompact_range_of_periodic`; "bounded analytic ⟹ constant" = Liouville; the constant is `0` (value at a lattice point), contradicting `(℘ z − c)⁻¹ ≠ 0` for any `z ∉ Λ` (e.g. `ω₁/2`, `ω₁_div_two_notMem_lattice`).
    - Proof plan: `by_contra! hc` (`∀ z, z ∉ Λ → ℘ z ≠ c`); `g := (Λᶜ).indicator (℘ − c)⁻¹`; `hg : Differentiable ℂ g` (AG1.2); periodic: `g (z + w) = g z` for `w ∈ Λ` (`Set.indicator`, `Submodule.add_mem_iff_right`, `weierstrassP_add_coe`); bounded: `(IsZLattice.isCompact_range_of_periodic L.lattice g hg.continuous hper).isBounded`; `hg.apply_eq_apply_of_bounded hb (ω₁/2) 0`: `g (ω₁/2) = g 0 = 0`; but `g (ω₁/2) = (℘ (ω₁/2) − c)⁻¹ ≠ 0` by `inv_ne_zero (sub_ne_zero.mpr (hc _ ω₁_div_two_notMem_lattice))`.
    - Composition attack: `isCompact_range_of_periodic` requires `[DiscreteTopology L.lattice] [IsZLattice ℝ L.lattice]` — both are instances in Mathlib's Weierstrass.lean (lines 118, 120) ✓ and is already used the same way at Weierstrass.lean:1070. SURVIVED.
    - **AG1.1** (leaf, mathlib+project) `tendsto_weierstrassP_cobounded` (S:53).
      - Source: Q18 (`order_weierstrassP`: pole of order 2 at lattice points); Q4 ("a pole … congruent").
      - Lean ↔ source: `weierstrassP_eq : ℘ z = ℘[L - 0] z + 1/z²` (project Uniqueness.lean) with `℘[L-0]` analytic (bounded) near `0` and `‖1/z²‖ → ∞` (`NormedField.tendsto_norm_inv_nhdsNE_zero_atTop`, Field/Lemmas.lean:202, squared), so `‖℘ z‖ → ∞` as `z → 0`, i.e. `Tendsto ℘ (𝓝[≠] 0) (cobounded ℂ)` (`tendsto_norm_atTop_iff_cobounded`); at `l ∈ Λ` translate by `weierstrassP_sub_coe`.
      - Discharged by: `weierstrassP_eq`, `analyticAt_weierstrassPExcept` (continuity ⟹ bounded near 0), `tendsto_norm_atTop_iff_cobounded` + `NormedField.tendsto_norm_inv_nhdsNE_zero_atTop`; `Filter.Tendsto.atTop_add` of bounded. (composition ✓)
      - Attacks: [1] grep Mathlib for `Tendsto ℘[L] … cobounded`: absent (gap confirmed, not contradicted; `not_continuousAt_weierstrassP` is the weaker existing fact). [2] `l = 0` base case then translation ✓. [3] `hl` necessary (off Λ, ℘ is continuous). [5] names verified. SURVIVED.
    - **AG1.2** (leaf, mathlib) `differentiable_inv_weierstrassP_sub` (S:58).
      - Source: Q4 ("such a function is not just meromorphic, but rather it is analytic"), Q12.
      - Lean ↔ source: off `Λ`: `g = (℘ − c)⁻¹` on the open set `Λᶜ` (`isClosed_lattice.isOpen_compl`), differentiable by `analyticOnNhd_weierstrassP` and `hc` (`DifferentiableAt.inv`), `Set.indicator_of_mem`; at `l ∈ Λ`: `g` is differentiable on the punctured neighbourhood `Λᶜ ∪ … ` given by `compl_lattice_sdiff_singleton_mem_nhds` (Weierstrass.lean:140), and continuous at `l` since `g l = 0` and `g → 0` (AG1.1 inverted: `Tendsto.inv_tendsto_cobounded`-type, i.e. `tendsto_inv_zero_cobounded`… realised as `(tendsto_norm_atTop_iff_cobounded.mp h).inv_tendsto_atTop` on norms + `tendsto_zero_iff_norm_tendsto_zero`), so `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` (RemovableSingularity.lean:36) gives analyticity, hence differentiability.
      - Discharged by: `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`, `compl_lattice_sdiff_singleton_mem_nhds`, `Set.indicator_of_mem/notMem` (+ AG1.1). (≤ 3 + AG1.1 ✓)
      - Attacks: [2] `c` itself a lattice value? `℘` at lattice points is junk (`weierstrassP_coe`), irrelevant: `hc` quantifies over `z ∉ Λ` only ✓. [3] `hc` necessary (otherwise `g` has poles). [4] drift: Q4 says "analytic" for a function with no poles — exactly the removable-singularity step. [5] verified. SURVIVED.
    - **AG1'** (leaf, mathlib+AG1) `exists_weierstrassP_eq_and_derivWeierstrassP_eq` (S:66) — shared-witness existential (documented exception: `∃ z, z ∉ Λ ∧ ℘ z = x ∧ ℘' z = y` must keep one witness).
      - Source: Q13 ("It is certainly a well-defined map … 2:1"), LeanBridge `work/inverse.lean` docstring: "for an affine point (x, y) ∈ E, pick z with ℘(z) = x; the curve equation forces (½℘′(z))² = y², and replacing z by −z (℘ even, ℘′ odd) fixes the sign."
      - Lean ↔ source: AG1 gives `z ∉ Λ`, `℘ z = x`; `derivWeierstrassP_sq` ⟹ `℘' z ^ 2 = y ^ 2` ⟹ `℘' z = y ∨ ℘' z = −y` (`sq_eq_sq_iff_eq_or_eq_neg`); in the second case use `−z` (`neg_mem_iff`, `weierstrassP_neg`, `derivWeierstrassP_neg`).
      - Attacks: [2] `y = 0`: both cases coincide ✓. [3] `h` necessary (otherwise no such `z`). [5] `sq_eq_sq_iff_eq_or_eq_neg` (Commute.lean:219), parity lemmas (Q18) ✓. SURVIVED.
  - **AG2** (API gap, J:76) `sub_mem_lattice_of_weierstrassP_eq_of_derivWeierstrassP_eq` — sub-tree:
    - Source: Q11 (statement: the zeros of ℘(z) − ℘(y) are exactly z ≡ ±y), Q13 ("2:1 … except at the [half-periods], where it is one-to-one"), Q8. Sources' proof: counting (Q10/Q5). Substitute per Q20: the project's ODE route, whose three steps are literally `eventually_weierstrassP_add_eq_sub`, `weierstrassP_add_eq_sub_of_derivWeierstrassP_eq_zero`, `two_mul_mem_lattice_of_derivWeierstrassP_eq_zero` in HalfPeriods.lean with `(a, b) = (z₀, −z₀)`; here generalised to arbitrary `a, b`.
    - Lean ↔ source: Q11 says ℘(a) = ℘(b) ⟹ a ≡ ±b; adding ℘′(a) = ℘′(b) selects the sign `+` (since ℘′ is odd and, off the half-lattice, nonzero) — that is the statement `a − b ∈ Λ`. Our proof: AG2.1 ⟹ AG2.2 ⟹ `a − b` is a period of ℘ ⟹ AG2.3.
    - Proof plan (main): `apply L.mem_lattice_of_forall_weierstrassP_add_eq`; `intro z hz hz'`; set `w := z − b` … precisely: for `z ∉ Λ` with `z + (a − b) ∉ Λ`, write `z = b + (z − b)` and `z + (a − b) = a + (z − b)`; apply AG2.2 with `hz : a + (z − b) ∉ Λ`, `hz' : b + (z − b) ∉ Λ`.
    - Composition attack: AG2.3 needs the identity for *all* `z` off the two lattices; AG2.2 provides exactly that (its hypotheses are the two non-membership conditions). Could `a − b ∈ Λ` fail although `℘(· + (a−b)) = ℘`? No — that is AG2.3. SURVIVED.
    - **AG2.1** (leaf, mathlib+project) `eventually_weierstrassP_add_eq_add` (J:59): transcription of `eventually_weierstrassP_add_eq_sub` (HalfPeriods.lean:136–178, sorry-free) with `g t := (℘ (b + t), ℘' (b + t))` in place of `(℘ (z₀ − t), −℘' (z₀ − t))`; initial values agree by `h₁, h₂`.
      - Source: Q6 (the ODE and uniqueness of its solutions: "the general solution of this equation is y = ℘(z + z₀)"); Q20 (project's substitution).
      - Discharged by: `ODE_solution_unique_of_eventually` (ExistUnique.lean:312), `ContDiffAt.exists_lipschitzOnWith`, `hasDerivAt_weierstrassP`/`hasDerivAt_derivWeierstrassP` (project), `HasDerivAt.comp_ofReal`, `HasDerivAt.prodMk`. (mirrors an existing proof ✓)
      - Attacks: [2] `a = b`: trivial ✓; `a − b ∈ Λ` already: consistent. [3] `ha`, `hb` needed (derivatives exist only off Λ) ✓. [4] drift: the source's uniqueness is for the first-order equation `(dy/dz)² = …`, which has the sign ambiguity Q6 notes ("w = ±z + z₀"); our second-order system removes it — that is why `h₂` (equal ℘′) is a hypothesis. Attack confirms `h₂` is essential: with only `h₁`, `b = −a` is a counterexample (℘(a+t) ≠ ℘(−a+t) in general). [5] verified. SURVIVED.
    - **AG2.2** (leaf, mathlib+project) `weierstrassP_add_eq_add_of_eq` (J:65): transcription of `weierstrassP_add_eq_sub_of_derivWeierstrassP_eq_zero` (HalfPeriods.lean:182–222) with `U := {w | a + w ∉ Λ ∧ b + w ∉ Λ}`.
      - Source: identity theorem (Q6's "general solution", Q20). Discharged by: `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, `Complex.isPreconnected_compl_of_countable` (project), `countable_lattice` (project), AG2.1. ✓
      - Attacks: [2] `z = 0`: the hypotheses reduce to `ha, hb` ✓. [3] `hz, hz'` necessary (poles). [5] verified. SURVIVED.
    - **AG2.3** (leaf, mathlib+project) `mem_lattice_of_forall_weierstrassP_add_eq` (J:71): transcription of `two_mul_mem_lattice_of_derivWeierstrassP_eq_zero` (HalfPeriods.lean:227–247) with `c` in place of `2 z₀`.
      - Source: Q18 (`order_weierstrassP`: pole of order 2 at 0) vs analyticity at `c ∉ Λ` (Q18); the argument "comparing orders at 0" is the project's (Q20). Statement is classical: the period group of ℘ is Λ (Q1 "periodic with respect to a lattice Λ").
      - Discharged by: `order_weierstrassP` (Weierstrass.lean:921), `meromorphicOrderAt_congr` (Order.lean:277), `AnalyticAt.meromorphicOrderAt_nonneg` (Order.lean:308), `eventually_notMem_lattice` (project). ✓
      - Attacks: [1] counterexample search: a non-lattice period of ℘? Impossible by the pole argument; no Mathlib statement contradicts. [2] `c = 0`: `zero_mem` ✓ (the `by_contra` route handles it). [3] the hypothesis quantifies only over `z` with both points off Λ — that is exactly what AG2.2 provides; cannot be strengthened without losing applicability. [5] verified. SURVIVED.
    - **AG2.4** (leaf, mathlib+AG2) `weierstrassP_eq_iff` (J:81): (→) `derivWeierstrassP_sq` at `a, b` with `h` ⟹ `℘' a ^ 2 = ℘' b ^ 2` ⟹ `℘' a = ℘' b ∨ ℘' a = −℘' b`; first case AG2 ⟹ `a − b ∈ Λ`; second: `℘' a = ℘' (−b)`, `℘ a = ℘ (−b)` (parity), AG2 at `(a, −b)` ⟹ `a + b ∈ Λ`. (←) `weierstrassP_sub_coe`/`weierstrassP_add_coe` + `weierstrassP_neg`. Source: Q11 verbatim. Attacks: [2] `a = b`: `0 ∈ Λ` ✓; `b = −a`: second disjunct ✓. [3] `ha`, `hb` needed (junk values on Λ). [5] verified. SURVIVED.
  - **Definition/API leaves** (P:56–65, IPL:64–68, CP:76): `curveIntegral_mem_curveIntegralPeriods` (`⟨p, γ, hγ, hS, rfl⟩`), `curveIntegralPeriods_mono` (`Set.Subset.trans`), `zero_mem_curveIntegralPeriods` (`Path.refl p`, `curveIntegral_refl` (Basic.lean:171), `Path.refl_extend` (Path.lean:244) + `contDiffOn_const`), `neg_mem_curveIntegralPeriods` (`γ.symm`, `curveIntegral_symm` (213), `Path.extend_symm` (251) + `ContDiffOn.comp` with `t ↦ 1 − t`), `affineNonTwoTorsion_nonempty` (`Polynomial.exists_eval_ne_zero` (Roots.lean:772) for `Ψ₂Sq ≠ 0` (`Ψ₂Sq_ne_zero four_ne_zero`) gives `x`; `IsAlgClosed.exists_pow_nat_eq` (IsAlgClosed/Basic.lean:81) gives `s` with `s² = Ψ₂Sq x`; `y := (s − a₁x − a₃)/2`; `Equation` via L2.5's identity reversed (`equation_iff` + `linear_combination`), and `2y + a₁x + a₃ = s ≠ 0`), `zero_mem_integralPeriodLattice`, `neg_mem_integralPeriodLattice` (from the general ones), `exists_curveIntegral_eq_of_mem_lattice` (`mem_integralPeriodLattice_iff.mp (W.integralPeriodLattice_eq ▸ hl)`). Source for the definitional ones: Q17. Attacks: [2] `S = ∅`: `zero_mem` needs `S.Nonempty` — present ✓ (attack found it necessary). `neg_mem`: `symm` of a loop at `p` is a loop at `p` ✓. [5] all names verified. SURVIVED.

### Step 5 — confidence gate
1. Every leaf is discharged from Mathlib (names grep-verified), from project code (`HalfPeriods.lean`, `Uniqueness.lean`, `Existence.lean`, `PeriodLattice.lean`), or is one of the API gaps AG1, AG2 with its own sub-tree above. ✓
2. Skeleton compiles: `lake build` of the two top-level targets succeeded with only sorry warnings (2026-09-10). ✓
3. Every leaf has a verbatim quote (Q-references above, each quoted in full in the quote block) and a Lean ↔ source paragraph. ✓ (Purely definitional leaves quote the Mathlib definition Q17/Q19.)
4. Every leaf and internal node has an attack block with ≥ 3 categories; all recorded attacks ended "SURVIVED"; the attacks that *changed* the plan (necessity of `ht1`, `to_local_left_inverse` at nearby points, `l = 0` case, `S.Nonempty`) are recorded in place. ✓
5. B2 log empty. ✓
6. Tree mirrors the sources: R ↔ Q1/Q13 (uniformisation ⟹ periods = lattice); AG1 ↔ Q4/Q12 (Liouville, verbatim route); AG2 ↔ Q11 with the counting step replaced by the project's documented ODE route (Q20) — the one deliberate departure, recorded; L4 ↔ Q6/Q13 (the elliptic integral inverts ℘; local isomorphism); L2 ↔ Sil2009 III §1 / Q19. LOC estimates (tickets.md) cite source lengths: Q4 = 6 lines, Q12 = 4 lines, Q6 = 10 lines, Q13 proof = 8 lines, HalfPeriods.lean = 247 lines for the specialised AG2. ✓
7. Single-conclusion: the only bundled statements are the two documented shared-witness existentials (AG1', L4.3), the assembly nodes R, L3, and the `Path`-structure fields of `weierstrassLoop`. ✓
