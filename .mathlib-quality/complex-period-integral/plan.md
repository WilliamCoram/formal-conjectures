# Development Plan: the complex period as a single integral

Board: `.mathlib-quality/complex-period-integral/` (this directory). Branch `periods`, files under
`FormalConjecturesTest/Period/` (the moved layout; the moved folders were verified to build on
2026-09-10 before the skeleton was added). Shared B2 log: `.mathlib-quality/b2_log.jsonl` (empty).
Nothing is committed by the agent — the user commits ([[never-commit-or-merge]]).

## Goal

```lean
/-- Ω_ℂ(E) = ∫_{E(ℂ)} |ω ∧ ω̄| = 4 ∫_ℂ dA(x) / |Ψ₂²(x)|, the period at a complex place. -/
def WeierstrassCurve.complexPeriodIntegral (W : WeierstrassCurve ℂ) : ℝ :=
  4 * ∫ x : ℂ, ‖W.Ψ₂Sq.eval x‖⁻¹

/-- The complex period is twice the covolume of the period lattice. -/
theorem WeierstrassCurve.complexPeriodIntegral_eq_two_mul_covolume (W : WeierstrassCurve ℂ)
    [W.IsElliptic] : W.complexPeriodIntegral = 2 * ZLattice.covolume W.periodPair.lattice

/-- In the form of the LMFDB knowl: `2 |Im(ω̄₁ ω₂)|`. -/
theorem WeierstrassCurve.complexPeriodIntegral_eq_two_mul_abs_im (W : WeierstrassCurve ℂ)
    [W.IsElliptic] : W.complexPeriodIntegral = 2 * |((starRingEnd ℂ) W.periodPair.ω₁ * W.periodPair.ω₂).im|
```

Milestone: `complexPeriodIntegral_eq_two_mul_covolume` (T018). Everything is stated with the
`periodPair` chosen on the complex-period board; only its lattice enters, and the covolume does not
depend on the basis.

## References

| Tag | Reference | Used for |
|---|---|---|
| [LMFDB-P] | LMFDB knowl `ec.period` (https://www.lmfdb.org/knowledge/show/ec.period), fetched 2026-09-10, text in the decomposition | the **definition** `Ω_v(E_v) = ∫_{E_v(ℂ)} ω_E ∧ ω̄_E`, the **value** `2 Im(w̄₁w₂)`, and the phrase "double the covolume of the period lattice" |
| [LMFDB-PL] | LMFDB knowl `ec.q.period_lattice` | the period lattice is the lattice of periods of `dx/(2y + a₁x + a₃)`; `ℂ/Λ ≅ E(ℂ)` via ℘ |
| [Mil2006] | J. S. Milne, *Elliptic Curves* (2006), Ch. III: Prop. 2.4 (p. 85), Prop. 3.7, Remark 3.11 (p. 94); https://www.jmilne.org/math/Books/ectext6.pdf, extracted to the session scratchpad as `milne.txt` | the pullback identity `dx/y = ℘'(z)dz/℘'(z) = dz`; `℘' = d℘/dz` |
| [Sil2009] | Silverman, *AEC* 2nd ed., VI.3.6(b), VI.5.1 | statements only (not fetchable): `ℂ/Λ → E(ℂ)` bijective via `(℘, ℘')` — realised in this project as `exists_weierstrassP_eq` / `weierstrassP_eq_iff` |
| [Wiki-CR] | Wikipedia, *Cauchy–Riemann equations* (raw wikitext fetched 2026-09-10, line 71) | "the Jacobian of f at z₀ is the complex scalar f'(z₀), regarded as a real-linear map of ℂ" |
| [Wiki-C] | Wikipedia, *Complex number*, § Matrix representation (raw wikitext, line 271) | "this isomorphism associates the square of the absolute value of a complex number with the determinant of the corresponding matrix" |
| project | `Weierstrass/{Injective,Surjective,HalfPeriods}.lean`, `EllipticCurve/{InvariantDifferential,PeriodLattice}.lean` | `weierstrassP_eq_iff`, `exists_weierstrassP_eq`, `derivWeierstrassP_eq_zero_iff`, `hasDerivAt_weierstrassP`, `eval_Ψ₂Sq_sub`, `periodPair_g₂`, `periodPair_g₃` |

**Source-faithfulness note — where the Lean object differs from the source's object.** The knowl
defines the period as an integral over $E(\mathbb{C})$ of the 2-form $\omega \wedge \bar\omega$;
its stated value $2\operatorname{Im}(\bar w_1 w_2) > 0$ shows the integrand is meant as the density
$|\omega \wedge \bar\omega|$. Mathlib has no measure on the affine curve as a real surface, so the
definition is transcribed through the projection to the $x$-line: on each of the two sheets over
$x$, $|\omega \wedge \bar\omega| = |dx \wedge d\bar x| / |2y + a_1 x + a_3|^2$ and
$(2y + a_1x + a_3)^2 = \Psi_2^2(x)$ on the curve (`WeierstrassCurve.eval_Ψ₂Sq_eq_sq_of_equation`),
while $|dx \wedge d\bar x| = 2\,dA$; two sheets give the factor $4$. This dictionary — source
object $\int_{E(\mathbb{C})}|\omega\wedge\bar\omega|$ ↔ Lean object
`4 * ∫ x : ℂ, ‖W.Ψ₂Sq.eval x‖⁻¹` — is the one non-formal step of the development, and it is the
same step the real-period board took (`leastRealPeriodIntegral` is $\int dx/\sqrt{\Psi_2^2(x)}$
over the real locus). It is recorded in the module docstring of `ComplexPeriodIntegral.lean`, not
proved. Everything after it is a theorem.

The proof mirrors the source at the only place the source has one: [Mil2006, Rem. 3.11]'s
`dx/y = dz` is, in real terms, "the density $dA(x)/|4x^3 - g_2x - g_3|$ pulls back under
$x = \wp(z)$ to $dA(z)$", i.e. Jacobian $|\wp'|^2$ cancels $|4\wp^3 - g_2\wp - g_3| = |\wp'|^2$.
The remaining content — that $\wp$ is two-to-one from a fundamental domain — is [Sil2009, VI.3.6(b)]
plus evenness, realised by the project's own `weierstrassP_eq_iff` and `exists_weierstrassP_eq`.
No leaf was invented to "connect to existing code": the half-domain bookkeeping is the formal
rendering of "fundamental domain modulo $\pm$".

## Mathlib inventory

| Concept | Mathlib status | Action |
|---|---|---|
| Change of variables in ℝⁿ for an injective a.e.-differentiable map | `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`, `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` (`MeasureTheory/Function/Jacobian.lean:1213, 1199`) | USE |
| Image of a null set under a differentiable map is null | `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (`Jacobian.lean:556`) | USE |
| Proper subspaces are null | `Measure.addHaar_submodule` (`Measure/Lebesgue/EqHaar.lean:172`), `addHaar_affineSubspace` (:199) | USE |
| Lebesgue measure on ℂ is the inner-product Haar measure; ℂ ≃ ℝ² measure preserving | `MeasureTheory/Measure/Lebesgue/Complex.lean` (`measureSpaceOfInnerProductSpace`, `volume_preserving_equiv_real_prod`) | USE (instances) |
| Real determinant of multiplication by `c` is `‖c‖²` | **absent** (`ContinuousLinearMap.det_smulRight` is the 𝕜-linear `f 1 * v`) | DEFINE: `Complex.det_restrictScalars_smulRight` |
| Covolume of a ℤ-lattice; via a ℤ-basis and an ℝ-basis | `ZLattice.covolume`, `covolume_eq_measure_fundamentalDomain` (:84), `covolume_eq_det_mul_measureReal` (:115), `covolume_pos` (:98) | USE |
| Covolume of a lattice in ℂ as `\|Im(w̄₁w₂)\|` | **absent** | DEFINE: `ZLattice.covolume_eq_abs_im_conj_mul` |
| Fundamental domain of a ℤ-span; measurability, boundedness, `fract`, `=ᵐ parallelepiped` | `ZSpan.fundamentalDomain`, `fundamentalDomain_measurableSet` (:336), `isAddFundamentalDomain` (:350), `fundamentalDomain_subset_parallelepiped` (:312), `fract_*` (:166–206), `fundamentalDomain_ae_parallelepiped` (:397) | USE |
| Unit square has area 1 | `OrthonormalBasis.volume_parallelepiped` (`Haar/InnerProductSpace.lean:82`) + `Complex.orthonormalBasisOneI`, `toBasis_orthonormalBasisOneI` (`PiL2.lean:876, 893`) | USE; wrap as `Complex.volume_fundamentalDomain_basisOneI` |
| ℤ-span membership ↔ integer coordinates | `Basis.mem_span_iff_repr_mem` (`LinearAlgebra/Basis/Submodule.lean:191`) | USE; wrap as `PeriodPair.mem_lattice_iff_repr` |
| Period pair basis, lattice, lattice basis | `PeriodPair.basis` (`Weierstrass.lean:72`, with `basis_zero/one`), `lattice_eq_span_range_basis` (:112), `latticeBasis` (:149, `latticeBasis_zero/one`), `IsZLattice`/`DiscreteTopology` instances (:118–120) | USE |
| Translation invariance of `∫` and of `volume` | `integral_sub_right_eq_self` (to_additive of `integral_div_right_eq_self`, `Group/Integral.lean:111`), `measure_preimage_add` (to_additive of `measure_preimage_mul`, `Group/Measure.lean:230`); right-invariance on a commutative group is the instance `IsMulLeftInvariant.isMulRightInvariant` (:748) | USE |
| ℘ analytic, `℘' = d℘/dz`, `℘'² = 4℘³ − g₂℘ − g₃`, `℘' = 0 ↔ 2z ∈ Λ`, fibres of ℘, surjectivity | Mathlib `differentiableOn_weierstrassP`, `derivWeierstrassP_sq`; project `hasDerivAt_weierstrassP`, `derivWeierstrassP_eq_zero_iff` (HalfPeriods), `weierstrassP_eq_iff` (Injective:165), `exists_weierstrassP_eq` (Surjective:80) | USE |
| `Ψ₂Sq` and its shift to the depressed cubic | Mathlib `WeierstrassCurve.Ψ₂Sq`; project `eval_Ψ₂Sq_sub` (InvariantDifferential:118), `periodPair_g₂/g₃` (PeriodLattice:175/181) | USE |

## File structure (all under `FormalConjecturesTest/Period/`)

| file | content | tickets |
|---|---|---|
| `LinearAlgebra/Complex/Determinant.lean` | `Complex.det_restrictScalars_smulRight` | T001 |
| `Algebra/Module/ZLattice/Complex.lean` | `Complex.volume_fundamentalDomain_basisOneI`, `ZLattice.covolume_eq_abs_im_conj_mul`, `PeriodPair.covolume_lattice` | T002, T003 |
| `Analysis/SpecialFunctions/Elliptic/Weierstrass/HalfDomain.lean` | `mem_lattice_iff_repr`, `halfDomain` + membership API, `injOn_weierstrassP_halfDomain`, null lines, `volume_real_halfDomain`, image lemmas, `image_weierstrassP_halfDomain_ae_eq_univ` | T004–T010 |
| `Analysis/SpecialFunctions/Elliptic/Weierstrass/Area.lean` | the real derivative on `H`, the pointwise cancellation, integrability, **`integral_inv_norm_cubic`** | T011–T014 |
| `AlgebraicGeometry/EllipticCurve/ComplexPeriodIntegral.lean` | `complexPeriodIntegrand`, **`complexPeriodIntegral`**, translation to the depressed cubic, integrability, **`complexPeriodIntegral_eq_two_mul_covolume`**, `_eq_two_mul_abs_im`, `_pos` | T015–T019 |

The skeleton (every declaration `:= by sorry`) was written and built on 2026-09-10:
`lake build FormalConjecturesTest.Period.AlgebraicGeometry.EllipticCurve.ComplexPeriodIntegral`
completes (3506 jobs); the test library has `warn.sorry = false`, so sorries are silent there.

## Dependency graph

```
T001 det_restrictScalars_smulRight ──────────────────┐
T002 volume_fundamentalDomain_basisOneI → T003 covolume_eq_abs_im / covolume_lattice ─┐
T004 mem_lattice_iff_repr → T005 halfDomain API → T006 injOn ─┐                       │
                                     │                          │                       │
                                     ├→ T007 null lines → T008 volume_real_halfDomain ─┤
                                     ├→ T009 image ∪ segments = univ ──→ T010 ae_eq_univ┤
                                     ├→ T011 hasFDerivWithinAt ─────────────────────────┤
                                     └→ T012 |det|·f∘℘ = 1  (also T001) ────────────────┤
T006, T010, T011, T012 → T013 integrability on ℘(H) and on ℂ                            │
T008, T010, T011, T012, T013 → T014 integral_inv_norm_cubic ─────────────────────────────┤
T015 complexPeriodIntegrand/complexPeriodIntegral API → T016 translation to (g₂, g₃)     │
T013, T016 → T017 integrable_complexPeriodIntegrand                                      │
T014, T016 → [CLEANUP-ALL-1] → T018 complexPeriodIntegral_eq_two_mul_covolume (milestone)│
T018, T003 → T019 _eq_two_mul_abs_im, _pos ← ────────────────────────────────────────────┘
```
Parallel fronts at the start: T001, T002, T004, T015.

## Generality decisions

- `complexPeriodIntegrand`/`complexPeriodIntegral` are defined for every `WeierstrassCurve ℂ`;
  `[IsElliptic]` enters only where `periodPair` does. Nothing is stated over a general
  archimedean field: the object is the Lebesgue integral over $\mathbb{C}$.
- `ZLattice.covolume_eq_abs_im_conj_mul` is stated for an arbitrary ℤ-lattice
  `L : Submodule ℤ ℂ` with `[DiscreteTopology L] [IsZLattice ℝ L]` and any ℤ-basis
  `b : Basis (Fin 2) ℤ L` — the Mathlib-facing form; `PeriodPair.covolume_lattice` specialises.
- `Complex.det_restrictScalars_smulRight` is stated for the exact map `HasDerivAt` produces,
  `(smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ`, so the change-of-variables call needs no
  `congr`.
- The half domain is a `Set ℂ` in coordinates `L.basis.repr`, not a subtype, so Mathlib's
  `ZSpan` API (`fundamentalDomain`, `fract`, `isAddFundamentalDomain`) applies verbatim.
- The integrand uses `‖·‖⁻¹`, matching `realPeriodIntegrand := (√·)⁻¹`.

## Design decisions

1. **Normalisation.** `complexPeriodIntegral = ∫_{E(ℂ)} |ω ∧ ω̄|` exactly as the knowl defines
   $\Omega_v$, no extra factor; the factor `4` in the definition is the projection dictionary above.
   The theorem `= 2 * covolume` then reads off the knowl's "double the covolume".
2. **Half domain, not a factor `1/2`.** Mathlib's change of variables needs injectivity on the
   set, so we integrate over $H = \{s\omega_1 + t\omega_2 : s \in [0,1), t \in (0,\tfrac12)\}$ where
   $\wp$ is injective, and separately show $\operatorname{vol}(H) = \tfrac12\operatorname{covol}$
   ($F = H \sqcup (H + \omega_2/2) \sqcup$ two null segments) and $\wp(H) =^{ae} \mathbb{C}$
   (the complement is $\wp$ of the two segments, null by `addHaar_image_eq_zero_of_...`).
3. **Absolute value.** Mathlib's `PeriodPair` has no orientation (`indep` only), so the
   knowl's $2\operatorname{Im}(\bar w_1 w_2)$ becomes $2|\operatorname{Im}(\bar\omega_1\omega_2)|$.
4. **Integrability comes from the change of variables**, not from a separate decay estimate: the
   pulled-back integrand is the constant `1` on the bounded set `H`.
5. Naming: `complexPeriodIntegral` beside `leastRealPeriodIntegral`/`realPeriodIntegral`; the
   ℘-side theorem is `PeriodPair.integral_inv_norm_cubic`.

## Risks (and where they are contained)

- The change-of-variables theorem's `HasFDerivWithinAt … s x` and `InjOn` hypotheses are the
  whole reason for the half domain; T011/T006 are small, so a mismatch surfaces early.
- `ZLattice.covolume_eq_det_mul_measureReal` needs `[DecidableEq ι]` and produces
  `|b₀.det ((↑) ∘ b)|`; unfolding to `det_fin_two` goes through `Basis.det_apply` and
  `Basis.toMatrix_apply` (T003). If the coercion `((↑) ∘ b)` fights `simp`, state the matrix
  explicitly with `Matrix.of`.
- Translation invariance on ℂ needs `IsAddRightInvariant volume`; on a commutative group this is
  the priority-100 instance `IsMulLeftInvariant.isMulRightInvariant` — verified present.

## Follow-ups (not planned here)

- Analyticity of the uniformisation and a genuine surface measure on $E(\mathbb{C})$ would turn
  the projection dictionary into a theorem; out of scope.
- Upstreaming: `Complex.det_restrictScalars_smulRight`, `ZLattice.covolume_eq_abs_im_conj_mul`,
  `Complex.volume_fundamentalDomain_basisOneI` are Mathlib-ready.
