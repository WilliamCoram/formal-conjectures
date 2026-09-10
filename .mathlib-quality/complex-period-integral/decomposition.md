# Decomposition for the complex period as a single integral

## Skeleton location
Every lemma below exists as a `:= by sorry` declaration in
- `FormalConjecturesTest/Period/LinearAlgebra/Complex/Determinant.lean` (1 declaration)
- `FormalConjecturesTest/Period/Algebra/Module/ZLattice/Complex.lean` (3)
- `FormalConjecturesTest/Period/Analysis/SpecialFunctions/Elliptic/Weierstrass/HalfDomain.lean` (13)
- `FormalConjecturesTest/Period/Analysis/SpecialFunctions/Elliptic/Weierstrass/Area.lean` (5)
- `FormalConjecturesTest/Period/AlgebraicGeometry/EllipticCurve/ComplexPeriodIntegral.lean` (9)

`lake build FormalConjecturesTest.Period.AlgebraicGeometry.EllipticCurve.ComplexPeriodIntegral`
passes (3506 jobs, 2026-09-10); the only edit needed after the first draft was `open Module`
for `Basis`. The test library sets `warn.sorry = false`, so the sorries are silent.

Prior-B2 log: `.mathlib-quality/b2_log.jsonl` is empty (0 bytes). No leaf below matches a prior
B2 by name or shape; the per-leaf entries say "clean" for this reason and it is not repeated.

Sources, with the verbatim passages used below:
- [LMFDB-P] knowl `ec.period` (fetched 2026-09-10): "For a complex place given by an embedding
  $v : K \to \mathbb{C}$, we define $\Omega_v(E_v) = \int_{E_v(\mathbb{C})} \omega_E \wedge
  \overline{\omega_E}$. In terms of a basis $[w_1,w_2]$ of the period lattice of $E_v$, where
  $\Im(w_2/w_1) > 0$, we have $\Omega_v(E_v) = 2\Im(\overline{w_1}w_2)$, which is double the
  covolume of the period lattice."
- [LMFDB-PL] knowl `ec.q.period_lattice`: "the period lattice of $E$ is the set $\Lambda$ of periods
  of the invariant differential $dx/(2y+a_1x+a_3)$, which is a discrete lattice of rank 2 in
  $\mathbb{C}$. There is an isomorphism (of complex Lie groups) $\mathbb{C}/\Lambda \cong
  E(\mathbb{C})$ defined in terms of the Weierstrass $\wp$-function."
- [Mil2006, III Rem. 3.11, p. 94] (PDF p. 102 of `milne.txt`, font-decoded): "Consider the
  isomorphism $z \mapsto (\wp(z) : \wp'(z) : 1) : \mathbb{C}/\Lambda \to E(\mathbb{C})$. Since
  $x = \wp(z)$ and $y = \wp'(z)$, $dx/y = \wp'(z)dz/\wp'(z) = dz$. Thus the differential $dz$ on
  $\mathbb{C}$ corresponds to the differential $dx/y$ on $E(\mathbb{C})$."
- [Mil2006, III Prop. 2.4, p. 85]: "The two series above converge normally on compact subsets of
  $\mathbb{C}$, and their sums $\wp$ and $\wp'$ are doubly periodic meromorphic functions on
  $\mathbb{C}$ with $\wp' = d\wp/dz$."
- [Wiki-CR] *Cauchy–Riemann equations*, raw wikitext line 71: "if $f$ is complex differentiable at
  $z_0$, it is also real differentiable and the Jacobian of $f$ at $z_0$ is the complex scalar
  $f'(z_0)$, regarded as a real-linear map of $\mathbb{C}$".
- [Wiki-C] *Complex number*, § Matrix representation, raw wikitext line 271: "This isomorphism
  associates the square of the absolute value of a complex number with the determinant of the
  corresponding matrix".

Where a leaf is discharged from project code, the source is the mathematics that code formalised
(cited on the complex-period board) and the entry says so; the "quote" is then the statement of
the project lemma, which is the checkable artifact.

---

## Result R: `WeierstrassCurve.complexPeriodIntegral_eq_two_mul_covolume`

`ComplexPeriodIntegral.lean:91`
```lean
theorem complexPeriodIntegral_eq_two_mul_covolume [W.IsElliptic] :
    W.complexPeriodIntegral = 2 * ZLattice.covolume W.periodPair.lattice := by
  sorry
```

### Plain-English proof (the source's argument, expanded)
[LMFDB-P] defines $\Omega_{\mathbb{C}} = \int_{E(\mathbb{C})} |\omega\wedge\bar\omega|$ and states
its value $2\Im(\bar w_1 w_2)$, "double the covolume"; it gives no proof. The proof is:

1. *(Definition dictionary, recorded, not proved.)* Over the $x$-line the curve has two sheets and on
   each $|\omega \wedge \bar\omega| = |dx\wedge d\bar x|/|2y+a_1x+a_3|^2 = 2\,dA(x)/|\Psi_2^2(x)|$,
   so $\Omega_{\mathbb{C}} = 4\int_{\mathbb{C}} dA(x)/|\Psi_2^2(x)|$ =: `complexPeriodIntegral`.
2. *(Shift to the depressed cubic.)* $\Psi_2^2(x - b_2/12) = 4x^3 - \tfrac{c_4}{12}x -
   \tfrac{c_6}{216} = 4x^3 - g_2 x - g_3$ with $g_2, g_3$ the invariants of the period lattice
   (`eval_Ψ₂Sq_sub`, `periodPair_g₂`, `periodPair_g₃`); Lebesgue measure is translation invariant,
   so $\int_{\mathbb{C}} dA/|\Psi_2^2| = \int_{\mathbb{C}} dA/|4x^3 - g_2x - g_3|$. **(L16)**
3. *(Area formula for the curve of a lattice.)* For any period lattice,
   $\int_{\mathbb{C}} dA(x)/|4x^3 - g_2x - g_3| = \tfrac12\operatorname{covol}(\Lambda)$. **(R1)**
   Substitute $x = \wp(z)$: by [Mil2006, Rem. 3.11] $dx/y$ pulls back to $dz$, i.e. the real
   Jacobian $|\wp'(z)|^2$ of $\wp$ ([Wiki-CR], [Wiki-C]) cancels $|4\wp^3 - g_2\wp - g_3| =
   |\wp'|^2$; $\wp$ is two-to-one from a fundamental parallelogram onto $\mathbb{C}$ ([Sil2009,
   VI.3.6(b)] + evenness), so integrating over a half parallelogram $H$ on which $\wp$ is
   injective gives $\operatorname{area}(H) = \tfrac12\operatorname{covol}$, the complement of
   $\wp(H)$ being $\wp$ of two segments, a null set.
4. Combine: $\Omega = 4 \cdot \tfrac12 \operatorname{covol} = 2\operatorname{covol}$.

### Lemma tree

- **R** (internal, assembly): `complexPeriodIntegral_eq_two_mul_covolume` — `ComplexPeriodIntegral.lean:91`
  - Proof plan: `unfold complexPeriodIntegral; rw [L16, R1]; ring`.
  - Attacks on the composition: (i) *could L16 and R1 hold and R fail?* Only through the constant:
    $4 \cdot \operatorname{covol}/2 = 2\operatorname{covol}$ — checked. (ii) *Does R1's `L.g₂` match
    L16's `W.periodPair.g₂`?* L16 is stated with `W.periodPair.g₂`, `W.periodPair.g₃` and R1 is
    applied at `L := W.periodPair` — syntactically identical after `rw`. (iii) *Numerical sanity:*
    for $y^2 = x^3 - x$ (LMFDB 32.a3), the lattice is the square lattice of side $5.2441151$
    scaled: the real-period board found $\operatorname{covol} = (2.6220571 \cdot \sqrt 2)^2$…;
    more simply, for the square lattice $\Lambda = c(\mathbb{Z} + i\mathbb{Z})$ the knowl's
    $2\Im(\bar w_1 w_2) = 2c^2$ and $\operatorname{covol} = c^2$, consistent with "double".
    Verdict: SURVIVED.

- **L16** (leaf, project + mathlib): `integral_complexPeriodIntegrand` — `ComplexPeriodIntegral.lean:81`
  ```lean
  lemma integral_complexPeriodIntegrand [W.IsElliptic] :
      ∫ x : ℂ, W.complexPeriodIntegrand x
        = ∫ x : ℂ, ‖4 * x ^ 3 - W.periodPair.g₂ * x - W.periodPair.g₃‖⁻¹ := by
    sorry
  ```
  - Source: translation invariance of Lebesgue measure (Mathlib) and the project's
    `eval_Ψ₂Sq_sub` (`InvariantDifferential.lean:118`):
    > `W.Ψ₂Sq.eval (x - W.b₂ / 12) = 4 * x ^ 3 - W.c₄ / 12 * x - W.c₆ / 216`
    with `periodPair_g₂ : W.periodPair.g₂ = W.c₄ / 12`, `periodPair_g₃ : … = W.c₆ / 216`
    (`PeriodLattice.lean:175, 181`).
  - Lean ↔ source: the integrand `‖Ψ₂Sq.eval x‖⁻¹` composed with `x ↦ x - b₂/12` is
    `‖4x³ - g₂x - g₃‖⁻¹`; `integral_sub_right_eq_self` says the integral is unchanged.
  - Discharged by: `MeasureTheory.integral_sub_right_eq_self` (to_additive of
    `integral_div_right_eq_self`, `Group/Integral.lean:111`; needs `IsAddRightInvariant volume`,
    supplied on the commutative group ℂ by the priority-100 instance
    `IsMulLeftInvariant.isMulRightInvariant`, `Group/Measure.lean:748`), `eval_Ψ₂Sq_sub` (needs
    `NeZero (2 : ℂ)`, `NeZero (3 : ℂ)`, available from `CharZero`), `periodPair_g₂`, `periodPair_g₃`.
    3 project lemmas + 1 Mathlib lemma.
  - Attacks: [1] counterexample search: `eval_Ψ₂Sq_sub` is an identity for all `x`, so no value is
    excluded; no contradicting statement in the project. [2] edge cases: `b₂ = 0` (short model) —
    the shift is the identity and the claim is `Ψ₂Sq = 4x³ + 2b₄x + b₆ = 4x³ - g₂x - g₃`, true
    since then `c₄ = -24 b₄`, `c₆ = -216 b₆`; `W` singular — statement needs `IsElliptic` only for
    `periodPair`, fine. [3] hypothesis test: `IsElliptic` is necessary to name `periodPair`; nothing
    else is assumed. [4] source-drift: `eval_Ψ₂Sq_sub` is stated over any field with `2, 3 ≠ 0`;
    ℂ qualifies. [5] discharge: `integral_sub_right_eq_self (f) (g) : ∫ x, f (x - g) ∂μ = ∫ x, f x ∂μ`
    — direction is "shifted integral equals unshifted", used right-to-left; verified by reading
    `Group/Integral.lean:111`. Verdict: SURVIVED.

- **R1** (internal): `PeriodPair.integral_inv_norm_cubic` — `Area.lean:78`
  ```lean
  theorem integral_inv_norm_cubic :
      ∫ x : ℂ, ‖4 * x ^ 3 - L.g₂ * x - L.g₃‖⁻¹ = ZLattice.covolume L.lattice / 2 := by
    sorry
  ```
  - Source: [Mil2006, Rem. 3.11] (quoted above) for the pullback; [LMFDB-P] for the value.
  - Structure: `∫ x, f x = ∫ x in ℘ '' H, f x` (L10) `= ∫ z in H, |det (D℘ z)| • f (℘ z)`
    (Mathlib `integral_image_eq_integral_abs_det_fderiv_smul` with L5, L11, L6)
    `= ∫ z in H, 1` (L12, `setIntegral_congr_fun measurableSet_H`) `= volume.real H`
    (`setIntegral_const`, `smul_eq_mul`, `mul_one`) `= covol / 2` (L8).
  - Attacks on the composition: (i) *two-to-one:* if $\wp$ were injective on all of $F$ the answer
    would be $\operatorname{covol}$, not half — the half domain is exactly what encodes
    $\wp(-z) = \wp(z)$; the numerical check in R confirms the factor. (ii) *is the change of
    variables applicable with `f` merely a.e. defined?* `f` is a total function on ℂ (junk value
    `‖0‖⁻¹ = 0` at the three roots), so `integral_image_eq_integral_abs_det_fderiv_smul` applies
    with `g := f` literally. (iii) *does `∫ x in ℘ '' H` equal `∫ x` over ℂ?* Only up to the null
    complement — that is L10, via `setIntegral_congr_set` and `setIntegral_univ`. Verdict:
    SURVIVED.

  - **L5** (leaf, project): `injOn_weierstrassP_halfDomain` — `HalfDomain.lean:82`
    ```lean
    lemma injOn_weierstrassP_halfDomain : InjOn ℘[L] L.halfDomain := by
      sorry
    ```
    - Source: [Sil2009, VI.3.6(b)] / [LMFDB-PL] "$\mathbb{C}/\Lambda \cong E(\mathbb{C})$ defined
      in terms of $\wp$", realised in the project as `weierstrassP_eq_iff` (`Injective.lean:165`):
      > `℘[L] a = ℘[L] b ↔ a - b ∈ L.lattice ∨ a + b ∈ L.lattice` (for `a, b ∉ L.lattice`).
    - Lean ↔ source: for $z, w \in H$, $z - w \in \Lambda$ forces equal coordinates
      ($|s - s'| < 1$, $|t - t'| < \tfrac12$ integers ⇒ $0$), and $z + w \in \Lambda$ is impossible
      ($t + t' \in (0, 1)$ is not an integer).
    - Discharged by: `weierstrassP_eq_iff`, L4 (`mem_lattice_iff_repr`), `map_sub`/`map_add` of
      `L.basis.repr`, integer arithmetic (`Int.cast_lt`, `Int.eq_zero_of_abs_lt_one`-style:
      `abs_sub_lt_one_of_floor_eq_floor` or plain `omega` after `Int.cast` normalisation).
    - Attacks: [1] counterexample: $z = t\omega_2$, $w = (1-t)\omega_2$ have $\wp(z) = \wp(w)$
      ($z + w = \omega_2$) — but $w \notin H$ when $t \in (0,\tfrac12)$ since $1 - t > \tfrac12$;
      $z = s\omega_1 + t\omega_2$, $w = (1-s)\omega_1 + t\omega_2$: $z + w = \omega_1 + 2t\omega_2
      \notin \Lambda$ as $2t \in (0,1)$. The boundary $t = 0$ *would* break injectivity
      ($s\omega_1$ and $(1-s)\omega_1$), which is why $H$ is open in $t$. [2] edge cases:
      $s = 0$ allowed ($z = t\omega_2$): $z - w$ with $w = s'\omega_1 + t'\omega_2$ gives
      $-s' \in \mathbb{Z} \cap (-1, 0]$ ⇒ $s' = 0$; fine. [3] hypothesis test: the statement
      needs no hypothesis beyond membership in $H$; `weierstrassP_eq_iff` needs $z, w \notin
      \Lambda$, supplied by L7. [4] source-drift: the source's bijection is on
      $\mathbb{C}/\Lambda$; injectivity on $H$ is the "$\pm$" refinement, justified by evenness,
      which `weierstrassP_eq_iff`'s second disjunct expresses. [5] discharge: `weierstrassP_eq_iff`
      is sorry-free (complex-period board, `Injective.lean:165`, axioms checked). Verdict: SURVIVED.

  - **L4** (leaf, mathlib): `mem_lattice_iff_repr` — `HalfDomain.lean:59`
    ```lean
    lemma mem_lattice_iff_repr (z : ℂ) :
        z ∈ L.lattice ↔ ∀ i, ∃ n : ℤ, L.basis.repr z i = n := by
      sorry
    ```
    - Source (Mathlib): `Basis.mem_span_iff_repr_mem` (`LinearAlgebra/Basis/Submodule.lean:191`):
      > `m ∈ span R (Set.range b) ↔ ∀ i, b.repr m i ∈ Set.range (algebraMap R S)`
      and `PeriodPair.lattice_eq_span_range_basis` (`Weierstrass.lean:112`):
      > `L.lattice = Submodule.span ℤ (Set.range L.basis)`.
    - Lean ↔ source: with `R = ℤ`, `S = ℝ`, `algebraMap ℤ ℝ n = (n : ℝ)` (`algebraMap_int_eq`,
      `eq_intCast`).
    - Discharged by: the two lemmas above + `Set.mem_range` (2 lemmas).
    - Attacks: [1] counterexample: none possible, it is a rewrite of a Mathlib iff. [2] edge case
      `z = 0`: both sides true (`n = 0`). [3] hypothesis test: none to weaken. [4] source-drift:
      `mem_span_iff_repr_mem` is for a basis over `S` and span over `R ⊆ S`; `L.basis` is an
      ℝ-basis and the span is over ℤ — exactly the lemma's shape. [5] discharge verified by
      reading the statement at `Submodule.lean:191`. Verdict: SURVIVED.

  - **L6** (leaf, mathlib): `measurableSet_halfDomain` — `HalfDomain.lean:67`; also
    **L6'** `halfDomain_subset_fundamentalDomain` (:70), **L7** `notMem_lattice_of_mem_halfDomain`
    (:73), **L7'** `two_mul_notMem_lattice_of_mem_halfDomain` (:76).
    - Statements: see skeleton. `halfDomain := {z | L.basis.repr z 0 ∈ Ico 0 1 ∧ L.basis.repr z 1 ∈ Ioo 0 (1/2)}`.
    - Source: bookkeeping; no source. Discharges: L6 by `measurableSet_Ico`, `measurableSet_Ioo`,
      `(L.basis.coord i).continuous_of_finiteDimensional.measurable` (`LinearMap.continuous_of_finiteDimensional`,
      `FiniteDimension.lean:283`), `MeasurableSet.inter`, `Measurable.measurableSet_preimage`
      (≤ 3 Mathlib lemmas per conjunct). L6' by `ZSpan.mem_fundamentalDomain` (`ZLattice/Basic.lean:95`) and
      `Set.Ioo_subset_Ico_self`. L7, L7' by L4: coordinate `t ∈ (0, 1/2)` (resp. `2t ∈ (0,1)`) is not
      an integer (`Int.cast` + `Int.floor_eq_iff`-free argument: an integer `n` with `0 < n < 1`
      is impossible, `Int.lt_iff_add_one_le`/`omega` after `Int.cast_pos`, `Int.cast_lt_one`).
    - Attacks: [1] `2 * z` in L7': `L.basis.repr (2 * z) 1 = 2 * t` by `map_smul`/`two_mul` + `map_add`;
      $2t \in (0, 1)$ ✓ (this is where `t < 1/2` is used, not `t < 1`). [2] edge: `s = 0` is in
      $H$ and off $\Lambda$ since $t \ne 0$ ✓. [3] hypothesis test: dropping `0 < t` would put
      $s\omega_1$ (in particular $0 \in \Lambda$) into $H$ — necessary. [4] drift: n/a. [5] the
      cited names were read from Mathlib on 2026-09-10. Verdict: SURVIVED.

  - **L8** (internal): `volume_real_halfDomain` — `HalfDomain.lean:97`
    ```lean
    lemma volume_real_halfDomain : volume.real L.halfDomain = ZLattice.covolume L.lattice / 2 := by
      sorry
    ```
    - Structure: `covolume L.lattice = volume.real (fundamentalDomain L.basis)` (Mathlib
      `ZLattice.covolume_eq_measure_fundamentalDomain` (`Covolume.lean:84`) applied to
      `ZSpan.isAddFundamentalDomain L.basis volume` (`ZLattice/Basic.lean:350`) after rewriting
      `lattice_eq_span_range_basis`), then L9, `measureReal_def`, `ENNReal.toReal_mul`,
      finiteness (both sets lie in the compact parallelepiped:
      `ZSpan.fundamentalDomain_subset_parallelepiped` (:312), `Basis.parallelepiped` is a
      `PositiveCompacts` (`Haar/OfBasis.lean:187`, `Basis.coe_parallelepiped` :204,
      `PositiveCompacts.isCompact`), `IsCompact.measure_lt_top` (`Typeclasses/Finite.lean:336`),
      `measure_mono`).
    - Source: [LMFDB-P] "the covolume of the period lattice" = area of a fundamental parallelogram
      (Mathlib's definition agrees: `covolume_eq_measure_fundamentalDomain`).
    - Attacks on the composition: (i) `IsAddFundamentalDomain (span ℤ (range L.basis))` vs
      `L.lattice` — equal submodules, rewrite with `lattice_eq_span_range_basis` *before* applying
      `covolume_eq_measure_fundamentalDomain` (its `L` is the submodule, so `rw` in the goal's
      `covolume L.lattice`; instances `DiscreteTopology`/`IsZLattice` for the span are then needed
      — obtained by `lattice_eq_span_range_basis ▸ inferInstance` as Mathlib itself does at
      `Weierstrass.lean:118`, or by rewriting the *other* way, `← lattice_eq_span_range_basis` at the
      fundamental-domain lemma; the ticket sketch takes the second route). (ii) `ENNReal` to `ℝ`:
      `volume F = 2 * volume H` in `ℝ≥0∞`; `toReal` of both sides needs `volume H ≠ ⊤` ✓.
      Verdict: SURVIVED.

    - **L9** (leaf, mathlib): `volume_fundamentalDomain_eq_two_mul_volume_halfDomain` — `HalfDomain.lean:91`
      ```lean
      lemma volume_fundamentalDomain_eq_two_mul_volume_halfDomain :
          volume (ZSpan.fundamentalDomain L.basis) = 2 * volume L.halfDomain := by
        sorry
      ```
      - Source: elementary; $F = H \sqcup (H + \tfrac12\omega_2) \sqcup \{t = 0\} \sqcup
        \{t = \tfrac12\}$ (within $F$), the last two null (L9').
      - Discharged by: `measure_union` (`MeasureSpace.lean:112`, disjoint + measurable),
        `measure_union_le` (`OuterMeasure/Basic.lean:88`), `measure_mono`, `measure_preimage_add`
        (to_additive of `measure_preimage_mul`, `Group/Measure.lean:230`) for
        `volume ((· + ω₂/2) ⁻¹' H₂) = volume H₂`-type equalities, `measure_union_null`, L9'.
        The translate is expressed as `H₂ := {z | repr z 0 ∈ Ico 0 1 ∧ repr z 1 ∈ Ioo (1/2) 1}` with
        `H₂ = (fun z ↦ z - ω₂/2) ⁻¹' H` (coordinates: `repr (z - ω₂/2) 1 = t - 1/2` by
        `map_sub`, `Basis.repr_self` (`Basis/Defs.lean:132`), `map_smul`).
      - Attacks: [1] counterexample: a point of $F$ with $t = \tfrac12$ is in neither $H$ nor
        $H_2$ — correctly assigned to the null segment; $t \in (\tfrac12, 1)$ ⇒ $t - \tfrac12 \in
        (0, \tfrac12)$ ✓ so $H_2 = H + \omega_2/2$ exactly. [2] edge: $s$ is untouched by the
        translation ✓ (`repr (ω₂/2) 0 = 0`). [3] hypothesis test: the statement holds for every
        `PeriodPair`; nothing to weaken. [4] drift: n/a. [5] discharge: `measure_union` requires
        `Disjoint` + `MeasurableSet` of the second set — `H`, `H₂` measurable by L6's proof pattern;
        disjointness from `t < 1/2 < t'`. Two inequalities `≤` give the equality in `ℝ≥0∞`
        (`le_antisymm`). Verdict: SURVIVED.

    - **L9'** (leaf, mathlib): `volume_setOf_repr_eq` — `HalfDomain.lean:86`
      ```lean
      lemma volume_setOf_repr_eq (i : Fin 2) (c : ℝ) : volume {z : ℂ | L.basis.repr z i = c} = 0 := by
        sorry
      ```
      - Source: a line in the plane is Lebesgue-null; Mathlib `Measure.addHaar_affineSubspace`
        (`Lebesgue/EqHaar.lean:199`):
        > `(s : AffineSubspace ℝ E) (hs : s ≠ ⊤) : μ s = 0`.
      - Lean ↔ source: `{z | repr z i = c} = AffineSubspace.mk' z₀ (ker (L.basis.coord i))` for any
        `z₀` with coordinate `c` (e.g. `c • L.basis i`, `Basis.repr_self`), and it is `≠ ⊤` because
        `L.basis (1 - i)`-direction has coordinate `0 ≠ 1`… concretely `z₀ + L.basis j` for `j ≠ i`
        has coordinate `c`, but `z₀ + L.basis i` has coordinate `c + 1 ≠ c`, so the set is not `univ`.
      - Discharged by: `Measure.addHaar_affineSubspace`, `AffineSubspace.mk'`/`mem_mk'`
        (`AffineSubspace/Defs.lean:388, 397`), `LinearMap.mem_ker`; alternatively
        `Measure.addHaar_submodule` (`EqHaar.lean:172`) on `ker (coord i)` plus
        `measure_preimage_add` for the translate — the ticket sketch uses the submodule + translate
        route to avoid `AffineSubspace` API. ≤ 3 lemmas either way.
      - Attacks: [1] `c` arbitrary, including values with an empty… no: the set is never empty
        (coordinates are surjective). [2] edge `c = 0`: the set is the ℝ-line through `L.basis (1-i)`,
        a proper submodule ✓. [3] hypothesis test: none. [4] drift: n/a. [5] discharge:
        `addHaar_submodule` needs `[IsAddHaarMeasure volume]` on ℂ — ℂ's `volume` is
        `measureSpaceOfInnerProductSpace` (`Lebesgue/Complex.lean` header), an add-Haar measure ✓.
        Verdict: SURVIVED.

  - **L10** (internal): `image_weierstrassP_halfDomain_ae_eq_univ` — `HalfDomain.lean:116`
    ```lean
    lemma image_weierstrassP_halfDomain_ae_eq_univ : ℘[L] '' L.halfDomain =ᵐ[volume] univ := by
      sorry
    ```
    - Structure: `ae_eq_univ` (`OuterMeasure/AE.lean:147`: `s =ᵐ[μ] univ ↔ μ sᶜ = 0`); the
      complement is contained in `℘ '' (S₀ \ Λ) ∪ ℘ '' (S_{1/2} \ Λ)` by L10' (with
      `{t = 0 ∨ t = 1/2} = {t = 0} ∪ {t = 1/2}`), each null by L10''; `measure_union_null`,
      `measure_mono_null`.
    - Attacks on the composition: (i) the set difference `\ L.lattice` in L10' is needed because
      `℘` is not differentiable at lattice points (L10'' relies on `differentiableOn_weierstrassP`
      on `Λᶜ`) — and L10' can afford it since preimages of a value are off `Λ`. (ii) `Set.compl_subset_comm`
      bookkeeping only. Verdict: SURVIVED.

    - **L10'** (leaf, project): `image_weierstrassP_halfDomain_union_eq_univ` — `HalfDomain.lean:104`
      ```lean
      lemma image_weierstrassP_halfDomain_union_eq_univ :
          ℘[L] '' L.halfDomain ∪
            ℘[L] '' ({z | L.basis.repr z 1 = 0 ∨ L.basis.repr z 1 = 1 / 2} \ L.lattice) = univ := by
        sorry
      ```
      - Source: [LMFDB-PL]/[Sil2009, VI.3.6(b)] surjectivity of $\mathbb{C}/\Lambda \to E(\mathbb{C})$,
        realised as `exists_weierstrassP_eq` (`Surjective.lean:80`):
        > `∃ z, z ∉ L.lattice ∧ ℘[L] z = c`
        plus evenness `weierstrassP_neg` and periodicity `weierstrassP_add_coe`/`sub_coe` (Mathlib).
      - Lean ↔ source: given `x`, take `z ∉ Λ` with `℘ z = x`; `w := ZSpan.fract L.basis z` lies in
        `F` (`fract_mem_fundamentalDomain`, `ZLattice/Basic.lean:194`) and `z - w ∈ Λ`
        (`fract_apply`: `fract b m = m - floor b m`, `floor b m ∈ span`), so `℘ w = x` and `w ∉ Λ`.
        With `(s, t) = repr w`: if `t ∈ (0, 1/2)`, `w ∈ H`; if `t ∈ {0, 1/2}`, `w` is in the segment
        set; if `t ∈ (1/2, 1)`, reflect: `w' := ω₂ - w` when `s = 0`, else `w' := ω₁ + ω₂ - w`; then
        `repr w' = (0, 1 - t)` resp. `(1 - s, 1 - t) ∈ Ico 0 1 × Ioo 0 (1/2)`, so `w' ∈ H`, and
        `℘ w' = ℘ (-w) = ℘ w = x`.
      - Discharged by: `exists_weierstrassP_eq`, `ZSpan.fract_mem_fundamentalDomain`,
        `ZSpan.fract_apply` (:166, `fract b m = m - floor b m`) with `(ZSpan.floor L.basis z).2 :
        floor ∈ span` (:125, `floor` is a subtype element) — or equivalently
        `ZSpan.exist_unique_vadd_mem_fundamentalDomain` (:258) — `weierstrassP_neg`,
        `weierstrassP_add_coe`, `Basis.repr_self`, `map_add`/`map_sub`/`map_neg`.
      - Attacks: [1] counterexample: `x = 0` (value at lattice points is junk `0` — but also a
        genuine value: `exists_weierstrassP_eq 0` gives `z ∉ Λ` with `℘ z = 0`) ✓ handled uniformly.
        [2] edge: `s = 0, t ∈ (1/2, 1)`: `ω₁ + ω₂ - w` has `repr 0 = 1 ∉ Ico 0 1` — this is why
        the reflection is split on `s = 0`; `ω₂ - w` then has `repr = (0, 1 - t)` ✓. [3] hypothesis
        test: no hypotheses. [4] drift: the source gives surjectivity of `(℘, ℘')`; we use only the
        `℘`-part. [5] discharge: `exists_weierstrassP_eq` sorry-free (complex-period board).
        Verdict: SURVIVED.

    - **L10''** (leaf, mathlib): `volume_image_weierstrassP_setOf_repr_eq` — `HalfDomain.lean:111`
      ```lean
      lemma volume_image_weierstrassP_setOf_repr_eq (c : ℝ) :
          volume (℘[L] '' ({z | L.basis.repr z 1 = c} \ L.lattice)) = 0 := by
        sorry
      ```
      - Source (Mathlib): `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`
        (`Jacobian.lean:556`):
        > `(hf : DifferentiableOn ℝ f s) (hs : μ s = 0) : μ (f '' s) = 0`.
      - Lean ↔ source: `s := {t = c} \ Λ ⊆ Λᶜ`, `℘` is `DifferentiableOn ℂ ℘ Λᶜ`
        (`differentiableOn_weierstrassP`, `Weierstrass.lean:303`), hence over ℝ by
        `DifferentiableOn.restrictScalars` (`FDeriv/RestrictScalars.lean:75`) and `.mono`; the set is
        null by L9' and `measure_mono_null`.
      - Discharged by: the three lemmas above (3).
      - Attacks: [1] the theorem needs `[IsAddHaarMeasure μ]`, `FiniteDimensional ℝ ℂ`, `BorelSpace ℂ`
        — all instances present. [2] edge `c` such that the segment meets `Λ` (`c = 0`): removed by
        `\ Λ` ✓. [3] hypothesis test: `DifferentiableOn ℝ`, not `ℂ`, is what the lemma wants —
        `restrictScalars` supplies it. [4] drift: n/a. [5] discharge: signature read at
        `Jacobian.lean:556`. Verdict: SURVIVED.

  - **L11** (leaf, project + mathlib): `hasFDerivWithinAt_weierstrassP_halfDomain` — `Area.lean:52`
    ```lean
    lemma hasFDerivWithinAt_weierstrassP_halfDomain {z : ℂ} (hz : z ∈ L.halfDomain) :
        HasFDerivWithinAt ℘[L]
          ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (℘'[L] z)).restrictScalars ℝ)
          L.halfDomain z := by
      sorry
    ```
    - Source: [Mil2006, Prop. 2.4] "$\wp' = d\wp/dz$" (quoted above), as the project's
      `hasDerivAt_weierstrassP` (`HalfPeriods.lean`: `HasDerivAt ℘[L] (℘'[L] z) z` for `z ∉ Λ`).
    - Lean ↔ source: `hasDerivAt_iff_hasFDerivAt` (`Deriv/Basic.lean:198`) turns it into
      `HasFDerivAt ℘ (smulRight 1 (℘' z)) z`; `HasFDerivAt.restrictScalars ℝ`
      (`FDeriv/RestrictScalars.lean:56`) and `.hasFDerivWithinAt` give the statement; `z ∉ Λ` is L7.
    - Discharged by: 4 lemmas, all named; the "≤ 3" rule is met per step.
    - Attacks: [1] `restrictScalars` needs `[NormedSpace ℝ ℂ] [IsScalarTower ℝ ℂ ℂ]` ✓ instances.
      [2] edge: none (pointwise). [3] hypothesis: only `z ∈ H` (for `z ∉ Λ`). [4] drift: n/a.
      [5] the statement's derivative term is exactly the one the CoV theorem will see, so no
      `congr` is needed there. Verdict: SURVIVED.

  - **L12** (internal): `abs_det_mul_inv_norm_cubic_weierstrassP` — `Area.lean:60`
    ```lean
    lemma abs_det_mul_inv_norm_cubic_weierstrassP {z : ℂ} (hz : z ∈ L.halfDomain) :
        |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (℘'[L] z)).restrictScalars ℝ).det| *
          ‖4 * ℘[L] z ^ 3 - L.g₂ * ℘[L] z - L.g₃‖⁻¹ = 1 := by
      sorry
    ```
    - Source: [Mil2006, Rem. 3.11] "$dx/y = \wp'(z)dz/\wp'(z) = dz$", read as densities.
    - Structure: L1 gives `|det| = ‖℘' z‖²` (`abs_of_nonneg`); `derivWeierstrassP_sq z hz'`
      (Mathlib, `Weierstrass.lean:1075`: `℘'[L] z ^ 2 = 4 * ℘[L] z ^ 3 - L.g₂ * ℘[L] z - L.g₃`)
      rewrites the cubic to `℘' z ^ 2`, `norm_pow`, and `mul_inv_cancel₀` with `℘' z ≠ 0` from
      `derivWeierstrassP_eq_zero_iff` (HalfPeriods) and L7'.
    - Attacks on the composition: (i) sign/abs: `‖c‖² ≥ 0` so `|‖c‖²| = ‖c‖²` ✓. (ii) at a
      half-period `℘' = 0` and the identity would read `0 * ‖0‖⁻¹ = 0 ≠ 1` — such points are excluded
      from `H` by `t < 1/2` (L7') ✓; this is the one place the `1/2` is load-bearing. Verdict:
      SURVIVED.

    - **L1** (leaf, mathlib): `Complex.det_restrictScalars_smulRight` — `Determinant.lean:41`
      ```lean
      lemma det_restrictScalars_smulRight (c : ℂ) :
          ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
        sorry
      ```
      - Source: [Wiki-CR] (the Jacobian of $f$ at $z_0$ is $f'(z_0)$ as a real-linear map) and
        [Wiki-C] (the determinant of the matrix of a complex number is the square of its absolute
        value), both quoted above.
      - Lean ↔ source: the map is $z \mapsto cz$; in the basis $(1, i)$ its matrix is
        $\begin{pmatrix} a & -b \\ b & a\end{pmatrix}$, determinant $a^2 + b^2 = \|c\|^2$.
      - Discharged by: `ContinuousLinearMap.det` is an `abbrev` for `LinearMap.det ↑A`
        (`Topology/Algebra/Module/Determinant.lean:23`, unfolds by `show`), `LinearMap.det_toMatrix Complex.basisOneI`
        (`LinearAlgebra/Determinant.lean:212`), `Matrix.det_fin_two` (`Determinant/Basic.lean:807`),
        `LinearMap.toMatrix_apply`, `Complex.coe_basisOneI_repr` (`Complex/Module.lean:156`),
        `Complex.coe_basisOneI` (:160), then `Complex.sq_norm`/`Complex.normSq_apply` and `ring`.
        Slightly more than 3 lemmas, but each is a rewrite; no mathematics.
      - Attacks: [1] counterexample search: Mathlib's `ContinuousLinearMap.det_smulRight`
        (`Determinant.lean:33`) says `(smulRight f v).det = f 1 * v` for the 𝕜-linear det — over
        ℂ that is `c`, not `‖c‖²`; no contradiction, it is the determinant over a different field
        (the ℝ-det of a ℂ-linear map is the norm-square of the ℂ-det, consistent). [2] edge `c = 0`:
        both sides `0` ✓; `c = i`: matrix $\begin{pmatrix}0&-1\\1&0\end{pmatrix}$, det `1 = ‖i‖²` ✓;
        `c = -1`: det of `-id` on ℝ² is `1 = ‖-1‖²` ✓. [3] hypothesis test: none. [4] drift: n/a.
        [5] discharge: `det_toMatrix (b : Basis ι A M) (f : M →ₗ[A] M) : det (toMatrix b b f) = det f`
        read at `Determinant.lean:212`. Verdict: SURVIVED.

  - **L13** (leaf, mathlib): `integrableOn_inv_norm_cubic_image` — `Area.lean:67`, and
    **L13'** `integrable_inv_norm_cubic` — `Area.lean:71`.
    - Statements: `IntegrableOn f (℘ '' H)` and `Integrable f` for
      `f x = ‖4 * x ^ 3 - L.g₂ * x - L.g₃‖⁻¹`.
    - Source (Mathlib): `integrableOn_image_iff_integrableOn_abs_det_fderiv_smul`
      (`Jacobian.lean:1199`):
      > `IntegrableOn g (f '' s) μ ↔ IntegrableOn (fun x => |(f' x).det| • g (f x)) s μ`.
    - Lean ↔ source: with L6, L11, L5 the right side is `IntegrableOn (fun _ ↦ 1) H` after
      `IntegrableOn.congr_fun` with L12 — `integrableOn_const` (`IntegrableOn.lean:119`, needs
      `volume H ≠ ∞`, from the compact parallelepiped as in L8). L13' from L13 via
      `integrableOn_univ` (`IntegrableOn.lean:105`) and `Measure.restrict_congr_set`
      (`Restrict.lean:102`) with L10.
    - Attacks: [1] the integrand has junk value `0` at the three roots — irrelevant to integrability.
      [2] edge: none. [3] hypothesis test: `IsElliptic` is not needed — a `PeriodPair` always has
      `Δ ≠ 0`. [4] drift: n/a. [5] discharge signatures read at the cited lines. Verdict: SURVIVED.

- **L2** (leaf, mathlib): `Complex.volume_fundamentalDomain_basisOneI` — `Complex.lean:43`
  ```lean
  lemma volume_fundamentalDomain_basisOneI : volume (ZSpan.fundamentalDomain Complex.basisOneI) = 1 := by
    sorry
  ```
  - Source: the unit square has area `1`; Mathlib `OrthonormalBasis.volume_parallelepiped`
    (`Haar/InnerProductSpace.lean:82`):
    > `(b : OrthonormalBasis ι ℝ F) : volume (parallelepiped b) = 1`.
  - Lean ↔ source: `ZSpan.fundamentalDomain_ae_parallelepiped` (`ZLattice/Basic.lean:397`) gives
    `fundamentalDomain b =ᵐ[volume] parallelepiped b`; `measure_congr`; then
    `Complex.toBasis_orthonormalBasisOneI` (`PiL2.lean:893`: `orthonormalBasisOneI.toBasis = basisOneI`)
    and `OrthonormalBasis.coe_toBasis` identify `parallelepiped basisOneI` with
    `parallelepiped orthonormalBasisOneI`.
  - Discharged by: the 4 lemmas above.
  - Attacks: [1] is ℂ's `volume` the inner-product Haar measure the lemma refers to? Yes:
    `MeasureTheory/Measure/Lebesgue/Complex.lean` defines it via `measureSpaceOfInnerProductSpace`
    and proves `volume_preserving_equiv_real_prod` as a *theorem*. [2] edge: n/a. [3] hypotheses:
    none. [4] drift: n/a. [5] `fundamentalDomain_ae_parallelepiped` requires `[IsAddHaarMeasure μ]`
    ✓. Verdict: SURVIVED.

- **L3** (leaf, mathlib): `ZLattice.covolume_eq_abs_im_conj_mul` — `Complex.lean:52`; and
  **L3'** `PeriodPair.covolume_lattice` — `Complex.lean:63`.
  ```lean
  theorem covolume_eq_abs_im_conj_mul (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]
      (b : Basis (Fin 2) ℤ L) :
      covolume L = |((starRingEnd ℂ) (b 0 : ℂ) * (b 1 : ℂ)).im| := by
    sorry
  ```
  - Source: [LMFDB-P] "$2\Im(\overline{w_1}w_2)$, which is double the covolume of the period
    lattice" (so the covolume is $\Im(\bar w_1 w_2)$ when $\Im(w_2/w_1) > 0$; in general its
    absolute value).
  - Lean ↔ source: Mathlib `ZLattice.covolume_eq_det_mul_measureReal` (`Covolume.lean:115`):
    > `covolume L μ = |b₀.det ((↑) ∘ b)| * μ.real (fundamentalDomain b₀)`
    with `b₀ := Complex.basisOneI`; the second factor is `1` by L2 and `measureReal_def`;
    `Basis.det_apply` (`Determinant.lean:616`), `Basis.toMatrix_apply` (`Matrix/Basis.lean:55`),
    `Complex.coe_basisOneI_repr`, `Matrix.det_fin_two` give
    `(b 0).re * (b 1).im - (b 1).re * (b 0).im`, which is `((starRingEnd ℂ) (b 0) * b 1).im`
    (`Complex.mul_im`, `Complex.conj_re`, `Complex.conj_im`, `ring`). L3' is L3 at
    `L.latticeBasis` with `latticeBasis_zero/one` (`Weierstrass.lean:153–154`).
  - Attacks: [1] counterexample search: `covolume_eq_det_mul_measureReal` is stated with
    `[DecidableEq ι]`; `Fin 2` has it ✓. [2] edge: `b = (1, i)`: `Im(conj 1 · i) = 1` = area of the
    unit square ✓; `b = (i, 1)`: `Im(conj i · 1) = Im(-i) = -1`, absolute value `1` ✓ — this is why
    the statement carries `|·|` (Mathlib's `PeriodPair.indep` has no orientation, unlike the
    knowl's `Im(w₂/w₁) > 0`). [3] hypothesis test: `DiscreteTopology`, `IsZLattice ℝ` are exactly
    what `covolume` needs. [4] drift: matches the knowl up to the absolute value, explained.
    [5] discharge: signature of `covolume_eq_det_mul_measureReal` read at `Covolume.lean:115`.
    Verdict: SURVIVED.

- **L15** (leaf, project): `complexPeriodIntegral_eq_two_mul_abs_im` — `ComplexPeriodIntegral.lean:97`:
  `R` + L3' (`rw`). **L15'** `complexPeriodIntegral_pos` (:101): `R` + `ZLattice.covolume_pos`
  (`Covolume.lean:98`) + `mul_pos`. Attacks: trivial compositions; `covolume_pos` needs
  `[IsZLattice ℝ L]` ✓ instance from `Weierstrass.lean:120`. SURVIVED.

- **L17** (leaf, project + mathlib): `integrable_complexPeriodIntegrand` — `ComplexPeriodIntegral.lean:86`:
  L13' composed with `x ↦ x - b₂/12`: `Integrable.comp_sub_right` (to_additive of
  `Integrable.comp_div_right`, `Group/Integral.lean:144`) and `eval_Ψ₂Sq_sub`. SURVIVED (same
  attacks as L16).

- **L14** (leaf, API): `complexPeriodIntegrand_nonneg` (:68) by `inv_nonneg.mpr (norm_nonneg _)`;
  `measurable_complexPeriodIntegrand` (:71) by `(W.Ψ₂Sq.continuous.norm.measurable).inv`
  (`Polynomial.continuous`, `Continuous.norm`, `Continuous.measurable`, `Measurable.inv`).
  SURVIVED.

### Confidence gate (Step 5)
1. Every leaf is discharged from Mathlib (names and file:line verified 2026-09-10 by grep on the
   vendored Mathlib v4.33.1) or from sorry-free project code (complex-period board); the one new
   piece of infrastructure is `Complex.det_restrictScalars_smulRight`, a 2×2 determinant. ✓
2. Skeleton compiles. ✓
3. Every leaf has a source quote (or, for project discharges, the checkable project statement)
   and a match paragraph. ✓
4. Every node has an attack block with ≥ 3 categories; no attack succeeded. ✓
5. `b2_log.jsonl` empty. ✓
6. The tree mirrors the sources where the sources argue ([Mil2006, 3.11] for the pullback, the
   knowl for definition and value); the half-domain nodes are the formal content of "two-to-one
   modulo ±" and are marked as bookkeeping with no source, deliberately. LOC estimates in the
   tickets are grounded in the skeleton statements and the cited Mathlib lemma shapes, not in
   source line counts — the sources have no proofs to count. ✓
7. Single-conclusion: the only bundled statements are `halfDomain`'s membership API, kept as
   separate lemmas; no `∧`-chain conclusions. ✓
