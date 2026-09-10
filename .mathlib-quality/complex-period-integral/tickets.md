# Ticket Board: the complex period as a single integral

Board directory `.mathlib-quality/complex-period-integral/`; skeleton files (all `:= by sorry`,
compiling) under `FormalConjecturesTest/Period/`. Beastmode needs this board path explicitly.
All file paths below are relative to `FormalConjecturesTest/Period/`. Abbreviations:
**D** = `LinearAlgebra/Complex/Determinant.lean`, **Z** = `Algebra/Module/ZLattice/Complex.lean`,
**H** = `Analysis/SpecialFunctions/Elliptic/Weierstrass/HalfDomain.lean`,
**A** = `Analysis/SpecialFunctions/Elliptic/Weierstrass/Area.lean`,
**C** = `AlgebraicGeometry/EllipticCurve/ComplexPeriodIntegral.lean`.

Every skeleton statement is protected: tickets fill the `sorry` at the named line; they do not
change the statement. Mathlib names were verified on 2026-09-10 against the vendored v4.33.1;
line numbers refer to `.lake/packages/mathlib/Mathlib/`.

## Summary
- Total: 30 tickets = 19 proof/definition tickets + 9 per-file cleanups + CLEANUP-ALL-1 +
  CLEANUP-FINAL.
- Open: 0 | In Progress: 0 | Done: 30 (all closed 2026-09-10; nothing committed — the user commits).
- Parallel capacity: 4 workers at the start (T001, T002, T004, T015 are independent; files D, Z,
  H, C are independent fronts).
- Milestone: T018 `complexPeriodIntegral_eq_two_mul_covolume` (preceded by CLEANUP-ALL-1).

Generality defaults (every ticket): keep the skeleton's binders exactly; `[W.IsElliptic]` only
where `periodPair` appears; lemmas about a `PeriodPair` never assume anything beyond `L`.

---

### [T001] The real determinant of multiplication by a complex number
- **Status**: done (finished 2026-09-10) · **File**: D:41 · **Depends on**: none · **Parallel**: yes · **Type**: lemma
- **Progress**: `show LinearMap.det _ = _; rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]; simp [LinearMap.toMatrix_apply, Complex.sq_norm, Complex.normSq_apply]` — `simp` already closes the goal, the planned final `ring` is not needed.

#### Statement
```lean
lemma det_restrictScalars_smulRight (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ).det = ‖c‖ ^ 2 := by
  sorry
```
#### Proof sketch
1. `ContinuousLinearMap.det` is an `abbrev` for `LinearMap.det (A : ℂ →ₗ[ℝ] ℂ)`; `show LinearMap.det _ = _`.
2. `rw [← LinearMap.det_toMatrix Complex.basisOneI]` to pass to the `2 × 2` matrix, then
   `Matrix.det_fin_two`.
3. Each entry is `(LinearMap.toMatrix b b f) i j = b.repr (f (b j)) i` (`LinearMap.toMatrix_apply`);
   `f (b j) = c * b j` (`ContinuousLinearMap.coe_restrictScalars`, `ContinuousLinearMap.smulRight_apply`,
   `one_apply`, `smul_eq_mul`), with `b 0 = 1`, `b 1 = I` (`Complex.coe_basisOneI`) and
   `b.repr z = ![z.re, z.im]` (`Complex.coe_basisOneI_repr`). `simp` with these, `Fin.sum_univ_two`
   where needed.
4. The determinant is `c.re * c.re - (-c.im) * c.im`; close with `Complex.sq_norm`,
   `Complex.normSq_apply` and `ring`.
#### Mathlib lemmas needed
`LinearMap.det_toMatrix` (LinearAlgebra/Determinant.lean:212), `Matrix.det_fin_two`
(Matrix/Determinant/Basic.lean:807), `LinearMap.toMatrix_apply`, `Complex.coe_basisOneI_repr`
(LinearAlgebra/Complex/Module.lean:156), `Complex.coe_basisOneI` (:160), `Complex.sq_norm`
(Analysis/Complex/Norm.lean:150), `Complex.normSq_apply` (Data/Complex/Basic.lean:517).
#### Sources
[Wiki-CR] line 71 (the Jacobian of $f$ at $z_0$ is $f'(z_0)$ as a real-linear map); [Wiki-C]
line 271 (the determinant of the matrix of a complex number is the square of its absolute value).
#### Generality decision
Stated for the exact map `HasDerivAt` produces so that T012 needs no `congr`; the `LinearMap`
version is implicit in step 1. Not generalised to other `RCLike` fields — only ℂ has this matrix.

### [CLEANUP-1] Run /cleanup on D (final)
- **Status**: done (finished 2026-09-10) · **Depends on**: T001 · **Type**: cleanup
- **Progress**: done as a direct pass (not the multi-agent `/cleanup` workflow): D is one 3-line proof; docstring present, no diagnostics, lines ≤ 100.

---

### [T002] The unit square has volume one
- **Status**: done (finished 2026-09-10) · **File**: Z:43 · **Depends on**: none · **Parallel**: yes · **Type**: lemma
- **Progress**: as sketched, first try (`measure_congr (fundamentalDomain_ae_parallelepiped …)`, `← toBasis_orthonormalBasisOneI`, `OrthonormalBasis.coe_toBasis`, `volume_parallelepiped`).

#### Statement
```lean
lemma volume_fundamentalDomain_basisOneI : volume (ZSpan.fundamentalDomain Complex.basisOneI) = 1 := by
  sorry
```
#### Proof sketch
1. `rw [measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped Complex.basisOneI volume)]`.
2. `rw [← Complex.toBasis_orthonormalBasisOneI, OrthonormalBasis.coe_toBasis]` so the set is
   `parallelepiped ⇑Complex.orthonormalBasisOneI` (`Basis.coe_parallelepiped` if the
   `PositiveCompacts` coercion appears).
3. `exact Complex.orthonormalBasisOneI.volume_parallelepiped`.
#### Mathlib lemmas needed
`ZSpan.fundamentalDomain_ae_parallelepiped` (Algebra/Module/ZLattice/Basic.lean:397),
`measure_congr` (OuterMeasure/AE.lean:278), `Complex.toBasis_orthonormalBasisOneI`
(InnerProductSpace/PiL2.lean:893), `OrthonormalBasis.coe_toBasis` (:484),
`OrthonormalBasis.volume_parallelepiped` (Measure/Haar/InnerProductSpace.lean:82).
#### Sources
The unit square; ℂ's `volume` is `measureSpaceOfInnerProductSpace` (Measure/Lebesgue/Complex.lean).
#### Generality decision
Specific to `basisOneI`; it is the normalisation fact the covolume formula needs.

### [T003] Covolume of a lattice in ℂ
- **Status**: done (finished 2026-09-10) · **File**: Z:52, Z:63 · **Depends on**: T002 · **Parallel**: no · **Type**: theorem
- **Progress**: positional `covolume_eq_det_mul_measureReal L volume b Complex.basisOneI` works; the named form `(b := b) (b₀ := Complex.basisOneI)` does NOT (rw pattern `covolume L ?m` — the measure stays a metavariable). Then `measureReal_def`, T002, `ENNReal.toReal_one`, `Basis.det_apply`, `det_fin_two`; `congr 1; simp [Basis.toMatrix_apply, coe_basisOneI_repr, Complex.mul_im]; ring`.

#### Statement
```lean
theorem covolume_eq_abs_im_conj_mul (L : Submodule ℤ ℂ) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin 2) ℤ L) :
    covolume L = |((starRingEnd ℂ) (b 0 : ℂ) * (b 1 : ℂ)).im| := by
  sorry

theorem covolume_lattice (L : PeriodPair) :
    ZLattice.covolume L.lattice = |((starRingEnd ℂ) L.ω₁ * L.ω₂).im| := by
  sorry
```
#### Proof sketch
1. `rw [ZLattice.covolume_eq_det_mul_measureReal L volume b Complex.basisOneI]` (check the argument
   order at Covolume.lean:115: `(b : Basis ι ℤ L) (b₀ : Basis ι ℝ E)`; `μ` may be implicit/explicit
   via the `volume_tac` default).
2. Second factor: `measureReal_def`, T002, `ENNReal.toReal_one`, `mul_one`.
3. `Basis.det_apply`, `Matrix.det_fin_two`, `Basis.toMatrix_apply`, `Complex.coe_basisOneI_repr`,
   `Function.comp_apply`: the determinant becomes `(b 0).re * (b 1).im - (b 1).re * (b 0).im`
   (as coerced complex numbers).
4. Rewrite the target with `Complex.mul_im`, `Complex.conj_re`, `Complex.conj_im`; `congr 1; ring`.
5. `covolume_lattice`: `rw [covolume_eq_abs_im_conj_mul L.lattice L.latticeBasis, latticeBasis_zero,
   latticeBasis_one]`.
#### Mathlib lemmas needed
`ZLattice.covolume_eq_det_mul_measureReal` (Covolume.lean:115), `measureReal_def`
(MeasureSpaceDef.lean:104), `Basis.det_apply` (Determinant.lean:616), `Basis.toMatrix_apply`
(Matrix/Basis.lean:55), `Matrix.det_fin_two`, `Complex.coe_basisOneI_repr`, `Complex.mul_im`
(Data/Complex/Basic.lean:219), `Complex.conj_re` (:467), `Complex.conj_im`,
`PeriodPair.latticeBasis_zero/one` (Elliptic/Weierstrass.lean:153–154).
#### Sources
[LMFDB-P] "$2\Im(\overline{w_1}w_2)$, which is double the covolume of the period lattice".
#### Generality decision
`covolume_eq_abs_im_conj_mul` is stated for any ℤ-lattice in ℂ with any ℤ-basis, Mathlib-ready;
the absolute value is necessary because `Basis (Fin 2) ℤ L` carries no orientation.

### [CLEANUP-2] Run /cleanup on Z (after 3rd = final)
- **Status**: done (finished 2026-09-10) · **Depends on**: T003 · **Type**: cleanup
- **Progress**: done as a direct pass (not the multi-agent `/cleanup` workflow): one over-long signature reflowed (`volume_fundamentalDomain_basisOneI`); 0 diagnostics.

---

### [T004] Lattice membership in period coordinates
- **Status**: done (finished 2026-09-10) · **File**: H:59 · **Depends on**: none · **Parallel**: yes · **Type**: lemma
- **Progress**: `Basis` is `Module.Basis`; the file does not `open Module`, so the lemma must be written `Module.Basis.mem_span_iff_repr_mem`. `simp only [Set.mem_range, algebraMap_int_eq, eq_intCast, eq_comm]` closes.

#### Statement
```lean
lemma mem_lattice_iff_repr (z : ℂ) :
    z ∈ L.lattice ↔ ∀ i, ∃ n : ℤ, L.basis.repr z i = n := by
  sorry
```
#### Proof sketch
1. `rw [L.lattice_eq_span_range_basis, Basis.mem_span_iff_repr_mem]`.
2. `simp only [Set.mem_range, algebraMap_int_eq, eq_intCast]`; the two sides differ only by the
   orientation of the equation — `exact forall_congr' fun i ↦ exists_congr fun n ↦ eq_comm`.
#### Mathlib lemmas needed
`PeriodPair.lattice_eq_span_range_basis` (Weierstrass.lean:112), `Basis.mem_span_iff_repr_mem`
(LinearAlgebra/Basis/Submodule.lean:191), `algebraMap_int_eq` (Algebra/Algebra/Basic.lean:304),
`eq_intCast`, `Set.mem_range`.
#### Sources
Mathlib API only.
#### Generality decision
Stated with `∃ n : ℤ, … = n` rather than `∈ Set.range (algebraMap ℤ ℝ)` for downstream `omega`/`Int`
arithmetic.

### [T005] The half domain and its membership API
- **Status**: done (finished 2026-09-10) · **File**: H:64–79 · **Depends on**: T004 · **Parallel**: no · **Type**: def + API
- **Progress**: as sketched; measurability via `LinearMap.continuous_of_finiteDimensional (L.basis.coord i)` (the coercion unifies with `fun z ↦ L.basis.repr z i` by defeq); fundamental-domain membership via `Fin.forall_fin_two`; integer bounds via `exact_mod_cast` + `omega`.

#### Statement
```lean
def halfDomain : Set ℂ :=
  {z | L.basis.repr z 0 ∈ Ico (0 : ℝ) 1 ∧ L.basis.repr z 1 ∈ Ioo (0 : ℝ) (1 / 2)}

lemma measurableSet_halfDomain : MeasurableSet L.halfDomain := by
  sorry

lemma halfDomain_subset_fundamentalDomain : L.halfDomain ⊆ ZSpan.fundamentalDomain L.basis := by
  sorry

lemma notMem_lattice_of_mem_halfDomain {z : ℂ} (hz : z ∈ L.halfDomain) : z ∉ L.lattice := by
  sorry

lemma two_mul_notMem_lattice_of_mem_halfDomain {z : ℂ} (hz : z ∈ L.halfDomain) :
    2 * z ∉ L.lattice := by
  sorry
```
#### Proof sketch
1. `measurableSet_halfDomain`: `halfDomain = (coord 0) ⁻¹' Ico 0 1 ∩ (coord 1) ⁻¹' Ioo 0 (1/2)` with
   `coord i := L.basis.coord i : ℂ →ₗ[ℝ] ℝ`, continuous by
   `LinearMap.continuous_of_finiteDimensional`, hence measurable; `MeasurableSet.inter`,
   `measurableSet_Ico.preimage`/`Measurable.measurableSet_preimage`, `measurableSet_Ioo`. (If the
   coordinate is written `L.basis.repr z i`, note `L.basis.coord i z = L.basis.repr z i` by
   `Basis.coord_apply`.)
2. `halfDomain_subset_fundamentalDomain`: `intro z ⟨h0, h1⟩; rw [ZSpan.mem_fundamentalDomain]`;
   `Fin 2` cases: `i = 0` gives `h0`, `i = 1` gives `Set.Ioo_subset_Ico_self h1` after
   `1/2 ≤ 1` (`Ico_subset_Ico_right (by norm_num)`).
3. `notMem_lattice_of_mem_halfDomain`: `rw [mem_lattice_iff_repr]; rintro h; obtain ⟨n, hn⟩ := h 1`;
   then `0 < n < 1/2` for an integer: `Int.cast_pos`, `Int.cast_lt` after `norm_num`, `omega`.
4. `two_mul_notMem_lattice_of_mem_halfDomain`: `L.basis.repr (2 * z) 1 = 2 * L.basis.repr z 1`
   (`two_mul`, `map_add`, or `map_smul` with `(2 : ℝ) • z = 2 * z`); then `0 < n < 1` for an
   integer is impossible, as in 3.
#### Mathlib lemmas needed
`LinearMap.continuous_of_finiteDimensional` (Topology/Algebra/Module/FiniteDimension.lean:283),
`Continuous.measurable`, `measurableSet_Ico`, `measurableSet_Ioo`, `MeasurableSet.inter`,
`Basis.coord_apply`, `ZSpan.mem_fundamentalDomain` (ZLattice/Basic.lean:95), `Set.Ioo_subset_Ico_self`,
`Int.cast_pos`, `Int.cast_lt`, `map_add`/`map_smul`.
#### Sources
Bookkeeping ([Sil2009, VI.3.6(b)] for why a half domain suffices). None for the lemmas.
#### Generality decision
`Set ℂ` in `L.basis.repr` coordinates so that Mathlib's `ZSpan` API applies unchanged.

### [T006] `℘` is injective on the half domain
- **Status**: done (finished 2026-09-10) · **File**: H:82 · **Depends on**: T005 · **Parallel**: no · **Type**: lemma
- **Progress**: as sketched; `Finsupp.coe_sub`/`Pi.sub_apply` for coordinates of a difference; closing step `L.basis.repr.injective (Finsupp.ext (Fin.forall_fin_two.mpr ⟨hm, hn⟩))`.

#### Statement
```lean
lemma injOn_weierstrassP_halfDomain : InjOn ℘[L] L.halfDomain := by
  sorry
```
#### Proof sketch
1. `intro z hz w hw h`; `rcases (L.weierstrassP_eq_iff (L.notMem_lattice_of_mem_halfDomain hz)
   (L.notMem_lattice_of_mem_halfDomain hw)).mp h with hsub | hadd`.
2. Case `z - w ∈ Λ`: `rw [mem_lattice_iff_repr] at hsub`; for `i = 0`: `repr (z - w) 0 = s - s'`
   (`map_sub`) is an integer in `(-1, 1)` hence `0`; for `i = 1`: `t - t' ∈ (-1/2, 1/2)` hence `0`.
   So `repr z = repr w` (`Basis.ext_elem` / `L.basis.repr.injective` after `Finsupp.ext` on
   `Fin 2`), giving `z = w`.
3. Case `z + w ∈ Λ`: `repr (z + w) 1 = t + t' ∈ (0, 1)` cannot be an integer — contradiction.
4. Integer arithmetic: from `(n : ℝ) = s - s'` with `-1 < s - s' < 1` get `n = 0` by `Int.cast_lt`,
   `Int.cast_neg`, `Int.cast_one`, `omega`.
#### Mathlib lemmas needed
`PeriodPair.weierstrassP_eq_iff` (project, Injective.lean:165), T004, `map_sub`, `map_add`,
`Basis.ext_elem_iff`/`Basis.repr.injective`, `Int.cast_lt`, `Int.cast_neg`.
#### Sources
[Sil2009, VI.3.6(b)] / [LMFDB-PL] (bijectivity of $\mathbb{C}/\Lambda \to E(\mathbb{C})$), as
`weierstrassP_eq_iff` on the complex-period board.
#### Generality decision
As stated; the `t < 1/2` bound is what excludes the `z + w ∈ Λ` case.

### [CLEANUP-3] Run /cleanup on H (after T006)
- **Status**: done (finished 2026-09-10) · **Depends on**: T006 · **Type**: cleanup
- **Progress**: done as a direct pass (not the multi-agent `/cleanup` workflow): see CLEANUP-5 (one pass over H).

### [T007] Lines are null
- **Status**: done (finished 2026-09-10) · **File**: H:86 · **Depends on**: CLEANUP-3 · **Parallel**: yes (with T009, T011, T012) · **Type**: lemma
- **Progress**: preimage-of-kernel route (`measure_preimage_add_right`, `Measure.addHaar_submodule`). TRAP: plain `simp` rewrites the real smul `c • L.basis i` on ℂ into `↑c * L.basis i` and then cannot apply `map_smul`; use `simp only [… map_smul, Module.Basis.coord_apply …]`.

#### Statement
```lean
lemma volume_setOf_repr_eq (i : Fin 2) (c : ℝ) : volume {z : ℂ | L.basis.repr z i = c} = 0 := by
  sorry
```
#### Proof sketch
1. Let `z₀ := c • L.basis i`; then `L.basis.repr z₀ i = c` (`map_smul`, `Basis.repr_self`,
   `Finsupp.single_eq_same`). The set equals `(fun z ↦ z - z₀) ⁻¹' (LinearMap.ker (L.basis.coord i))`
   (membership: `repr (z - z₀) i = repr z i - c`, `LinearMap.mem_ker`, `Basis.coord_apply`,
   `sub_eq_zero`); `ext z; simp [...]`.
2. `rw [this, measure_preimage_add_right]`-style translation invariance — for the subtraction form use
   `Measure.measure_preimage_add` after rewriting `z - z₀ = z + (-z₀)`, or
   `MeasureTheory.measure_preimage_add_right`.
3. `Measure.addHaar_submodule volume (ker (coord i)) h` with `h : ker ≠ ⊤`: the vector `L.basis i`
   is not in the kernel (`coord i (basis i) = 1 ≠ 0`), so `ker ≠ ⊤` via `Submodule.ne_top_iff_exists`
   or `fun h ↦ by simpa [h] using …`.
#### Mathlib lemmas needed
`Measure.addHaar_submodule` (Measure/Lebesgue/EqHaar.lean:172), `measure_preimage_add`
(to_additive of Group/Measure.lean:230), `LinearMap.mem_ker` (Submodule/Ker.lean:64),
`Basis.coord_apply`, `Basis.repr_self` (Basis/Defs.lean:132), `Submodule.eq_top_iff'`.
#### Sources
A line in the plane is Lebesgue-null; Mathlib.
#### Generality decision
Both coordinates `i : Fin 2` and any `c`, though only `i = 1` is used.

### [T008] The half domain has half the covolume
- **Status**: done (finished 2026-09-10) · **File**: H:91, H:97 · **Depends on**: T007 · **Parallel**: no · **Type**: lemma
- **Progress**: as sketched (F ⊆ H ∪ H₂ ∪ two lines; H ∪ H₂ ⊆ F disjoint). TRAPS: (i) `@[simp] PeriodPair.basis_one`/`basis_zero` fire before `Basis.repr_self`, so `simp [repr_self]` on `repr (L.basis 1) 0` gets stuck at `repr ω₂ 0` — use `rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg (by decide)]`; (ii) `← sub_eq_add_neg` inside a `simp only` set turns `z + -v` into `z - v` before `map_add` can fire — rewrite the target instead. `volume_real_halfDomain`: `rwa [← lattice_eq_span_range_basis] at` the `IsAddFundamentalDomain` works (no motive problem), `ENNReal.toReal_ofNat`, `ring`.

#### Statement
```lean
lemma volume_fundamentalDomain_eq_two_mul_volume_halfDomain :
    volume (ZSpan.fundamentalDomain L.basis) = 2 * volume L.halfDomain := by
  sorry

lemma volume_real_halfDomain : volume.real L.halfDomain = ZLattice.covolume L.lattice / 2 := by
  sorry
```
#### Proof sketch
1. Define `H₂ := {z | repr z 0 ∈ Ico 0 1 ∧ repr z 1 ∈ Ioo (1/2) 1}` and show
   `H₂ = (fun z ↦ z - L.ω₂ / 2) ⁻¹' L.halfDomain` (`ext`; `repr (z - ω₂/2) = repr z - (1/2) • single 1 1`
   via `map_sub`, `map_smul`, `basis_one ▸ Basis.repr_self`; `Finsupp` evaluation at `0`, `1`).
   Hence `volume H₂ = volume L.halfDomain` (`measure_preimage_add` after `sub_eq_add_neg`).
2. Upper bound: `fundamentalDomain ⊆ halfDomain ∪ H₂ ∪ {repr · 1 = 0} ∪ {repr · 1 = 1/2}`
   (case on `t ∈ [0,1)`: `t = 0`, `0 < t < 1/2`, `t = 1/2`, `1/2 < t < 1` — `lt_or_eq_of_le`,
   `lt_trichotomy`); `measure_mono`, `measure_union_le` twice, T007 twice (`measure_union_null`),
   `add_zero`, step 1: `volume F ≤ 2 * volume H`.
3. Lower bound: `halfDomain ∪ H₂ ⊆ fundamentalDomain` (`ZSpan.mem_fundamentalDomain`, both
   `Ioo ⊆ Ico`), disjoint (`Set.disjoint_left`: `t < 1/2 < t'`), measurable (`H₂` as in T005);
   `measure_union` + `measure_mono`: `2 * volume H ≤ volume F`. `le_antisymm`.
4. `volume_real_halfDomain`: `covolume L.lattice = volume.real (fundamentalDomain L.basis)`: rewrite
   the fundamental-domain lemma's lattice with `← L.lattice_eq_span_range_basis` in
   `ZSpan.isAddFundamentalDomain L.basis volume`, apply `ZLattice.covolume_eq_measure_fundamentalDomain`;
   then `measureReal_def`, step 3's equation, `ENNReal.toReal_mul`, `ENNReal.toReal_ofNat`;
   finiteness of `volume L.halfDomain` from `halfDomain ⊆ fundamentalDomain ⊆ parallelepiped`
   (`ZSpan.fundamentalDomain_subset_parallelepiped`, `Basis.coe_parallelepiped`,
   `(L.basis.parallelepiped).isCompact.measure_lt_top`, `measure_mono`, `ne_top_of_lt`); `field_simp`.
#### Mathlib lemmas needed
`measure_union` (MeasureSpace.lean:112), `measure_union_le` (OuterMeasure/Basic.lean:88),
`measure_union_null` (:128), `measure_mono`, `measure_preimage_add`,
`ZLattice.covolume_eq_measure_fundamentalDomain` (Covolume.lean:84), `ZSpan.isAddFundamentalDomain`
(ZLattice/Basic.lean:350), `ZSpan.fundamentalDomain_subset_parallelepiped` (:312),
`Basis.coe_parallelepiped` (Haar/OfBasis.lean:204), `PositiveCompacts.isCompact`,
`IsCompact.measure_lt_top` (Typeclasses/Finite.lean:336), `measureReal_def`, `ENNReal.toReal_mul`.
#### Sources
[LMFDB-P]: the covolume is the area of a fundamental parallelogram; the halving is bookkeeping.
#### Generality decision
As stated. (Trap from the complex-period board: rewriting `L.lattice` to the span inside instance
arguments — rewrite at the `IsAddFundamentalDomain` hypothesis instead, as in step 4.)

### [T009] Every value of `℘` comes from the half domain or the two segments
- **Status**: done (finished 2026-09-10) · **File**: H:104 · **Depends on**: T005 · **Parallel**: yes · **Type**: lemma
- **Progress**: as sketched: `fract` into the parallelogram, trichotomy on `t` vs `1/2`, reflection `ω₂ - w` if `s = 0` else `ω₁ + ω₂ - w`, value via `weierstrassP_add_coe` + `weierstrassP_neg`. First try.

#### Statement
```lean
lemma image_weierstrassP_halfDomain_union_eq_univ :
    ℘[L] '' L.halfDomain ∪
      ℘[L] '' ({z | L.basis.repr z 1 = 0 ∨ L.basis.repr z 1 = 1 / 2} \ L.lattice) = univ := by
  sorry
```
#### Proof sketch
1. `refine eq_univ_of_forall fun x ↦ ?_`; `obtain ⟨z, hz, hzx⟩ := L.exists_weierstrassP_eq x`.
2. Reduce into the parallelogram: `w := ZSpan.fract L.basis z`, with
   `hw : w ∈ ZSpan.fundamentalDomain L.basis` (`ZSpan.fract_mem_fundamentalDomain`) and
   `z - w = ZSpan.floor L.basis z ∈ L.lattice` (`ZSpan.fract_apply`, `(ZSpan.floor L.basis z).2`,
   `lattice_eq_span_range_basis`). Then `℘ w = ℘ z = x` (`weierstrassP_sub_coe` with the lattice
   element `⟨z - w, _⟩`; `w = z - (z - w)`), and `w ∉ Λ` (else `z ∈ Λ`, `add_mem`).
3. Let `s := repr w 0 ∈ Ico 0 1`, `t := repr w 1 ∈ Ico 0 1` (`ZSpan.mem_fundamentalDomain`).
   `rcases` on `t = 0`, `0 < t < 1/2`, `t = 1/2`, `1/2 < t`:
   - `t ∈ (0, 1/2)`: `left; exact ⟨w, ⟨hs, ht⟩, hwx⟩`.
   - `t = 0` or `t = 1/2`: `right; exact ⟨w, ⟨Or.inl/Or.inr _, hwΛ⟩, hwx⟩`.
   - `t ∈ (1/2, 1)`: `by_cases hs0 : s = 0`; put `w' := L.ω₂ - w` (if `hs0`) or `L.ω₁ + L.ω₂ - w`;
     `repr w' = (0, 1 - t)` resp. `(1 - s, 1 - t)` (`map_sub`, `map_add`, `basis_zero/one ▸ repr_self`),
     so `w' ∈ halfDomain` (`1 - t ∈ (0, 1/2)`, `1 - s ∈ (0,1)`); `℘ w' = ℘ (-w) = ℘ w = x` by
     `weierstrassP_add_coe (-w) ⟨ω₂, ω₂_mem_lattice⟩`/`⟨ω₁ + ω₂, add_mem ω₁_mem_lattice ω₂_mem_lattice⟩`
     (rewrite `ω₂ - w = -w + ω₂`) and `weierstrassP_neg`. `left; exact ⟨w', _, _⟩`.
#### Mathlib lemmas needed
`PeriodPair.exists_weierstrassP_eq` (project, Surjective.lean:80), `ZSpan.fract_mem_fundamentalDomain`
(ZLattice/Basic.lean:194), `ZSpan.fract_apply` (:166), `ZSpan.floor` (:125),
`ZSpan.mem_fundamentalDomain` (:95), `weierstrassP_sub_coe`, `weierstrassP_add_coe`, `weierstrassP_neg`,
`ω₁_mem_lattice`, `ω₂_mem_lattice` (Weierstrass.lean:85–86), `Basis.repr_self`, `Set.eq_univ_of_forall`.
#### Sources
[LMFDB-PL]/[Sil2009, VI.3.6(b)] surjectivity, as `exists_weierstrassP_eq`; evenness of $\wp$.
#### Generality decision
The segment set is stated with `\ L.lattice` so that T010 can use differentiability of `℘`.

### [CLEANUP-4] Run /cleanup on H (after T009)
- **Status**: done (finished 2026-09-10) · **Depends on**: T009 · **Type**: cleanup
- **Progress**: done as a direct pass (not the multi-agent `/cleanup` workflow): see CLEANUP-5 (one pass over H).

### [T010] The image of the half domain is almost everything
- **Status**: done (finished 2026-09-10) · **File**: H:111, H:116 · **Depends on**: T007, T009, CLEANUP-4 · **Parallel**: no · **Type**: lemma
- **Progress**: as sketched, term-mode; `Set.diff_subset` is deprecated → `sdiff_subset`; `Set.eq_univ_iff_forall` to extract membership from T009.

#### Statement
```lean
lemma volume_image_weierstrassP_setOf_repr_eq (c : ℝ) :
    volume (℘[L] '' ({z | L.basis.repr z 1 = c} \ L.lattice)) = 0 := by
  sorry

lemma image_weierstrassP_halfDomain_ae_eq_univ : ℘[L] '' L.halfDomain =ᵐ[volume] univ := by
  sorry
```
#### Proof sketch
1. First lemma: `MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` with
   `hf : DifferentiableOn ℝ ℘[L] ({…} \ L.lattice)` from
   `(L.differentiableOn_weierstrassP.restrictScalars ℝ).mono Set.diff_subset` (the complement of
   the lattice contains the difference: `Set.diff_subset_compl`... concretely
   `fun z hz ↦ hz.2`), and `hs : volume ({…} \ L.lattice) = 0` from `measure_mono_null diff_subset (T007 1 c)`.
2. Second lemma: `rw [ae_eq_univ]`; `refine measure_mono_null ?_ (measure_union_null (T010a 0) (T010a (1/2)))`;
   the inclusion `(℘ '' H)ᶜ ⊆ ℘ '' ({t=0} \ Λ) ∪ ℘ '' ({t=1/2} \ Λ)`: from T009, `x ∉ ℘ '' H` gives
   `x ∈ ℘ '' ({t = 0 ∨ t = 1/2} \ Λ)`; split the `∨` inside the image (`Set.image_union` after
   rewriting `{t = 0 ∨ t = 1/2} \ Λ = ({t = 0} \ Λ) ∪ ({t = 1/2} \ Λ)`, `Set.union_diff_distrib`,
   `Set.setOf_or`).
#### Mathlib lemmas needed
`addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero` (Function/Jacobian.lean:556),
`PeriodPair.differentiableOn_weierstrassP` (Weierstrass.lean:303), `DifferentiableOn.restrictScalars`
(FDeriv/RestrictScalars.lean:75), `DifferentiableOn.mono`, `measure_mono_null` (OuterMeasure/Basic.lean:54),
`measure_union_null` (:128), `ae_eq_univ` (OuterMeasure/AE.lean:147), `Set.image_union`,
`Set.union_diff_distrib`, `Set.setOf_or`.
#### Sources
Mathlib; the two segments are the boundary of the half domain modulo $\pm$.
#### Generality decision
As stated.

### [CLEANUP-5] Run /cleanup on H (final)
- **Status**: done (finished 2026-09-10) · **Depends on**: T010 · **Type**: cleanup
- **Progress**: done as a direct pass (not the multi-agent `/cleanup` workflow): four missing docstrings added; the integer-in-an-interval argument that was repeated in `notMem_lattice_of_mem_halfDomain`, `two_mul_notMem_lattice_of_mem_halfDomain` and both branches of `injOn_weierstrassP_halfDomain` factored into two private lemmas `intCast_notMem_Ioo_zero_one` and `eq_zero_of_intCast_mem_Ioo` (injOn 34 → 21 lines); deprecated `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `Set.diff_subset` → `Set.sdiff_subset`; six unused `simp only` arguments removed; one long line reflowed. Verified on a scratch copy (0 diagnostics) before replacing the file.

---

### [T011] The real derivative of `℘` on the half domain
- **Status**: done (finished 2026-09-10) · **File**: A:52 · **Depends on**: T005 · **Parallel**: yes · **Type**: lemma
- **Progress**: as sketched, term-mode, first try.

#### Statement
```lean
lemma hasFDerivWithinAt_weierstrassP_halfDomain {z : ℂ} (hz : z ∈ L.halfDomain) :
    HasFDerivWithinAt ℘[L]
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (℘'[L] z)).restrictScalars ℝ)
      L.halfDomain z := by
  sorry
```
#### Proof sketch
1. `have h := L.hasDerivAt_weierstrassP (L.notMem_lattice_of_mem_halfDomain hz)`.
2. `exact ((hasDerivAt_iff_hasFDerivAt.mp h).restrictScalars ℝ).hasFDerivWithinAt`.
#### Mathlib lemmas needed
`PeriodPair.hasDerivAt_weierstrassP` (project, HalfPeriods.lean), `hasDerivAt_iff_hasFDerivAt`
(Deriv/Basic.lean:198), `HasFDerivAt.restrictScalars` (FDeriv/RestrictScalars.lean:56),
`HasFDerivAt.hasFDerivWithinAt`.
#### Sources
[Mil2006, III Prop. 2.4] "$\wp' = d\wp/dz$".
#### Generality decision
Stated on `halfDomain` (what the change of variables consumes); the pointwise `HasFDerivAt` is
step 2's intermediate.

### [T012] The pulled-back integrand is `1`
- **Status**: done (finished 2026-09-10) · **File**: A:60 · **Depends on**: T001, T005 · **Parallel**: yes · **Type**: lemma
- **Progress**: as sketched, first try.

#### Statement
```lean
lemma abs_det_mul_inv_norm_cubic_weierstrassP {z : ℂ} (hz : z ∈ L.halfDomain) :
    |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (℘'[L] z)).restrictScalars ℝ).det| *
      ‖4 * ℘[L] z ^ 3 - L.g₂ * ℘[L] z - L.g₃‖⁻¹ = 1 := by
  sorry
```
#### Proof sketch
1. `rw [Complex.det_restrictScalars_smulRight, abs_of_nonneg (by positivity)]`.
2. `rw [← L.derivWeierstrassP_sq z (L.notMem_lattice_of_mem_halfDomain hz), norm_pow]`.
3. `℘'[L] z ≠ 0`: `fun h ↦ L.two_mul_notMem_lattice_of_mem_halfDomain hz
   ((L.derivWeierstrassP_eq_zero_iff _).mp h)` (check the exact form of
   `derivWeierstrassP_eq_zero_iff` in HalfPeriods.lean: `℘'[L] z = 0 ↔ 2 * z ∈ L.lattice` for `z ∉ Λ`).
4. `exact mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr h))`.
#### Mathlib lemmas needed
T001, `PeriodPair.derivWeierstrassP_sq` (Weierstrass.lean:1075), `derivWeierstrassP_eq_zero_iff`
(project, HalfPeriods.lean), `norm_pow`, `mul_inv_cancel₀`, `norm_ne_zero_iff`, `abs_of_nonneg`.
#### Sources
[Mil2006, III Rem. 3.11] "$dx/y = \wp'(z)dz/\wp'(z) = dz$".
#### Generality decision
As stated; this is the only place where `t < 1/2` (no half-periods in `H`) is essential.

### [T013] Integrability
- **Status**: done (finished 2026-09-10) · **File**: A:67, A:71 · **Depends on**: T006, T010, T011, T012 · **Parallel**: no · **Type**: lemma
- **Progress**: `integrableOn_image_iff_…` then `(integrableOn_const hfin).congr_fun`; finiteness via `(fundamentalDomain_isBounded).isCompact_closure.measure_lt_top`; the global form via `IntegrableOn.congr_set_ae` + `integrableOn_univ` (cleaner than the planned `restrict_congr_set` rewrite).

#### Statement
```lean
lemma integrableOn_inv_norm_cubic_image :
    IntegrableOn (fun x : ℂ ↦ ‖4 * x ^ 3 - L.g₂ * x - L.g₃‖⁻¹) (℘[L] '' L.halfDomain) := by
  sorry

theorem integrable_inv_norm_cubic :
    Integrable (fun x : ℂ ↦ ‖4 * x ^ 3 - L.g₂ * x - L.g₃‖⁻¹) := by
  sorry
```
#### Proof sketch
1. `rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume L.measurableSet_halfDomain
   (fun z hz ↦ L.hasFDerivWithinAt_weierstrassP_halfDomain hz) L.injOn_weierstrassP_halfDomain]`.
2. `refine (integrableOn_const ?_).congr_fun (fun z hz ↦ ?_) L.measurableSet_halfDomain`
   (`IntegrableOn.congr_fun (h : IntegrableOn f s) (hst : EqOn f g s) (hs : MeasurableSet s)`);
   the pointwise goal is `1 = |det| • f (℘ z)`, i.e. T012 with `smul_eq_mul`, `eq_comm`.
   Finiteness `volume L.halfDomain ≠ ⊤` as in T008 step 4 (factor it into a small `have` or a
   private lemma `volume_halfDomain_ne_top` if T008 did not already expose it).
3. `integrable_inv_norm_cubic`: `rw [← integrableOn_univ, ← Measure.restrict_congr_set
   L.image_weierstrassP_halfDomain_ae_eq_univ]; exact L.integrableOn_inv_norm_cubic_image`.
#### Mathlib lemmas needed
`integrableOn_image_iff_integrableOn_abs_det_fderiv_smul` (Jacobian.lean:1199), `integrableOn_const`
(IntegrableOn.lean:119), `IntegrableOn.congr_fun`, `integrableOn_univ` (IntegrableOn.lean:105),
`Measure.restrict_congr_set` (Restrict.lean:102).
#### Sources
Mathlib; integrability is a by-product of the change of variables.
#### Generality decision
As stated; no `IsElliptic` (a `PeriodPair` always has nonzero discriminant).

### [CLEANUP-6] Run /cleanup on A (after T013)
- **Status**: done (finished 2026-09-10) · **Depends on**: T013 · **Type**: cleanup
- **Progress**: done as a direct pass (not the multi-agent `/cleanup` workflow): see CLEANUP-7.

### [T014] The area integral of the curve of a lattice
- **Status**: done (finished 2026-09-10) · **File**: A:78 · **Depends on**: T008, T010, T011, T012, CLEANUP-6 · **Parallel**: no · **Type**: theorem
- **Progress**: as sketched, a single `rw` chain; `setIntegral_congr_fun … (g := fun _ ↦ (1 : ℝ))` needs `g` named.

#### Statement
```lean
theorem integral_inv_norm_cubic :
    ∫ x : ℂ, ‖4 * x ^ 3 - L.g₂ * x - L.g₃‖⁻¹ = ZLattice.covolume L.lattice / 2 := by
  sorry
```
#### Proof sketch
1. `rw [← setIntegral_univ, ← setIntegral_congr_set L.image_weierstrassP_halfDomain_ae_eq_univ]`
   (the `∫ x in univ` form; `setIntegral_congr_set (hst : s =ᵐ[μ] t) : ∫ x in s, f x = ∫ x in t, f x`).
2. `rw [integral_image_eq_integral_abs_det_fderiv_smul volume L.measurableSet_halfDomain
   (fun z hz ↦ L.hasFDerivWithinAt_weierstrassP_halfDomain hz) L.injOn_weierstrassP_halfDomain]`.
3. `rw [setIntegral_congr_fun L.measurableSet_halfDomain (fun z hz ↦ ?_)]` with the pointwise
   goal `|det| • f (℘ z) = 1` from T012 (`smul_eq_mul`), then `setIntegral_const`, `smul_eq_mul`,
   `mul_one`, `L.volume_real_halfDomain`.
#### Mathlib lemmas needed
`setIntegral_univ` (Bochner/Set.lean:146), `setIntegral_congr_set` (:77),
`integral_image_eq_integral_abs_det_fderiv_smul` (Jacobian.lean:1213), `setIntegral_congr_fun` (:73),
`setIntegral_const` (:527), `smul_eq_mul`.
#### Sources
[Mil2006, III Rem. 3.11]; [LMFDB-P] for the value.
#### Generality decision
Any `PeriodPair`.

### [CLEANUP-7] Run /cleanup on A (final)
- **Status**: done (finished 2026-09-10) · **Depends on**: T014 · **Type**: cleanup
- **Progress**: done as a direct pass (not the multi-agent `/cleanup` workflow): docstring added to `integrable_inv_norm_cubic`; one long docstring line reflowed; 0 diagnostics.

---

### [T015] The integrand and the definition of the complex period
- **Status**: done (finished 2026-09-10) · **File**: C:66–77 · **Depends on**: none · **Parallel**: yes · **Type**: def + API
- **Progress**: as sketched, both term-mode.

#### Statement
```lean
def complexPeriodIntegrand (x : ℂ) : ℝ := ‖W.Ψ₂Sq.eval x‖⁻¹

lemma complexPeriodIntegrand_nonneg (x : ℂ) : 0 ≤ W.complexPeriodIntegrand x := by
  sorry

lemma measurable_complexPeriodIntegrand : Measurable W.complexPeriodIntegrand := by
  sorry

def complexPeriodIntegral : ℝ := 4 * ∫ x : ℂ, W.complexPeriodIntegrand x
```
#### Proof sketch
1. `complexPeriodIntegrand_nonneg`: `inv_nonneg.mpr (norm_nonneg _)`.
2. `measurable_complexPeriodIntegrand`: `(W.Ψ₂Sq.continuous.norm.measurable).inv`
   (`Polynomial.continuous`, `Continuous.norm`, `Continuous.measurable`, `Measurable.inv`).
#### Mathlib lemmas needed
`inv_nonneg`, `norm_nonneg`, `Polynomial.continuous`, `Continuous.norm`, `Continuous.measurable`,
`Measurable.inv`.
#### Sources
[LMFDB-P] (the definition); the projection dictionary in the module docstring.
#### Generality decision
Every `WeierstrassCurve ℂ`, no `IsElliptic`; mirrors `realPeriodIntegrand`.

### [T016] Translation to the depressed cubic of the period lattice
- **Status**: done (finished 2026-09-10) · **File**: C:81 · **Depends on**: T015 · **Parallel**: no · **Type**: lemma
- **Progress**: `rw [← integral_sub_right_eq_self W.complexPeriodIntegrand (W.b₂ / 12)]; simp only [complexPeriodIntegrand, eval_Ψ₂Sq_sub, periodPair_g₂, periodPair_g₃]` — `NeZero (2 : ℂ)`, `NeZero (3 : ℂ)` found automatically.

#### Statement
```lean
lemma integral_complexPeriodIntegrand [W.IsElliptic] :
    ∫ x : ℂ, W.complexPeriodIntegrand x
      = ∫ x : ℂ, ‖4 * x ^ 3 - W.periodPair.g₂ * x - W.periodPair.g₃‖⁻¹ := by
  sorry
```
#### Proof sketch
1. `rw [← integral_sub_right_eq_self (fun x ↦ W.complexPeriodIntegrand x) (W.b₂ / 12)]`.
2. `congr 1; ext x; simp only [complexPeriodIntegrand, W.eval_Ψ₂Sq_sub, W.periodPair_g₂, W.periodPair_g₃]`
   (`eval_Ψ₂Sq_sub` needs `NeZero (2 : ℂ)`, `NeZero (3 : ℂ)` — instances from `CharZero`).
#### Mathlib lemmas needed
`integral_sub_right_eq_self` (to_additive, Group/Integral.lean:111), project `eval_Ψ₂Sq_sub`
(InvariantDifferential.lean:118), `periodPair_g₂`, `periodPair_g₃` (PeriodLattice.lean:175, 181).
#### Sources
Project lemmas from the real- and complex-period boards.
#### Generality decision
As stated.

### [T017] Integrability of the complex period integrand
- **Status**: done (finished 2026-09-10) · **File**: C:86 · **Depends on**: T013, T016 · **Parallel**: no · **Type**: theorem
- **Progress**: `Integrable.comp_add_right` (not `comp_sub_right`: the identity needs `Ψ₂Sq.eval ((x + b₂/12) - b₂/12)`), then `show` the pointwise form and `rw [periodPair_g₂, periodPair_g₃, ← eval_Ψ₂Sq_sub, add_sub_cancel_right]`.

#### Statement
```lean
theorem integrable_complexPeriodIntegrand [W.IsElliptic] : Integrable W.complexPeriodIntegrand := by
  sorry
```
#### Proof sketch
1. `have h := (W.periodPair.integrable_inv_norm_cubic).comp_sub_right (W.b₂ / 12)`.
2. `refine h.congr (Eventually.of_forall fun x ↦ ?_)` (or `convert h using 2; ext x`), with the pointwise
   identity `‖4 (x - b₂/12)³ - g₂ (x - b₂/12) - g₃‖⁻¹ = ‖Ψ₂Sq.eval x‖⁻¹` — from `eval_Ψ₂Sq_sub`
   at `x - b₂/12 + b₂/12`… simpler: rewrite the *integrand* as `fun x ↦ f (x - b₂/12)` with
   `f := ‖4x³ - g₂x - g₃‖⁻¹`: `funext x; simp [complexPeriodIntegrand, ← W.eval_Ψ₂Sq_sub …]` is the
   wrong direction; instead show `W.complexPeriodIntegrand = fun x ↦ f (x + b₂/12)` using
   `eval_Ψ₂Sq_sub (x + b₂/12)` (`add_sub_cancel_right`), then `Integrable.comp_add_right`.
#### Mathlib lemmas needed
`Integrable.comp_add_right`/`comp_sub_right` (to_additive of Group/Integral.lean:144), T013,
`eval_Ψ₂Sq_sub`, `periodPair_g₂/g₃`, `add_sub_cancel_right`.
#### Sources
As T016.
#### Generality decision
As stated.

### [CLEANUP-8] Run /cleanup on C (after T017)
- **Status**: done (finished 2026-09-10) · **Depends on**: T017 · **Type**: cleanup
- **Progress**: done as a direct pass (not the multi-agent `/cleanup` workflow): see CLEANUP-9.

### [CLEANUP-ALL-1] Run /cleanup-all on the project so far
- **Status**: done (finished 2026-09-10) · **Depends on**: CLEANUP-1, -2, -5, -7, -8 · **Type**: cleanup-all
- **Progress**: done (2026-09-10): naming checked (`halfDomain`, `inv_norm_cubic`, `complexPeriodIntegrand` consistent with `leastRealPeriodIntegral`); `#print axioms` on T014, T018, T019, T003, T001: `propext`, `Classical.choice`, `Quot.sound` only; the chain `lake build …ComplexPeriodIntegral` completes with no errors or warnings.
- **Description**: naming consistency (`halfDomain`, `inv_norm_cubic`, `complexPeriodIntegrand`),
  docstring cross-references, import minimisation, `#print axioms` on T014's theorem.

### [T018] The complex period is twice the covolume — MILESTONE
- **Status**: done (finished 2026-09-10) · **File**: C:91 · **Depends on**: T014, T016, CLEANUP-ALL-1 · **Parallel**: no · **Type**: theorem
- **Progress**: as sketched: `rw [complexPeriodIntegral, integral_complexPeriodIntegrand, integral_inv_norm_cubic]; ring`.

#### Statement
```lean
theorem complexPeriodIntegral_eq_two_mul_covolume [W.IsElliptic] :
    W.complexPeriodIntegral = 2 * ZLattice.covolume W.periodPair.lattice := by
  sorry
```
#### Proof sketch
1. `rw [complexPeriodIntegral, W.integral_complexPeriodIntegrand, W.periodPair.integral_inv_norm_cubic]`.
2. `ring`.
#### Mathlib lemmas needed
None beyond T014, T016.
#### Sources
[LMFDB-P] "$\Omega_v(E_v) = 2\Im(\overline{w_1}w_2)$, which is double the covolume of the period lattice".
#### Generality decision
`[W.IsElliptic]` for `periodPair`.

### [T019] The LMFDB form and positivity
- **Status**: done (finished 2026-09-10) · **File**: C:97, C:101 · **Depends on**: T018, T003 · **Parallel**: no · **Type**: theorem
- **Progress**: as sketched; `ZLattice.covolume_pos _ _`.

#### Statement
```lean
theorem complexPeriodIntegral_eq_two_mul_abs_im [W.IsElliptic] :
    W.complexPeriodIntegral = 2 * |((starRingEnd ℂ) W.periodPair.ω₁ * W.periodPair.ω₂).im| := by
  sorry

theorem complexPeriodIntegral_pos [W.IsElliptic] : 0 < W.complexPeriodIntegral := by
  sorry
```
#### Proof sketch
1. `rw [W.complexPeriodIntegral_eq_two_mul_covolume, W.periodPair.covolume_lattice]`.
2. `rw [W.complexPeriodIntegral_eq_two_mul_covolume]; exact mul_pos two_pos (ZLattice.covolume_pos _ _)`
   (argument shape of `covolume_pos`: `(L) (μ)`, check at Covolume.lean:98).
#### Mathlib lemmas needed
`ZLattice.covolume_pos` (Covolume.lean:98), `mul_pos`, T003.
#### Sources
[LMFDB-P].
#### Generality decision
As stated.

### [CLEANUP-9] Run /cleanup on C (final)
- **Status**: done (finished 2026-09-10) · **Depends on**: T019 · **Type**: cleanup
- **Progress**: done as a direct pass (not the multi-agent `/cleanup` workflow): four docstrings added (`complexPeriodIntegrand_nonneg`, `measurable_complexPeriodIntegrand`, `integrable_complexPeriodIntegrand`, `complexPeriodIntegral_pos`); 0 diagnostics.

### [CLEANUP-FINAL] Run /cleanup-all on the whole project
- **Status**: done (finished 2026-09-10) · **Depends on**: every other ticket · **Type**: cleanup-all
- **Progress**: both CI gates green with warnings as errors — `lake --wfail build FormalConjecturesForMathlib FormalConjecturesUtil` (8901 jobs, exit 0; the root import is back to main's after the move) and `lake --wfail test` (8943 jobs, exit 0, includes all of `FormalConjecturesTest/Period` and `/Uniformisation`). `#print axioms` on `complexPeriodIntegral_eq_two_mul_covolume`, `_eq_two_mul_abs_im`, `_pos`, `integrable_complexPeriodIntegrand`, `integral_inv_norm_cubic`, `covolume_eq_abs_im_conj_mul`, `det_restrictScalars_smulRight` after the final build: `propext`, `Classical.choice`, `Quot.sound`. Final inventory: 5 files, 650 lines, 33 declarations (2 private), 0 undocumented, 0 sorries, no line over 100 characters.
- **Description**: final pass; `#print axioms` on `complexPeriodIntegral_eq_two_mul_covolume` and
  `_eq_two_mul_abs_im`; both `--wfail` CI gates (`lake --wfail build FormalConjecturesForMathlib
  FormalConjecturesUtil` is unaffected — these files live in the test library, which
  `lake --wfail test` builds); regenerate nothing (no root import file for the test library).

---

## Cadence check
Proof/definition tickets per file: D 1 (CLEANUP-1 final) · Z 2 (CLEANUP-2 final) · H 7
(CLEANUP-3 after T006, CLEANUP-4 after T009, CLEANUP-5 final) · A 4 (CLEANUP-6 after T013,
CLEANUP-7 final) · C 5 (CLEANUP-8 after T017, CLEANUP-9 final). 19 proof tickets → ⌈19/3⌉ = 7 ≤ 9
per-file cleanups ✓; CLEANUP-ALL-1 before the milestone T018 ✓; CLEANUP-FINAL last ✓.
