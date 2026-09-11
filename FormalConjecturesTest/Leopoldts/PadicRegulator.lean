/-
Copyright 2025 The Formal Conjectures Authors.

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

import FormalConjecturesTest.Leopoldts.Elementary
import FormalConjecturesTest.Leopoldts.ForMathlib.LinearAlgebra.Matrix.Rank
import FormalConjecturesTest.Leopoldts.ForMathlib.NumberTheory.NumberField.EmbeddingsBasis
import FormalConjecturesTest.Leopoldts.ForMathlib.NumberTheory.NumberField.PadicEmbeddings
import FormalConjecturesTest.Leopoldts.ForMathlib.NumberTheory.Padics.Basic
import FormalConjecturesTest.Leopoldts.ForMathlib.NumberTheory.Padics.IwasawaLog

/-!
# The `p`-adic-regulator form and the elementary form agree

`Leopoldt.leopoldt_conjecture.variants.padicRegulator` says that the matrix
`Leopoldt.logMatrix K p ε` of $p$-adic logarithms of a family `ε` of units of maximal rank lying
in $E_1$ has full rank $r_1 + r_2 - 1$. This file proves that equivalent to the elementary form
`LeopoldtConjecture` (`rank_logMatrix_eq_iff`, `forall_rank_logMatrix_iff`), and so to the
`p`-adic-relation form.

The proof goes through `iwasawaLogMatrix K p`, the matrix of Iwasawa logarithms of the
fundamental system `fundSystem K`:

* `leopoldtConjecture_iff_rank` [Nelson, Proposition 4.1]: the elementary form holds iff
  `iwasawaLogMatrix K p` has full rank. One direction takes logarithms of a relation
  $\prod_i \varepsilon_i^{a_i} = 1$; the other descends a $\mathbb{C}_p$-linear relation among the
  rows to a nonzero $\mathbb{Z}_p$-relation among the units, using that the rows lie in the
  $\mathbb{Q}_p$-span of the conjugates of an integral basis.
* `rank_logMatrix_eq`: `logMatrix K p ε` has the rank of `iwasawaLogMatrix K p`. Every conjugate
  of a unit of $E_1$ is a principal unit (`norm_map_sub_one_lt_one`), where `NormedSpace.log`
  is the Iwasawa logarithm (`PadicIwasawaLog.iwasawaLog_of_norm_sub_one_lt`); and
  $\varepsilon_i^w = \prod_j e_j^{C_{ij}}$ for an integer matrix $C$ invertible over
  $\mathbb{Q}$, so that $w \cdot$ `logMatrix K p ε` $= C \cdot$ `iwasawaLogMatrix K p`.

Both matrices use one logarithm: the Iwasawa logarithm `PadicIwasawaLog.iwasawaLog` is built on
`NormedSpace.log`, the logarithm of the statement. The statement only needs it on principal units,
but the comparison with the fundamental system needs it on every unit.
-/

open Filter IsDedekindDomain NumberField NumberField.Units

open scoped NumberField

namespace Leopoldt

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/- ## The matrix of Iwasawa logarithms of the fundamental system -/

/--
The matrix $(\log_p \sigma(\varepsilon_i))_{i, \sigma}$ of Iwasawa logarithms of the fundamental
system of units $\varepsilon_1, \dots, \varepsilon_r$ of $K$, over all embeddings
$\sigma : K \to \mathbb{C}_p$. Its rows are indexed by `Fin (rank K)` and its columns by
`K →+* ℂ_[p]`; the entries are the classical $p$-adic logarithms by
`iwasawaLogMatrix_apply_eq_div`.
-/
noncomputable def iwasawaLogMatrix : Matrix (Fin (rank K)) (K →+* ℂ_[p]) ℂ_[p] :=
  fun i σ ↦ PadicIwasawaLog.iwasawaLog p (σ (fundSystem K i : K))

/--
The entries of `iwasawaLogMatrix` are the classical $p$-adic logarithms: for any $Q \geq 1$ with
$\|\sigma(\varepsilon_i)^Q - 1\| < 1$,
$\log_p \sigma(\varepsilon_i) = \log_p(\sigma(\varepsilon_i)^Q) / Q$.
-/
@[category API, AMS 11]
theorem iwasawaLogMatrix_apply_eq_div (i : Fin (rank K)) (σ : K →+* ℂ_[p]) {Q : ℕ} (hQ : 0 < Q)
    (h : ‖σ (fundSystem K i : K) ^ Q - 1‖ < 1) :
    iwasawaLogMatrix K p i σ = NormedSpace.log (σ (fundSystem K i : K) ^ Q) / Q :=
  PadicIwasawaLog.iwasawaLog_of_hasPrincipalUnitPow
    PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one hQ h

/--
The Iwasawa logarithm turns a product of integer powers of units into a linear combination:
$\log_p \sigma(\prod_i \varepsilon_i^{n_i}) = \sum_i n_i \log_p \sigma(\varepsilon_i)$.

This uses that the Iwasawa logarithm is defined on all of $\mathbb{C}_p^\times$ and additive
there (`PadicIwasawaLog.PadicComplex.hasIwasawaLog`, `PadicIwasawaLog.iwasawaLog_prod`).
-/
@[category API, AMS 11]
theorem iwasawaLog_map_prod_zpow (σ : K →+* ℂ_[p]) (ε : Fin (rank K) → (𝓞 K)ˣ)
    (n : Fin (rank K) → ℤ) :
    PadicIwasawaLog.iwasawaLog p (σ ((∏ i, ε i ^ n i : (𝓞 K)ˣ) : K)) =
      ∑ i, (n i : ℂ_[p]) * PadicIwasawaLog.iwasawaLog p (σ (ε i : K)) := by
  have hne : ∀ i, σ (ε i : K) ≠ 0 := fun i ↦ (map_ne_zero σ).2 (coe_ne_zero _)
  have hσ : σ ((∏ i, ε i ^ n i : (𝓞 K)ˣ) : K) = ∏ i, σ (ε i : K) ^ n i := by
    have hcoe : ((∏ i, ε i ^ n i : (𝓞 K)ˣ) : K) = ∏ i, ((ε i : K) ^ n i) := by
      push_cast
      exact Finset.prod_congr rfl fun i _ ↦ coe_units_zpow (ε i) (n i)
    rw [hcoe, map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ map_zpow₀ σ _ _
  rw [hσ, PadicIwasawaLog.iwasawaLog_prod PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one
    fun i _ ↦ (PadicIwasawaLog.PadicComplex.hasIwasawaLog (hne i)).zpow (n i)]
  exact Finset.sum_congr rfl fun i _ ↦
    PadicIwasawaLog.iwasawaLog_zpow PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one
      (PadicIwasawaLog.PadicComplex.hasIwasawaLog (hne i)) (n i)

/--
**Taking logarithms in a $p$-adic relation.** If $\prod_i \varepsilon_i^{a_i} = 1$ in every
completion $K_\mathfrak{p}$ with $\mathfrak{p} \mid p$ (`IsPadicRelation`), then
$\sum_i a_i \log_p \sigma(\varepsilon_i) = 0$ for every embedding
$\sigma : K \to \mathbb{C}_p$.

This is the first half of [Nelson, Proposition 4.1]: the relation gives congruences
$\prod_i \varepsilon_i^{c_{i,n}} \equiv 1 \pmod{p^M}$ for the integer approximants
$c_{i,n}$ of $a_i$ (`eventually_dvd_of_tendsto`), hence
$\sigma(\prod_i \varepsilon_i^{c_{i,n}}) \to 1$ (`tendsto_map_of_forall_eventually_dvd`),
hence $\sum_i c_{i,n} \log_p \sigma(\varepsilon_i) \to 0$ by continuity of the logarithm at
$1$ (`PadicIwasawaLog.tendsto_iwasawaLog_of_tendsto_one`); and $c_{i,n} \to a_i$ in
$\mathbb{C}_p$ (`tendsto_appr_cast`).
-/
@[category API, AMS 11]
theorem sum_iwasawaLog_eq_zero_of_isPadicRelation {ε : Fin (rank K) → (𝓞 K)ˣ}
    {a : Fin (rank K) → ℤ_[p]} (ha : IsPadicRelation K p ε a) (σ : K →+* ℂ_[p]) :
    ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * PadicIwasawaLog.iwasawaLog p (σ (ε i : K)) = 0 := by
  set x : ℕ → (𝓞 K)ˣ := fun n ↦ ∏ i, ε i ^ (a i).appr n with hx
  -- The approximants are congruent to `1` modulo every power of `p`.
  have hdvd : ∀ M : ℕ, ∀ᶠ n in atTop, (p : 𝓞 K) ^ M ∣ ((x n : 𝓞 K) - 1) := fun M ↦
    eventually_dvd_of_tendsto (f := fun n ↦ (x n : 𝓞 K))
      (fun v hv ↦ (ha v hv).congr fun n ↦ by rw [coe_prod_pow]) M
  -- Hence they tend to `1` at every embedding, and their logarithms tend to `0`.
  have hone : Tendsto (fun n ↦ σ ((x n : 𝓞 K) : K)) atTop (nhds 1) := by
    have h0 := tendsto_map_of_forall_eventually_dvd K p (y := fun n ↦ (x n : 𝓞 K) - 1) hdvd σ
    have hfun : (fun n ↦ σ (((x n : 𝓞 K) - 1 : 𝓞 K) : K))
        = fun n ↦ σ ((x n : 𝓞 K) : K) - 1 := by
      funext n
      push_cast
      rw [map_sub, map_one]
    rw [hfun] at h0
    simpa using h0.add_const 1
  have hlog : Tendsto (fun n ↦ PadicIwasawaLog.iwasawaLog p (σ ((x n : 𝓞 K) : K))) atTop (nhds 0) :=
    PadicIwasawaLog.tendsto_iwasawaLog_of_tendsto_one
      PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one hone
  -- The logarithm of the approximant is the approximating sum.
  have heq : ∀ n, PadicIwasawaLog.iwasawaLog p (σ ((x n : 𝓞 K) : K))
      = ∑ i, (((a i).appr n : ℕ) : ℂ_[p]) * PadicIwasawaLog.iwasawaLog p (σ (ε i : K)) := by
    intro n
    have hz : x n = ∏ i, ε i ^ (((a i).appr n : ℕ) : ℤ) := by
      rw [hx]
      exact Finset.prod_congr rfl fun i _ ↦ (zpow_natCast _ _).symm
    rw [hz, iwasawaLog_map_prod_zpow K p σ ε]
    exact Finset.sum_congr rfl fun i _ ↦ by push_cast; ring
  -- Pass to the limit in each summand.
  have hsum : Tendsto (fun n ↦ ∑ i, (((a i).appr n : ℕ) : ℂ_[p]) *
      PadicIwasawaLog.iwasawaLog p (σ (ε i : K))) atTop
      (nhds (∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) *
        PadicIwasawaLog.iwasawaLog p (σ (ε i : K)))) :=
    tendsto_finsetSum _ fun i _ ↦ (tendsto_appr_cast p (a i)).mul_const _
  refine tendsto_nhds_unique hsum ?_
  simpa only [heq] using hlog

/--
If $\varepsilon_i^N = \prod_j \varepsilon_j^{C_{ij}}$ expresses the $N$-th powers of a family
of units in terms of the fundamental system, then
$N \log_p \sigma(\varepsilon_i) = \sum_j C_{ij} \log_p \sigma(\varepsilon_j)$, i.e. the
logarithm vector of $\varepsilon_i$ is the $C$-combination of the rows of `iwasawaLogMatrix`.
-/
@[category API, AMS 11]
theorem mul_iwasawaLog_map_eq_sum_iwasawaLogMatrix (σ : K →+* ℂ_[p])
    (ε : Fin (rank K) → (𝓞 K)ˣ) (C : Matrix (Fin (rank K)) (Fin (rank K)) ℤ) (N : ℕ)
    (hC : ∀ i, ε i ^ N = ∏ j, fundSystem K j ^ C i j) (i : Fin (rank K)) :
    (N : ℂ_[p]) * PadicIwasawaLog.iwasawaLog p (σ (ε i : K)) =
      ∑ j, (C i j : ℂ_[p]) * iwasawaLogMatrix K p j σ := by
  have hpow : PadicIwasawaLog.iwasawaLog p (σ ((ε i ^ N : (𝓞 K)ˣ) : K))
      = (N : ℂ_[p]) * PadicIwasawaLog.iwasawaLog p (σ (ε i : K)) := by
    rw [show ((ε i ^ N : (𝓞 K)ˣ) : K) = ((ε i : K)) ^ N by push_cast; ring, map_pow,
      PadicIwasawaLog.iwasawaLog_pow PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one
        (PadicIwasawaLog.PadicComplex.hasIwasawaLog ((map_ne_zero σ).2 (coe_ne_zero _)))]
  rw [← hpow, hC i, iwasawaLog_map_prod_zpow K p σ (fundSystem K) (C i)]
  rfl

/--
**Full rank of the logarithm matrix implies Leopoldt's conjecture** (the first half of
[Nelson, Proposition 4.1]). If the rows of `iwasawaLogMatrix K p` are `ℂ_p`-linearly independent,
then the only $p$-adic relation among a family of units of maximal rank is the trivial one.

Taking logarithms turns the relation into $\sum_i a_i \log_p \sigma(\varepsilon_i) = 0$
(`sum_iwasawaLog_eq_zero_of_isPadicRelation`); writing
$\varepsilon_i^N = \prod_j \varepsilon_j^{C_{ij}}$ makes this a relation among the rows of
`iwasawaLogMatrix` (`mul_iwasawaLog_map_eq_sum_iwasawaLogMatrix`), so $aC = 0$, and
$\det C \neq 0$ (`det_ne_zero_of_isMaxRank`) forces $a = 0$.
-/
@[category API, AMS 11]
theorem eq_zero_of_isPadicRelation_of_rank (h : (iwasawaLogMatrix K p).rank = rank K)
    {ε : Fin (rank K) → (𝓞 K)ˣ} (hmax : IsMaxRank ε) {a : Fin (rank K) → ℤ_[p]}
    (ha : IsPadicRelation K p ε a) : a = 0 := by
  classical
  have hw : torsionOrder K ≠ 0 := torsionOrder_ne_zero K
  choose ζe hζe using fun i ↦ (exist_unique_eq_mul_prod K (ε i)).exists
  set C : Matrix (Fin (rank K)) (Fin (rank K)) ℤ := fun i j ↦ (ζe i).2 j * torsionOrder K
  have hC : ∀ i, ε i ^ torsionOrder K = ∏ j, fundSystem K j ^ C i j := by
    intro i
    have hζ : ((ζe i).1 : (𝓞 K)ˣ) ^ torsionOrder K = 1 :=
      (mem_rootsOfUnity _ _).1 (by rw [rootsOfUnity_eq_torsion]; exact (ζe i).1.2)
    rw [hζe i, mul_pow, hζ, one_mul, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← zpow_natCast, ← zpow_mul]
  have hdet : C.det ≠ 0 := det_ne_zero_of_isMaxRank (isMaxRank_pow K hmax hw) C hC
  -- The rows of the logarithm matrix are linearly independent.
  have hli : LinearIndependent ℂ_[p] (iwasawaLogMatrix K p).row :=
    (Matrix.rank_eq_card_iff_linearIndependent_row _).1 (by rw [h, Fintype.card_fin])
  -- The coefficient vector `a C` annihilates every row.
  set b : Fin (rank K) → ℂ_[p] :=
    fun j ↦ ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * (C i j : ℂ_[p]) with hb
  have hzero : ∀ j, b j = 0 := by
    refine Fintype.linearIndependent_iff.1 hli b (funext fun σ ↦ ?_)
    rw [Finset.sum_apply, Pi.zero_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hlog := sum_iwasawaLog_eq_zero_of_isPadicRelation K p ha σ
    have hrow : ∑ j, b j * (iwasawaLogMatrix K p).row j σ
        = ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) *
            ((torsionOrder K : ℂ_[p]) * PadicIwasawaLog.iwasawaLog p (σ (ε i : K))) := by
      simp only [hb, Finset.sum_mul, Matrix.row]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_iwasawaLog_map_eq_sum_iwasawaLogMatrix K p σ ε C (torsionOrder K) hC i,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hfactor : ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) *
        ((torsionOrder K : ℂ_[p]) * PadicIwasawaLog.iwasawaLog p (σ (ε i : K)))
        = (torsionOrder K : ℂ_[p]) * ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) *
            PadicIwasawaLog.iwasawaLog p (σ (ε i : K)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hrow, hfactor, hlog, mul_zero]
  -- Descend the relation to `ℤ_[p]` and invert `C` by its adjugate.
  have hvec : Matrix.vecMul a ((Int.castRingHom ℤ_[p]).mapMatrix C) = 0 := by
    funext j
    have hj : algebraMap ℚ_[p] ℂ_[p]
        ((Matrix.vecMul a ((Int.castRingHom ℤ_[p]).mapMatrix C) j : ℤ_[p]) : ℚ_[p]) = 0 := by
      rw [← hzero j, hb]
      simp only [Matrix.vecMul, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply,
        eq_intCast]
      rw [PadicInt.coe_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [PadicInt.coe_mul, map_mul, PadicInt.coe_intCast, map_intCast]
    have h1 : ((Matrix.vecMul a ((Int.castRingHom ℤ_[p]).mapMatrix C) j : ℤ_[p]) : ℚ_[p]) = 0 :=
      (map_eq_zero_iff _ (algebraMap ℚ_[p] ℂ_[p]).injective).1 hj
    exact Subtype.ext h1
  have hdet' : ((Int.castRingHom ℤ_[p]).mapMatrix C).det ≠ 0 := by
    rw [← RingHom.map_det, eq_intCast, Int.cast_ne_zero]
    exact hdet
  have := congrArg (fun x ↦ Matrix.vecMul x ((Int.castRingHom ℤ_[p]).mapMatrix C).adjugate) hvec
  simp only [Matrix.vecMul_vecMul, Matrix.mul_adjugate, Matrix.vecMul_smul, Matrix.vecMul_one,
    Matrix.zero_vecMul] at this
  exact (smul_eq_zero.1 this).resolve_left hdet'

/--
**The rows of the logarithm matrix are defined over $\mathbb{Q}_p$**: each row lies in the
$\mathbb{Q}_p$-span of the conjugate vectors of an integral basis.

This is what replaces the Galois-trace descent of [Nelson, (4.4)] for a general number field.
The row is the limit of the vectors
$\sigma \mapsto (\sigma(\varepsilon_i^{Q p^k}) - 1) / (Q p^k)$
(`PadicIwasawaLog.tendsto_log`), each of which lies in the span
(`map_mem_span_integralBasis`), and the span is closed because it is finite-dimensional over the
complete field $\mathbb{Q}_p$ (`Submodule.closed_of_finiteDimensional`).
-/
@[category API, AMS 11]
theorem iwasawaLogMatrix_mem_span (i : Fin (rank K)) :
    iwasawaLogMatrix K p i ∈ Submodule.span ℚ_[p]
      (Set.range fun k ↦ fun σ : K →+* ℂ_[p] ↦ σ (integralBasis K k)) := by
  classical
  set V := Submodule.span ℚ_[p]
    (Set.range fun k ↦ fun σ : K →+* ℂ_[p] ↦ σ (integralBasis K k)) with hV
  have hfin : FiniteDimensional ℚ_[p] V :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hclosed : IsClosed (V : Set ((K →+* ℂ_[p]) → ℂ_[p])) :=
    Submodule.closed_of_finiteDimensional _
  obtain ⟨Q, hQ0, hQ⟩ := exists_pow_sub_one_dvd (K := K) (p := p)
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQ0
  have hunit : ∀ σ : K →+* ℂ_[p], ‖σ (fundSystem K i : K) ^ Q - 1‖ < 1 := by
    intro σ
    obtain ⟨c, hc⟩ := hQ (fundSystem K i)
    have h1 : σ (fundSystem K i : K) ^ Q - 1 = ((p : ℕ) : ℂ_[p]) * σ (c : K) := by
      have := congrArg (fun x : 𝓞 K ↦ σ (x : K)) hc
      simpa only [map_sub, map_mul, map_pow, map_natCast, map_one, Units.val_pow_eq_pow_val,
        RingOfIntegers.coe_eq_algebraMap] using this
    rw [h1, norm_mul]
    calc ‖((p : ℕ) : ℂ_[p])‖ * ‖σ (c : K)‖ ≤ ‖((p : ℕ) : ℂ_[p])‖ * 1 := by
          gcongr
          exact PadicIwasawaLog.PadicComplex.norm_le_one_of_isIntegral
            ((RingOfIntegers.isIntegral_coe c).map_of_comp_eq (RingHom.id ℤ) σ
              (RingHom.ext_int _ _))
      _ < 1 := by
          rw [mul_one]
          exact PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one
  -- The approximating vectors lie in `V`.
  have hterm : ∀ k : ℕ, (fun σ : K →+* ℂ_[p] ↦
      ((σ (fundSystem K i : K) ^ Q) ^ p ^ k - 1) / ((p : ℕ) : ℂ_[p]) ^ k / (Q : ℂ_[p])) ∈ V := by
    intro k
    have hx : (fun σ : K →+* ℂ_[p] ↦
        ((σ (fundSystem K i : K) ^ Q) ^ p ^ k - 1) / ((p : ℕ) : ℂ_[p]) ^ k / (Q : ℂ_[p]))
        = (algebraMap ℚ_[p] ℚ_[p] (((p : ℚ_[p]) ^ k * (Q : ℚ_[p]))⁻¹)) •
          (fun σ : K →+* ℂ_[p] ↦ σ (((fundSystem K i : K) ^ (Q * p ^ k) - 1))) := by
      funext σ
      rw [Pi.smul_apply, Algebra.smul_def, map_sub, map_pow, map_one, pow_mul]
      simp only [map_inv₀, map_mul, map_pow, map_natCast]
      field_simp
    rw [hx]
    exact Submodule.smul_mem _ _ (map_mem_span_integralBasis K p _)
  -- The row is the limit of those vectors.
  have hlim : Tendsto (fun k : ℕ ↦ (fun σ : K →+* ℂ_[p] ↦
      ((σ (fundSystem K i : K) ^ Q) ^ p ^ k - 1) / ((p : ℕ) : ℂ_[p]) ^ k / (Q : ℂ_[p])))
      atTop (nhds (iwasawaLogMatrix K p i)) := by
    refine tendsto_pi_nhds.2 fun σ ↦ ?_
    rw [iwasawaLogMatrix_apply_eq_div K p i σ hQpos (hunit σ)]
    exact (PadicIwasawaLog.tendsto_log PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one
      (hunit σ)).div_const _
  exact hclosed.mem_of_tendsto hlim (Filter.Eventually.of_forall hterm)

/--
**A `ℂ_p`-relation among the rows of the logarithm matrix descends to a nonzero `ℤ_p`-relation**
(the descent step of [Nelson, Proposition 4.1]).

The rows lie in the `ℚ_p`-span of the conjugate vectors of an integral basis
(`iwasawaLogMatrix_mem_span`), and those vectors are `ℂ_p`-linearly independent
(`NumberField.linearIndependent_embeddings_of_basis`), so a `ℂ_p`-relation among the rows is a
`ℂ_p`-relation among their `ℚ_p`-coordinate vectors, hence a `ℚ_p`-relation
(`linearIndependent_algebraMap_comp_iff`). Clearing denominators
(`IsLocalization.exist_integer_multiples`) makes the coefficients `p`-adic integers. This
replaces the decomposition-group trace of [Nelson, (4.4)], which needs `K/ℚ` Galois.
-/
@[category API, AMS 11]
theorem exists_ne_zero_sum_iwasawaLogMatrix_eq_zero
    (h : ¬ LinearIndependent ℂ_[p] (iwasawaLogMatrix K p).row) :
    ∃ a : Fin (rank K) → ℤ_[p], a ≠ 0 ∧ ∀ σ : K →+* ℂ_[p],
      ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * iwasawaLogMatrix K p i σ = 0 := by
  classical
  set w : Module.Free.ChooseBasisIndex ℤ (𝓞 K) → ((K →+* ℂ_[p]) → ℂ_[p]) :=
    fun k ↦ fun σ ↦ σ (integralBasis K k) with hw
  have hwli : LinearIndependent ℂ_[p] w :=
    NumberField.linearIndependent_embeddings_of_basis (E := ℂ_[p]) (integralBasis K)
  choose B hB using fun i ↦ (Submodule.mem_span_range_iff_exists_fun ℚ_[p]).1
    (iwasawaLogMatrix_mem_span K p i)
  have hBσ : ∀ (i : Fin (rank K)) (σ : K →+* ℂ_[p]),
      iwasawaLogMatrix K p i σ = ∑ k, algebraMap ℚ_[p] ℂ_[p] (B i k) * w k σ := by
    intro i σ
    rw [← hB i, Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [Pi.smul_apply, Algebra.smul_def]
  have hdepB : ¬ LinearIndependent ℂ_[p] (fun i ↦ algebraMap ℚ_[p] ℂ_[p] ∘ B i) := by
    rw [Fintype.linearIndependent_iff] at h ⊢
    push Not at h ⊢
    obtain ⟨c, hc, i₀, hi₀⟩ := h
    refine ⟨c, funext fun k ↦ ?_, i₀, hi₀⟩
    have hzero : ∑ k, (∑ i, c i * algebraMap ℚ_[p] ℂ_[p] (B i k)) • w k = 0 := by
      funext σ
      rw [Finset.sum_apply, Pi.zero_apply]
      have hcσ : ∑ i, c i * iwasawaLogMatrix K p i σ = 0 := by
        have hcc := congrFun hc σ
        simpa [Finset.sum_apply, Matrix.row] using hcc
      rw [← hcσ]
      simp only [Pi.smul_apply, smul_eq_mul, hBσ, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact (Finset.sum_comm).symm
    have hk := Fintype.linearIndependent_iff.1 hwli _ hzero k
    simpa using hk
  rw [linearIndependent_algebraMap_comp_iff, Fintype.linearIndependent_iff] at hdepB
  push Not at hdepB
  obtain ⟨d, hd, j₀, hj₀⟩ := hdepB
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors ℤ_[p])
    Finset.univ d
  choose a ha using fun i ↦ hm i (Finset.mem_univ i)
  have hm0 : (m : ℤ_[p]) ≠ 0 := nonZeroDivisors.coe_ne_zero m
  refine ⟨a, ?_, fun σ ↦ ?_⟩
  · intro hzero
    apply hj₀
    have h1 := ha j₀
    rw [congrFun hzero j₀] at h1
    simp only [Algebra.smul_def] at h1
    rcases mul_eq_zero.1 h1.symm with h2 | h2
    · exact absurd ((map_eq_zero_iff _ (IsFractionRing.injective ℤ_[p] ℚ_[p])).1 h2) hm0
    · exact h2
  · have hdk : ∀ k, ∑ i, d i * B i k = 0 := fun k ↦ by
      have hdd := congrFun hd k
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hdd
    have hrel : ∑ i, algebraMap ℚ_[p] ℂ_[p] (d i) * iwasawaLogMatrix K p i σ = 0 := by
      have hexp : ∑ i, algebraMap ℚ_[p] ℂ_[p] (d i) * iwasawaLogMatrix K p i σ
          = ∑ k, algebraMap ℚ_[p] ℂ_[p] (∑ i, d i * B i k) * w k σ := by
        simp only [map_sum, map_mul, hBσ, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
      rw [hexp]
      simp [hdk]
    calc ∑ i, algebraMap ℚ_[p] ℂ_[p] ((a i : ℤ_[p]) : ℚ_[p]) * iwasawaLogMatrix K p i σ
        = algebraMap ℚ_[p] ℂ_[p] (algebraMap ℤ_[p] ℚ_[p] (m : ℤ_[p])) *
            ∑ i, algebraMap ℚ_[p] ℂ_[p] (d i) * iwasawaLogMatrix K p i σ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [show ((a i : ℤ_[p]) : ℚ_[p]) = algebraMap ℤ_[p] ℚ_[p] (a i) from rfl, ha i,
            Algebra.smul_def, map_mul, mul_assoc]
      _ = 0 := by rw [hrel, mul_zero]

/--
**The approximants of a `ℤ_p`-relation tend to `1` at every embedding** (the `exp` step of
[Nelson, Proposition 4.1], replaced here by the isometry of the logarithm).

Choose `Q` with $p^2 \mid \varepsilon_i^Q - 1$, so that every $\sigma(\varepsilon_i^Q)$ lies in
the disc $\|u - 1\|^{p-1} < \|p\|$ where $\log_p$ is an isometry
(`PadicIwasawaLog.norm_log_eq`, valid for every prime, `p = 2` included). For
$x_m = \prod_i \varepsilon_i^{Q c_{i,m}}$ with $c_{i,m}$ the approximants of $a_i$, the relation
gives $\log_p \sigma(x_m) = \sum_i (c_{i,m} - a_i) \log_p \sigma(\varepsilon_i^Q)$, of norm at
most $p^{-m}$ times a constant, so $\|\sigma(x_m) - 1\| \to 0$.
-/
@[category API, AMS 11]
theorem tendsto_map_prod_pow_appr {a : Fin (rank K) → ℤ_[p]}
    (hrel : ∀ σ : K →+* ℂ_[p],
      ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * iwasawaLogMatrix K p i σ = 0)
    {Q : ℕ}
    (hQ : ∀ i, (p : 𝓞 K) ^ 2 ∣ ((fundSystem K i ^ Q : (𝓞 K)ˣ) : 𝓞 K) - 1)
    (σ : K →+* ℂ_[p]) :
    Tendsto (fun m ↦ σ ((∏ i, fundSystem K i ^ (Q * (a i).appr m) : (𝓞 K)ˣ) : K))
      atTop (nhds 1) := by
  classical
  have hppos : (0 : ℝ) < ‖((p : ℕ) : ℂ_[p])‖ := by
    have : ((p : ℕ) : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    exact norm_pos_iff.2 this
  have hplt : ‖((p : ℕ) : ℂ_[p])‖ < 1 := PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one
  -- Each `σ (ε_i ^ Q)` is a `1`-unit, in fact within `‖p‖ ^ 2` of `1`.
  set η : Fin (rank K) → ℂ_[p] := fun i ↦ σ (fundSystem K i : K) ^ Q with hη
  have hηsub : ∀ i, ‖η i - 1‖ ≤ ‖((p : ℕ) : ℂ_[p])‖ ^ 2 := by
    intro i
    obtain ⟨c, hc⟩ := hQ i
    have h1 : η i - 1 = ((p : ℕ) : ℂ_[p]) ^ 2 * σ (c : K) := by
      have := congrArg (fun x : 𝓞 K ↦ σ (x : K)) hc
      simpa only [hη, map_sub, map_mul, map_pow, map_natCast, map_one, Units.val_pow_eq_pow_val,
        RingOfIntegers.coe_eq_algebraMap] using this
    rw [h1, norm_mul, norm_pow]
    refine mul_le_of_le_one_right (by positivity) ?_
    exact PadicIwasawaLog.PadicComplex.norm_le_one_of_isIntegral
      ((RingOfIntegers.isIntegral_coe c).map_of_comp_eq (RingHom.id ℤ) σ (RingHom.ext_int _ _))
  have hdisc : ∀ i, ‖η i - 1‖ ^ (p - 1) < ‖((p : ℕ) : ℂ_[p])‖ := by
    intro i
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    calc ‖η i - 1‖ ^ (p - 1) ≤ (‖((p : ℕ) : ℂ_[p])‖ ^ 2) ^ (p - 1) := by
          gcongr
          exact hηsub i
      _ ≤ (‖((p : ℕ) : ℂ_[p])‖ ^ 2) ^ 1 :=
          pow_le_pow_of_le_one (by positivity) (by nlinarith) (by omega)
      _ < ‖((p : ℕ) : ℂ_[p])‖ := by
          rw [pow_one, sq]
          exact mul_lt_of_lt_one_left hppos hplt
  have hηne : ∀ i, η i ≠ 0 := fun i ↦
    pow_ne_zero _ ((map_ne_zero σ).2 (coe_ne_zero _))
  have hηnorm : ∀ i, ‖η i‖ ≤ 1 := fun i ↦
    le_of_eq (IsUltrametricDist.norm_eq_one_of_norm_sub_one_lt_one
      ((hηsub i).trans_lt (by nlinarith)))
  -- The approximants.
  set x : ℕ → ℂ_[p] := fun m ↦ ∏ i, η i ^ (a i).appr m with hx
  have hxeq : ∀ m, σ ((∏ i, fundSystem K i ^ (Q * (a i).appr m) : (𝓞 K)ˣ) : K) = x m := by
    intro m
    rw [hx]
    push_cast
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ ↦ by simp only [hη, map_pow, pow_mul]
  have hxsub : ∀ m, ‖x m - 1‖ ≤ ‖((p : ℕ) : ℂ_[p])‖ ^ 2 := by
    intro m
    simp only [hx]
    refine PadicIwasawaLog.norm_prod_sub_one_le (by positivity) (fun i _ ↦ ?_) (fun i _ ↦ ?_)
    · rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (hηnorm i)
    · exact (IsUltrametricDist.norm_pow_sub_one_le (hηnorm i) _).trans (hηsub i)
  have hxdisc : ∀ m, ‖x m - 1‖ ^ (p - 1) < ‖((p : ℕ) : ℂ_[p])‖ := by
    intro m
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    calc ‖x m - 1‖ ^ (p - 1) ≤ (‖((p : ℕ) : ℂ_[p])‖ ^ 2) ^ (p - 1) := by
          gcongr
          exact hxsub m
      _ ≤ (‖((p : ℕ) : ℂ_[p])‖ ^ 2) ^ 1 :=
          pow_le_pow_of_le_one (by positivity) (by nlinarith) (by omega)
      _ < ‖((p : ℕ) : ℂ_[p])‖ := by
          rw [pow_one, sq]
          exact mul_lt_of_lt_one_left hppos hplt
  -- The logarithm of the approximant, rewritten through the relation.
  have hηlog : ∀ i,
      PadicIwasawaLog.iwasawaLog p (η i) = (Q : ℂ_[p]) * iwasawaLogMatrix K p i σ := by
    intro i
    rw [hη, PadicIwasawaLog.iwasawaLog_pow PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one
      (PadicIwasawaLog.PadicComplex.hasIwasawaLog ((map_ne_zero σ).2 (coe_ne_zero _)))]
    rfl
  have hlogx : ∀ m, PadicIwasawaLog.iwasawaLog p (x m)
      = ∑ i, ((((a i).appr m : ℕ) : ℂ_[p]) - algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p])) *
          ((Q : ℂ_[p]) * iwasawaLogMatrix K p i σ) := by
    intro m
    have hprod : PadicIwasawaLog.iwasawaLog p (x m)
        = ∑ i, (((a i).appr m : ℕ) : ℂ_[p]) * ((Q : ℂ_[p]) * iwasawaLogMatrix K p i σ) := by
      simp only [hx]
      rw [PadicIwasawaLog.iwasawaLog_prod (f := fun i ↦ η i ^ (a i).appr m)
        PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one
        fun i _ ↦ (PadicIwasawaLog.PadicComplex.hasIwasawaLog (hηne i)).pow _]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [PadicIwasawaLog.iwasawaLog_pow PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one
        (PadicIwasawaLog.PadicComplex.hasIwasawaLog (hηne i)), hηlog i]
    rw [hprod]
    have hzero : ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) *
        ((Q : ℂ_[p]) * iwasawaLogMatrix K p i σ) = 0 := by
      have := hrel σ
      calc ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * ((Q : ℂ_[p]) * iwasawaLogMatrix K p i σ)
          = (Q : ℂ_[p]) * ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * iwasawaLogMatrix K p i σ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ ↦ by ring
        _ = 0 := by rw [this, mul_zero]
    rw [← sub_zero (∑ i, (((a i).appr m : ℕ) : ℂ_[p]) * ((Q : ℂ_[p]) * iwasawaLogMatrix K p i σ)),
      ← hzero, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  -- Bound the logarithm, hence the distance to `1`, by `p ^ (-m)` times a constant.
  set C : ℝ := ∑ i, ‖(Q : ℂ_[p]) * iwasawaLogMatrix K p i σ‖ with hC
  have hbound : ∀ m, ‖x m - 1‖ ≤ ((p : ℝ)⁻¹) ^ m * C := by
    intro m
    rw [← PadicIwasawaLog.norm_log_eq PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one (hxdisc m),
      ← PadicIwasawaLog.iwasawaLog_of_norm_sub_one_lt
        PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one
        (PadicIwasawaLog.norm_sub_one_lt_one_of_pow_lt
          PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one (hxdisc m)),
      hlogx m, hC, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_appr_sub_le p (a i) m) (norm_nonneg _)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hlim : Tendsto (fun m : ℕ ↦ ((p : ℝ)⁻¹) ^ m * C) atTop (nhds 0) := by
    have hinv : ((p : ℝ)⁻¹) < 1 := by
      rw [inv_lt_one₀] <;> linarith
    have h0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 hinv).mul_const C
  simp only [hxeq]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun m ↦ norm_nonneg _) hbound hlim

/--
**A nonzero `ℤ_p`-relation whose approximants are congruent to `1` refutes the elementary form of
Leopoldt's conjecture.** If $a \neq 0$ and $p^M$ divides
$\prod_i \varepsilon_i^{Q c_{i,m}} - 1$ for every $M$ and all large $m$, then the exponents
$Q c_{i_0,m}$ have $p$-adic absolute value bounded below by
$\|Q\| \cdot \|a_{i_0}\| > 0$, uniformly in $m$, so they are not divisible by an arbitrarily
large power of $p$, which is what the conjecture asserts.
-/
@[category API, AMS 11]
theorem not_leopoldtConjecture_of_forall_eventually_dvd {a : Fin (rank K) → ℤ_[p]} (ha : a ≠ 0)
    {Q : ℕ} (hQ : Q ≠ 0)
    (h : ∀ M : ℕ, ∀ᶠ m in atTop, (p : 𝓞 K) ^ M ∣
      ((∏ i, fundSystem K i ^ (Q * (a i).appr m) : (𝓞 K)ˣ) : 𝓞 K) - 1) :
    ¬ LeopoldtConjecture K p := by
  classical
  intro hL
  obtain ⟨i₀, hi₀⟩ : ∃ i, a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (funext hcon)
  have hppos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpinv : (p : ℝ)⁻¹ < 1 := by rw [inv_lt_one₀] <;> linarith
  have hQne : ((Q : ℕ) : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hQ
  set t : ℝ := ‖((Q : ℕ) : ℤ_[p])‖ * ‖a i₀‖ with ht
  have htpos : 0 < t := mul_pos (norm_pos_iff.2 hQne) (norm_pos_iff.2 hi₀)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ((p : ℝ)⁻¹) ^ N < t := exists_pow_lt_of_lt_one htpos hpinv
  have hNlt : (p : ℝ) ^ (-N : ℤ) < t := by rwa [zpow_neg, zpow_natCast, ← inv_pow]
  obtain ⟨m₀, hm₀'⟩ : ∃ m₀ : ℕ, ((p : ℝ)⁻¹) ^ m₀ < ‖a i₀‖ :=
    exists_pow_lt_of_lt_one (norm_pos_iff.2 hi₀) hpinv
  have hm₀ : (p : ℝ) ^ (-m₀ : ℤ) < ‖a i₀‖ := by rwa [zpow_neg, zpow_natCast, ← inv_pow]
  obtain ⟨M, hM⟩ := hL N
  obtain ⟨m, hmdvd, hmge⟩ := ((h M).and (eventually_ge_atTop m₀)).exists
  -- The exponent vector at stage `m` satisfies the congruence of `LeopoldtConjecture`.
  have hprod : (∏ i, fundSystem K i ^ ((Q * (a i).appr m : ℕ) : ℤ))
      = ∏ i, fundSystem K i ^ (Q * (a i).appr m) :=
    Finset.prod_congr rfl fun i _ ↦ zpow_natCast _ _
  have hexp : ((p : ℤ) ^ N) ∣ ((Q * (a i₀).appr m : ℕ) : ℤ) :=
    hM (fun i ↦ ((Q * (a i).appr m : ℕ) : ℤ)) (by rw [hprod]; exact hmdvd) i₀
  -- But the `p`-adic norm of that exponent is bounded below, uniformly in `m`.
  have hnormappr : ‖((a i₀).appr m : ℤ_[p])‖ = ‖a i₀‖ := by
    have hclose : ‖((a i₀).appr m : ℤ_[p]) - a i₀‖ < ‖a i₀‖ := by
      refine lt_of_le_of_lt ?_ hm₀
      rw [norm_sub_rev]
      refine le_trans ((PadicInt.norm_le_pow_iff_mem_span_pow _ m).2
        (PadicInt.appr_spec m (a i₀))) ?_
      exact zpow_le_zpow_right₀ hp1.le (by omega)
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (x := a i₀) (y := ((a i₀).appr m : ℤ_[p]) - a i₀) (by
        intro hcon
        exact absurd hcon.symm hclose.ne)
    rw [add_sub_cancel] at this
    rw [this, max_eq_left hclose.le]
  have hnormQ : ‖(((Q * (a i₀).appr m : ℕ) : ℤ) : ℤ_[p])‖ = t := by
    rw [ht, ← hnormappr]
    push_cast
    rw [norm_mul]
  have hle : ‖(((Q * (a i₀).appr m : ℕ) : ℤ) : ℤ_[p])‖ ≤ (p : ℝ) ^ (-N : ℤ) :=
    PadicInt.norm_int_le_pow_iff_dvd.2 (by exact_mod_cast hexp)
  rw [hnormQ] at hle
  exact absurd hle (not_le.2 hNlt)

/--
**Leopoldt's conjecture fails if the rows of the logarithm matrix satisfy a nonzero
`ℤ_p`-relation** (the second half of [Nelson, Proposition 4.1]).

Take $Q = Q_0 p$ with $\varepsilon_i^{Q_0} \equiv 1 \pmod p$ (`exists_pow_sub_one_dvd`), so that
$p^2 \mid \varepsilon_i^Q - 1$ (`pow_pow_sub_one_dvd`). Then the approximants of the relation
tend to $1$ at every embedding (`tendsto_map_prod_pow_appr`), hence are congruent to $1$ modulo
every power of $p$ (`eventually_pow_dvd_of_tendsto_map`), which contradicts the conjecture
(`not_leopoldtConjecture_of_forall_eventually_dvd`).
-/
@[category API, AMS 11]
theorem not_leopoldtConjecture_of_exists_relation {a : Fin (rank K) → ℤ_[p]} (ha : a ≠ 0)
    (hrel : ∀ σ : K →+* ℂ_[p],
      ∑ i, algebraMap ℚ_[p] ℂ_[p] (a i : ℚ_[p]) * iwasawaLogMatrix K p i σ = 0) :
    ¬ LeopoldtConjecture K p := by
  classical
  obtain ⟨Q₀, hQ₀, hQ₀'⟩ := exists_pow_sub_one_dvd (K := K) (p := p)
  set Q : ℕ := Q₀ * p with hQdef
  have hQ : Q ≠ 0 := mul_ne_zero hQ₀ (Fact.out : p.Prime).ne_zero
  have hQsq : ∀ i, (p : 𝓞 K) ^ 2 ∣ ((fundSystem K i ^ Q : (𝓞 K)ˣ) : 𝓞 K) - 1 := by
    intro i
    have hstep := pow_pow_sub_one_dvd (hQ₀' (fundSystem K i)) 1
    rw [pow_one] at hstep
    rw [hQdef, pow_mul]
    exact hstep
  refine not_leopoldtConjecture_of_forall_eventually_dvd K p ha hQ fun M ↦ ?_
  refine eventually_pow_dvd_of_tendsto_map
    (y := fun m ↦ ((∏ i, fundSystem K i ^ (Q * (a i).appr m) : (𝓞 K)ˣ) : 𝓞 K) - 1)
    (fun σ ↦ ?_) M
  have h0 := tendsto_map_prod_pow_appr K p hrel hQsq σ
  have hfun : (fun m ↦ σ ((((∏ i, fundSystem K i ^ (Q * (a i).appr m) : (𝓞 K)ˣ) : 𝓞 K) - 1 : 𝓞 K) : K))
      = fun m ↦ σ ((∏ i, fundSystem K i ^ (Q * (a i).appr m) : (𝓞 K)ˣ) : K) - 1 := by
    funext m
    push_cast
    rw [map_sub, map_one]
  rw [hfun]
  simpa using h0.sub_const 1

/--
**The equivalence of the two forms of Leopoldt's conjecture** [Nelson, Proposition 4.1]: the
elementary congruence form `LeopoldtConjecture` holds if and only if the matrix
`iwasawaLogMatrix K p` of $p$-adic logarithms of a fundamental system of units has full rank
$r_1 + r_2 - 1$.

The forward direction is by contraposition: if the rank is not full, the rows are
`ℂ_p`-dependent (`Matrix.rank_eq_card_iff_linearIndependent_row`), that dependence descends to a
nonzero `ℤ_p`-relation (`exists_ne_zero_sum_iwasawaLogMatrix_eq_zero`), and such a relation
contradicts the conjecture (`not_leopoldtConjecture_of_exists_relation`). The converse is
`eq_zero_of_isPadicRelation_of_rank` fed into `leopoldtConjecture_of_forall_isPadicRelation`.
-/
@[category API, AMS 11]
theorem leopoldtConjecture_iff_rank :
    LeopoldtConjecture K p ↔ (iwasawaLogMatrix K p).rank = rank K := by
  refine ⟨fun h ↦ ?_, fun h ↦ leopoldtConjecture_of_forall_isPadicRelation
    fun ε hmax _ a ha ↦ eq_zero_of_isPadicRelation_of_rank K p h hmax ha⟩
  by_contra hrank
  have hli : ¬ LinearIndependent ℂ_[p] (iwasawaLogMatrix K p).row := fun hli ↦
    hrank (by simpa using (Matrix.rank_eq_card_iff_linearIndependent_row _).2 hli)
  obtain ⟨a, hane, hrel⟩ := exists_ne_zero_sum_iwasawaLogMatrix_eq_zero K p hli
  exact not_leopoldtConjecture_of_exists_relation K p hane hrel h

/- ## The matrix `logMatrix K p ε` of the statement

`leopoldt_conjecture.variants.padicRegulator` is stated with `logMatrix K p ε`, the matrix of the
series logarithm `NormedSpace.log` at a family `ε` of units of maximal rank lying in $E_1$. -/

/-- A unit of $E_1$ is a principal unit at every embedding $\sigma : K \to \mathbb{C}_p$:
$u - 1$ lies in every prime above $p$, hence in the radical of $p \mathcal{O}_K$, so
$(u - 1)^n = p c$ for some $n$ and some $c \in \mathcal{O}_K$, and $\|\sigma(c)\| \le 1$. -/
@[category API, AMS 11]
theorem norm_map_sub_one_lt_one {u : (𝓞 K)ˣ} (hu : IsPrincipalUnitAbove K p u)
    (σ : K →+* ℂ_[p]) : ‖σ (u : K) - 1‖ < 1 := by
  have hp0 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  obtain ⟨n, hn⟩ : (u : 𝓞 K) - 1 ∈ (Ideal.span {(p : 𝓞 K)}).radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro J ⟨hpJ, hJ⟩
    have hpJ' : (p : 𝓞 K) ∈ J := hpJ (Ideal.mem_span_singleton_self _)
    exact hu ⟨J, hJ, fun h ↦ hp0 (by rwa [h, Ideal.mem_bot] at hpJ')⟩ hpJ'
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hn
  have hσ : (σ (u : K) - 1) ^ n = ((p : ℕ) : ℂ_[p]) * σ (c : K) := by
    have := congrArg (fun x : 𝓞 K ↦ σ (x : K)) hc
    simpa only [map_sub, map_mul, map_pow, map_natCast, map_one,
      RingOfIntegers.coe_eq_algebraMap] using this
  have hc1 : ‖σ (c : K)‖ ≤ 1 :=
    PadicIwasawaLog.PadicComplex.norm_le_one_of_isIntegral
      ((RingOfIntegers.isIntegral_coe c).map_of_comp_eq (RingHom.id ℤ) σ (RingHom.ext_int _ _))
  have hp1 : ‖((p : ℕ) : ℂ_[p])‖ < 1 := PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one
  by_contra h
  have h1 : 1 ≤ ‖σ (u : K) - 1‖ ^ n := one_le_pow₀ (not_lt.1 h)
  rw [← norm_pow, hσ, norm_mul] at h1
  nlinarith [mul_le_mul_of_nonneg_left hc1 (norm_nonneg ((p : ℕ) : ℂ_[p]))]

/--
**`logMatrix K p ε` has the rank of the Iwasawa-logarithm matrix of the fundamental system.**
Write $\varepsilon_i^w = \prod_j e_j^{C_{ij}}$, with $w$ the number of roots of unity in $K$ and
$C$ an integer matrix, invertible over $\mathbb{Q}$ since `ε` has maximal rank
(`det_ne_zero_of_isMaxRank`). On the principal units $\sigma(\varepsilon_i)$
(`norm_map_sub_one_lt_one`) `NormedSpace.log` is the Iwasawa logarithm, which turns this into
$w \cdot$ `logMatrix K p ε` $= C \cdot$ `iwasawaLogMatrix K p`.
-/
@[category API, AMS 11]
theorem rank_logMatrix_eq {ε : Fin (rank K) → (𝓞 K)ˣ} (hmax : IsMaxRank ε)
    (hone : ∀ i, IsPrincipalUnitAbove K p (ε i)) :
    (logMatrix K p ε).rank = (iwasawaLogMatrix K p).rank := by
  classical
  have hw : torsionOrder K ≠ 0 := torsionOrder_ne_zero K
  choose ζe hζe using fun i ↦ (exist_unique_eq_mul_prod K (ε i)).exists
  set C : Matrix (Fin (rank K)) (Fin (rank K)) ℤ := fun i j ↦ (ζe i).2 j * torsionOrder K
  have hC : ∀ i, ε i ^ torsionOrder K = ∏ j, fundSystem K j ^ C i j := by
    intro i
    have hζ : ((ζe i).1 : (𝓞 K)ˣ) ^ torsionOrder K = 1 :=
      (mem_rootsOfUnity _ _).1 (by rw [rootsOfUnity_eq_torsion]; exact (ζe i).1.2)
    rw [hζe i, mul_pow, hζ, one_mul, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← zpow_natCast, ← zpow_mul]
  have hdet : ((Int.castRingHom ℂ_[p]).mapMatrix C).det ≠ 0 := by
    rw [← RingHom.map_det, eq_intCast, Int.cast_ne_zero]
    exact det_ne_zero_of_isMaxRank (isMaxRank_pow K hmax hw) C hC
  have hmat : (torsionOrder K : ℂ_[p]) • logMatrix K p ε =
      (Int.castRingHom ℂ_[p]).mapMatrix C * iwasawaLogMatrix K p := by
    ext i σ
    show (torsionOrder K : ℂ_[p]) * NormedSpace.log (σ (ε i : K)) =
      ∑ j, (C i j : ℂ_[p]) * iwasawaLogMatrix K p j σ
    rw [← PadicIwasawaLog.iwasawaLog_of_norm_sub_one_lt
      PadicIwasawaLog.PadicComplex.norm_natCast_p_lt_one (norm_map_sub_one_lt_one K p (hone i) σ)]
    exact mul_iwasawaLog_map_eq_sum_iwasawaLogMatrix K p σ ε C _ hC i
  have hw' : ((torsionOrder K : ℂ_[p]) •
      (1 : Matrix (Fin (rank K)) (Fin (rank K)) ℂ_[p])).det ≠ 0 := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hw)
  rw [← Matrix.rank_mul_eq_right_of_det_ne_zero _ (logMatrix K p ε) hw', Matrix.smul_mul,
    Matrix.one_mul, hmat, Matrix.rank_mul_eq_right_of_det_ne_zero _ _ hdet]

/-- **The $p$-adic regulator form, for one family.** For a family `ε` of units of maximal rank
lying in $E_1$, `logMatrix K p ε` has full rank iff the elementary form of Leopoldt's conjecture
holds. In particular the rank does not depend on the family. -/
@[category API, AMS 11]
theorem rank_logMatrix_eq_iff {ε : Fin (rank K) → (𝓞 K)ˣ} (hmax : IsMaxRank ε)
    (hone : ∀ i, IsPrincipalUnitAbove K p (ε i)) :
    (logMatrix K p ε).rank = rank K ↔ LeopoldtConjecture K p := by
  rw [rank_logMatrix_eq K p hmax hone, leopoldtConjecture_iff_rank]

/-- **The $p$-adic regulator form and the elementary form agree**: the statement of
`leopoldt_conjecture.variants.padicRegulator` holds iff `LeopoldtConjecture K p` does. One
direction applies the statement to the family given by `exists_isMaxRank_isPrincipalUnitAbove`. -/
@[category API, AMS 11]
theorem forall_rank_logMatrix_iff :
    (∀ ε : Fin (rank K) → (𝓞 K)ˣ, IsMaxRank ε → (∀ i, IsPrincipalUnitAbove K p (ε i)) →
      (logMatrix K p ε).rank = rank K) ↔ LeopoldtConjecture K p := by
  refine ⟨fun h ↦ ?_, fun h ε hmax hone ↦ (rank_logMatrix_eq_iff K p hmax hone).2 h⟩
  obtain ⟨ε, hmax, hone⟩ := exists_isMaxRank_isPrincipalUnitAbove K p
  exact (rank_logMatrix_eq_iff K p hmax hone).1 (h ε hmax hone)

end Leopoldt
