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

public import FormalConjecturesTest.Period.Algebra.Module.ZLattice.Complex
public import FormalConjecturesTest.Period.Analysis.SpecialFunctions.Elliptic.Weierstrass.Injective
public import FormalConjecturesTest.Period.Analysis.SpecialFunctions.Elliptic.Weierstrass.Surjective
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public noncomputable section

/-!
# A half fundamental domain on which `℘` is injective

The Weierstrass function is even and $\Lambda$-periodic, so it is two-to-one from a fundamental
parallelogram $F = \{s\omega_1 + t\omega_2 : s, t \in [0, 1)\}$ onto $\mathbb{C}$, except over the
four points of order dividing two. This file cuts $F$ in half,
$$H = \{s\omega_1 + t\omega_2 : s \in [0, 1),\ t \in (0, \tfrac12)\}
  \qquad (\text{`PeriodPair.halfDomain`}),$$
and proves what the change of variables $x = \wp(z)$ needs of it:

* `℘` is injective on $H$ (`PeriodPair.injOn_weierstrassP_halfDomain`), because $\wp(z) = \wp(w)$
  forces $z \equiv \pm w \pmod \Lambda$ (`PeriodPair.weierstrassP_eq_iff`) and neither congruence is
  possible for two points of $H$ other than $z = w$;
* $H$ avoids $\Lambda$ and $\tfrac12\Lambda$, so $\wp$ is differentiable on it with $\wp' \ne 0$;
* $H$ has half the area of $F$: $F$ is the disjoint union of $H$, its translate $H + \omega_2/2$
  and two segments (`PeriodPair.volume_real_halfDomain`);
* $\wp(H)$ is all of $\mathbb{C}$ up to a null set, the image under $\wp$ of the two segments
  (`PeriodPair.image_weierstrassP_halfDomain_ae_eq_univ`).

## Source correspondence

[Sil2009, VI.3.6(b)] and [Mil2006, III Prop. 3.7]: $\mathbb{C}/\Lambda \to E(\mathbb{C})$,
$z \mapsto (\wp(z), \wp'(z))$, is a bijection; together with $\wp(-z) = \wp(z)$ this is the
two-to-one statement above. The half domain itself is a bookkeeping device with no source.
-/

open MeasureTheory Set

namespace PeriodPair

variable (L : PeriodPair)

/-- Source: Mathlib's `Basis.mem_span_iff_repr_mem` for `L.lattice = span ℤ (range L.basis)`. -/
lemma mem_lattice_iff_repr (z : ℂ) :
    z ∈ L.lattice ↔ ∀ i, ∃ n : ℤ, L.basis.repr z i = n := by
  rw [L.lattice_eq_span_range_basis, Module.Basis.mem_span_iff_repr_mem]
  simp only [Set.mem_range, algebraMap_int_eq, eq_intCast, eq_comm]

/-- The half fundamental domain $\{s\omega_1 + t\omega_2 : s \in [0, 1),\ t \in (0, \tfrac12)\}$. -/
def halfDomain : Set ℂ :=
  {z | L.basis.repr z 0 ∈ Ico (0 : ℝ) 1 ∧ L.basis.repr z 1 ∈ Ioo (0 : ℝ) (1 / 2)}

/-- The half domain is measurable: it is cut out by conditions on two continuous coordinates. -/
lemma measurableSet_halfDomain : MeasurableSet L.halfDomain := by
  have hc : ∀ i, Measurable fun z : ℂ ↦ L.basis.repr z i := fun i ↦
    (LinearMap.continuous_of_finiteDimensional (L.basis.coord i)).measurable
  exact ((hc 0) measurableSet_Ico).inter ((hc 1) measurableSet_Ioo)

/-- The half domain lies in the fundamental parallelogram of the basis $(\omega_1, \omega_2)$. -/
lemma halfDomain_subset_fundamentalDomain : L.halfDomain ⊆ ZSpan.fundamentalDomain L.basis := by
  rintro z ⟨h0, h1⟩
  rw [ZSpan.mem_fundamentalDomain, Fin.forall_fin_two]
  exact ⟨h0, h1.1.le, h1.2.trans (by norm_num)⟩

/-- No integer lies strictly between `0` and `1`. -/
private lemma intCast_notMem_Ioo_zero_one (n : ℤ) : (n : ℝ) ∉ Ioo 0 1 := by
  rintro ⟨h0, h1⟩
  have : (0 : ℤ) < n := by exact_mod_cast h0
  have : n < 1 := by exact_mod_cast h1
  omega

/-- The only integer strictly between `-1` and `1` is `0`. -/
private lemma eq_zero_of_intCast_mem_Ioo {n : ℤ} (h : (n : ℝ) ∈ Ioo (-1) 1) : n = 0 := by
  obtain ⟨h0, h1⟩ := h
  have : -1 < n := by exact_mod_cast h0
  have : n < 1 := by exact_mod_cast h1
  omega

/-- The half domain avoids the lattice: its second coordinate is not an integer. -/
lemma notMem_lattice_of_mem_halfDomain {z : ℂ} (hz : z ∈ L.halfDomain) : z ∉ L.lattice := by
  rw [L.mem_lattice_iff_repr]
  intro h
  obtain ⟨n, hn⟩ := h 1
  refine intCast_notMem_Ioo_zero_one n ?_
  rw [← hn]
  exact ⟨hz.2.1, hz.2.2.trans (by norm_num)⟩

/-- The half domain avoids the points of order two: for $z$ in it, $2z \notin \Lambda$, so
$\wp'(z) \ne 0$. -/
lemma two_mul_notMem_lattice_of_mem_halfDomain {z : ℂ} (hz : z ∈ L.halfDomain) :
    2 * z ∉ L.lattice := by
  rw [L.mem_lattice_iff_repr]
  intro h
  obtain ⟨n, hn⟩ := h 1
  have h2 : L.basis.repr (2 * z) 1 = 2 * L.basis.repr z 1 := by simp [two_mul]
  refine intCast_notMem_Ioo_zero_one n ?_
  rw [← hn, h2]
  exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩

/-- Source: [Sil2009, VI.3.6(b)] / [Mil2006, III Prop. 3.7] (bijectivity of $\mathbb{C}/\Lambda \to
E(\mathbb{C})$), in the form `PeriodPair.weierstrassP_eq_iff`. -/
lemma injOn_weierstrassP_halfDomain : InjOn ℘[L] L.halfDomain := by
  intro z hz w hw h
  rcases (L.weierstrassP_eq_iff (L.notMem_lattice_of_mem_halfDomain hz)
    (L.notMem_lattice_of_mem_halfDomain hw)).mp h with hsub | hadd
  · rw [L.mem_lattice_iff_repr] at hsub
    obtain ⟨m, hm⟩ := hsub 0
    obtain ⟨n, hn⟩ := hsub 1
    simp only [map_sub, Finsupp.coe_sub, Pi.sub_apply] at hm hn
    have hm0 := eq_zero_of_intCast_mem_Ioo (n := m) (by
      rw [← hm]; constructor <;> linarith [hz.1.1, hz.1.2, hw.1.1, hw.1.2])
    have hn0 := eq_zero_of_intCast_mem_Ioo (n := n) (by
      rw [← hn]; constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2])
    rw [hm0, Int.cast_zero, sub_eq_zero] at hm
    rw [hn0, Int.cast_zero, sub_eq_zero] at hn
    exact L.basis.repr.injective (Finsupp.ext (Fin.forall_fin_two.mpr ⟨hm, hn⟩))
  · rw [L.mem_lattice_iff_repr] at hadd
    obtain ⟨n, hn⟩ := hadd 1
    simp only [map_add, Finsupp.coe_add, Pi.add_apply] at hn
    refine (intCast_notMem_Ioo_zero_one n ?_).elim
    rw [← hn]
    constructor <;> linarith [hz.2.1, hz.2.2, hw.2.1, hw.2.2]

/-- A line $\{z : \text{coordinate}_i(z) = c\}$ is a proper affine subspace, hence null. -/
lemma volume_setOf_repr_eq (i : Fin 2) (c : ℝ) : volume {z : ℂ | L.basis.repr z i = c} = 0 := by
  have hii : L.basis.repr (L.basis i) i = 1 := by simp [Module.Basis.repr_self]
  have hset : {z : ℂ | L.basis.repr z i = c} =
      (fun z ↦ z + -(c • L.basis i)) ⁻¹' (LinearMap.ker (L.basis.coord i) : Set ℂ) := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe, LinearMap.mem_ker,
      Module.Basis.coord_apply, map_add, map_neg, map_smul, hii, smul_eq_mul, mul_one,
      add_neg_eq_zero]
  have hne : LinearMap.ker (L.basis.coord i) ≠ ⊤ := by
    intro h
    have hi : L.basis i ∈ LinearMap.ker (L.basis.coord i) := h ▸ Submodule.mem_top
    simp at hi
  rw [hset, measure_preimage_add_right]
  exact Measure.addHaar_submodule volume _ hne

/-- The fundamental parallelogram is, up to the two null segments $t = 0$ and $t = \tfrac12$, the
disjoint union of the half domain and its translate by $\omega_2 / 2$. -/
lemma volume_fundamentalDomain_eq_two_mul_volume_halfDomain :
    volume (ZSpan.fundamentalDomain L.basis) = 2 * volume L.halfDomain := by
  set v : ℂ := (1 / 2 : ℝ) • L.basis 1 with hv
  have h10 : L.basis.repr (L.basis 1) 0 = 0 := by
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg (by decide)]
  have h11 : L.basis.repr (L.basis 1) 1 = 1 := by
    rw [Module.Basis.repr_self, Finsupp.single_eq_same]
  have hrv0 : ∀ z, L.basis.repr (z + -v) 0 = L.basis.repr z 0 := fun z ↦ by
    simp only [hv, map_add, map_neg, map_smul, Finsupp.coe_add, Finsupp.coe_neg, Finsupp.coe_smul,
      Pi.add_apply, Pi.neg_apply, Pi.smul_apply, h10, smul_zero, neg_zero, add_zero]
  have hrv1 : ∀ z, L.basis.repr (z + -v) 1 = L.basis.repr z 1 - 1 / 2 := fun z ↦ by
    rw [sub_eq_add_neg]
    simp only [hv, map_add, map_neg, map_smul, Finsupp.coe_add, Finsupp.coe_neg, Finsupp.coe_smul,
      Pi.add_apply, Pi.neg_apply, Pi.smul_apply, h11, smul_eq_mul, mul_one]
  set H₂ : Set ℂ := (fun z ↦ z + -v) ⁻¹' L.halfDomain with hH₂
  have hmem₂ : ∀ z, z ∈ H₂ ↔
      L.basis.repr z 0 ∈ Ico (0 : ℝ) 1 ∧ L.basis.repr z 1 ∈ Ioo (1 / 2 : ℝ) 1 := by
    intro z
    simp only [hH₂, Set.mem_preimage, halfDomain, Set.mem_ofPred_eq, hrv0, hrv1, Set.mem_Ioo]
    constructor <;> rintro ⟨h0, h1, h2⟩ <;> exact ⟨h0, by linarith, by linarith⟩
  have hvol₂ : volume H₂ = volume L.halfDomain := measure_preimage_add_right _ _ _
  have hmeas₂ : MeasurableSet H₂ := L.measurableSet_halfDomain.preimage (measurable_add_const _)
  apply le_antisymm
  · calc volume (ZSpan.fundamentalDomain L.basis)
        ≤ volume (L.halfDomain ∪ H₂ ∪
            ({z | L.basis.repr z 1 = 0} ∪ {z | L.basis.repr z 1 = 1 / 2})) := by
          apply measure_mono
          intro z hz
          rw [ZSpan.mem_fundamentalDomain, Fin.forall_fin_two] at hz
          obtain ⟨hs, ht0, ht1⟩ := hz
          rcases ht0.eq_or_lt with h0 | h0
          · exact Or.inr (Or.inl h0.symm)
          rcases lt_trichotomy (L.basis.repr z 1) (1 / 2) with hlt | heq | hgt
          · exact Or.inl (Or.inl ⟨hs, h0, hlt⟩)
          · exact Or.inr (Or.inr heq)
          · exact Or.inl (Or.inr ((hmem₂ z).mpr ⟨hs, hgt, ht1⟩))
      _ ≤ volume (L.halfDomain ∪ H₂) +
            volume ({z | L.basis.repr z 1 = 0} ∪ {z | L.basis.repr z 1 = 1 / 2}) :=
          measure_union_le _ _
      _ ≤ volume L.halfDomain + volume H₂ + 0 :=
          add_le_add (measure_union_le _ _)
            (measure_union_null (L.volume_setOf_repr_eq 1 0) (L.volume_setOf_repr_eq 1 (1 / 2))).le
      _ = 2 * volume L.halfDomain := by rw [hvol₂, add_zero, two_mul]
  · calc 2 * volume L.halfDomain = volume L.halfDomain + volume H₂ := by rw [hvol₂, two_mul]
      _ = volume (L.halfDomain ∪ H₂) := by
          refine (measure_union ?_ hmeas₂).symm
          rw [Set.disjoint_left]
          intro z hz hz₂
          have := ((hmem₂ z).mp hz₂).2.1
          linarith [hz.2.2]
      _ ≤ volume (ZSpan.fundamentalDomain L.basis) := by
          apply measure_mono
          rintro z (hz | hz)
          · exact L.halfDomain_subset_fundamentalDomain hz
          · rw [ZSpan.mem_fundamentalDomain, Fin.forall_fin_two]
            obtain ⟨h0, h1⟩ := (hmem₂ z).mp hz
            exact ⟨h0, by linarith [h1.1], h1.2⟩

/-- Source: LMFDB knowl `ec.period` (the covolume is the area of the fundamental parallelogram);
Mathlib's `ZLattice.covolume_eq_measure_fundamentalDomain`. -/
lemma volume_real_halfDomain : volume.real L.halfDomain = ZLattice.covolume L.lattice / 2 := by
  have hF : IsAddFundamentalDomain L.lattice (ZSpan.fundamentalDomain L.basis) volume := by
    have h := ZSpan.isAddFundamentalDomain L.basis volume
    rwa [← L.lattice_eq_span_range_basis] at h
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L.lattice volume hF, measureReal_def,
    measureReal_def, L.volume_fundamentalDomain_eq_two_mul_volume_halfDomain, ENNReal.toReal_mul,
    ENNReal.toReal_ofNat]
  ring

/-- Every value of $\wp$ is attained on the half domain or on one of the two segments
$t = 0$, $t = \tfrac12$ of the fundamental parallelogram: reduce a preimage
(`PeriodPair.exists_weierstrassP_eq`) into the parallelogram, and reflect it by $z \mapsto -z$
modulo $\Lambda$ if it lands in the upper half. -/
lemma image_weierstrassP_halfDomain_union_eq_univ :
    ℘[L] '' L.halfDomain ∪
      ℘[L] '' ({z | L.basis.repr z 1 = 0 ∨ L.basis.repr z 1 = 1 / 2} \ L.lattice) = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  obtain ⟨z, hz, hzx⟩ := L.exists_weierstrassP_eq x
  have hzw : z - ZSpan.fract L.basis z ∈ L.lattice := by
    rw [ZSpan.fract_apply, sub_sub_cancel, L.lattice_eq_span_range_basis]
    exact (ZSpan.floor L.basis z).2
  set w := ZSpan.fract L.basis z with hw
  have hwF : w ∈ ZSpan.fundamentalDomain L.basis := ZSpan.fract_mem_fundamentalDomain L.basis z
  have hwx : ℘[L] w = x := by
    rw [← hzx]
    simpa using L.weierstrassP_sub_coe z ⟨z - w, hzw⟩
  have hwΛ : w ∉ L.lattice := fun h ↦ hz (by simpa using add_mem hzw h)
  have hr2 : L.basis.repr L.ω₂ = Finsupp.single 1 1 := by rw [← L.basis_one, L.basis.repr_self]
  have hr1 : L.basis.repr L.ω₁ = Finsupp.single 0 1 := by rw [← L.basis_zero, L.basis.repr_self]
  rw [ZSpan.mem_fundamentalDomain, Fin.forall_fin_two] at hwF
  obtain ⟨⟨hs0, hs1⟩, ⟨ht0, ht1⟩⟩ := hwF
  rcases lt_trichotomy (L.basis.repr w 1) (1 / 2) with hlt | heq | hgt
  · rcases ht0.eq_or_lt with h0 | h0
    · exact Or.inr ⟨w, ⟨Or.inl h0.symm, hwΛ⟩, hwx⟩
    · exact Or.inl ⟨w, ⟨⟨hs0, hs1⟩, h0, hlt⟩, hwx⟩
  · exact Or.inr ⟨w, ⟨Or.inr heq, hwΛ⟩, hwx⟩
  · refine Or.inl ?_
    have hneg : ∀ l ∈ L.lattice, ℘[L] (l - w) = x := fun l hl ↦ by
      rw [sub_eq_neg_add, ← hwx, ← L.weierstrassP_neg w]
      exact L.weierstrassP_add_coe (-w) ⟨l, hl⟩
    rcases hs0.eq_or_lt with hs | hs
    · have h0 : L.basis.repr (L.ω₂ - w) 0 = -L.basis.repr w 0 := by simp [hr2]
      have h1 : L.basis.repr (L.ω₂ - w) 1 = 1 - L.basis.repr w 1 := by simp [hr2]
      refine ⟨L.ω₂ - w, ⟨?_, ?_⟩, hneg _ L.ω₂_mem_lattice⟩
      · rw [h0, ← hs]; simp
      · rw [h1]; constructor <;> linarith
    · have h0 : L.basis.repr (L.ω₁ + L.ω₂ - w) 0 = 1 - L.basis.repr w 0 := by simp [hr1, hr2]
      have h1 : L.basis.repr (L.ω₁ + L.ω₂ - w) 1 = 1 - L.basis.repr w 1 := by simp [hr1, hr2]
      refine ⟨L.ω₁ + L.ω₂ - w, ⟨?_, ?_⟩, hneg _ (add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice)⟩
      · rw [h0]; constructor <;> linarith
      · rw [h1]; constructor <;> linarith

/-- The image under $\wp$ of a null set off the lattice is null, $\wp$ being differentiable there
(Mathlib's `addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero`). -/
lemma volume_image_weierstrassP_setOf_repr_eq (c : ℝ) :
    volume (℘[L] '' ({z | L.basis.repr z 1 = c} \ L.lattice)) = 0 :=
  addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    ((L.differentiableOn_weierstrassP.restrictScalars ℝ).mono fun _ hz ↦ hz.2)
    (measure_mono_null sdiff_subset (L.volume_setOf_repr_eq 1 c))

/-- $\wp(H)$ is almost all of $\mathbb{C}$. -/
lemma image_weierstrassP_halfDomain_ae_eq_univ : ℘[L] '' L.halfDomain =ᵐ[volume] univ := by
  rw [ae_eq_univ]
  refine measure_mono_null (fun x hx ↦ ?_) <| measure_union_null
    (L.volume_image_weierstrassP_setOf_repr_eq 0)
    (L.volume_image_weierstrassP_setOf_repr_eq (1 / 2))
  rcases Set.eq_univ_iff_forall.mp L.image_weierstrassP_halfDomain_union_eq_univ x with
    h | ⟨z, ⟨hz1 | hz1, hzΛ⟩, rfl⟩
  · exact absurd h hx
  · exact Or.inl ⟨z, ⟨hz1, hzΛ⟩, rfl⟩
  · exact Or.inr ⟨z, ⟨hz1, hzΛ⟩, rfl⟩

end PeriodPair

end
