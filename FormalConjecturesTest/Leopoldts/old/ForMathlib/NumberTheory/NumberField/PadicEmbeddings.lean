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

import FormalConjectures.Wikipedia.LeopoldtConjecture
import FormalConjecturesTest.Leopoldts.old.ForMathlib.NumberTheory.Padics.ExpLog

/-!
# Principal-unit powers of global units in `ℂ_[p]`

**Deprecated.** `Leopoldt.hasPrincipalUnitPow_map`, split off
`FormalConjecturesTest/Leopoldts/ForMathlib/NumberTheory/NumberField/PadicEmbeddings.lean`, where
nothing used it any more: every global unit has a principal-unit power at every embedding
`K → ℂ_[p]`, which is what makes its Iwasawa logarithm defined.
-/

open NumberField

open scoped NumberField

namespace Leopoldt

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/--
Every global unit has a principal-unit power at every embedding into $\mathbb{C}_p$: with
$Q = |(\mathcal{O}_K/p)^\times|$ one has $\varepsilon^Q \equiv 1 \pmod{p}$
(`exists_pow_sub_one_dvd`), so $\|\sigma(\varepsilon)^Q - 1\| \le \|p\| < 1$.
-/
theorem hasPrincipalUnitPow_map (σ : K →+* ℂ_[p]) (u : (𝓞 K)ˣ) :
    PadicExpLog.HasPrincipalUnitPow (σ (u : K)) := by
  obtain ⟨Q, hQ0, hQ⟩ := exists_pow_sub_one_dvd (K := K) (p := p)
  obtain ⟨c, hc⟩ := hQ u
  refine ⟨Q, Nat.pos_of_ne_zero hQ0, ?_⟩
  have h1 : σ (u : K) ^ Q - 1 = ((p : ℕ) : ℂ_[p]) * σ (c : K) := by
    have := congrArg (fun x : 𝓞 K ↦ σ (x : K)) hc
    simpa only [map_sub, map_mul, map_pow, map_natCast, map_one, Units.val_pow_eq_pow_val,
      RingOfIntegers.coe_eq_algebraMap] using this
  rw [h1, norm_mul]
  calc ‖((p : ℕ) : ℂ_[p])‖ * ‖σ (c : K)‖ ≤ ‖((p : ℕ) : ℂ_[p])‖ * 1 := by
        gcongr
        exact PadicExpLog.PadicComplex.norm_le_one_of_isIntegral
          ((RingOfIntegers.isIntegral_coe c).map_of_comp_eq (RingHom.id ℤ) σ (RingHom.ext_int _ _))
    _ < 1 := by
        rw [mul_one]
        exact PadicExpLog.PadicComplex.norm_natCast_p_lt_one

end Leopoldt
