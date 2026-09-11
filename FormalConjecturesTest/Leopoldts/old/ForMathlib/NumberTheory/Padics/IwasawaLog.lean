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
public import FormalConjecturesTest.Leopoldts.ForMathlib.NumberTheory.Padics.IwasawaLog

/-!
# Unused part of the Iwasawa logarithm library

**Deprecated.** The declarations of
`FormalConjecturesTest/Leopoldts/ForMathlib/NumberTheory/Padics/IwasawaLog.lean` that the Leopoldt
equivalence proofs do not use: `HasIwasawaLog.ne_zero`, `PadicComplex.hasIwasawaLog_iff`.
-/

@[expose] public section

open Filter Topology

open scoped Nat

namespace PadicIwasawaLog

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [NontriviallyNormedField K]
  [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

section Iwasawa

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Only nonzero elements have an Iwasawa logarithm, since `0 ^ N / p ^ m - 1 = -1`. -/
theorem HasIwasawaLog.ne_zero {x : K} (hx : HasIwasawaLog p x) : x ≠ 0 := by
  rintro rfl
  obtain ⟨N, hN, m, h⟩ := hx
  rw [zero_pow hN.ne', zero_div, zero_sub, norm_neg, norm_one] at h
  exact lt_irrefl _ h

end Iwasawa

section PadicComplex

omit [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The domain of the Iwasawa logarithm in `ℂ_[p]` is exactly `ℂ_[p]^×`. -/
theorem PadicComplex.hasIwasawaLog_iff {x : ℂ_[p]} : HasIwasawaLog p x ↔ x ≠ 0 :=
  ⟨HasIwasawaLog.ne_zero, PadicComplex.hasIwasawaLog⟩

end PadicComplex

end PadicIwasawaLog
