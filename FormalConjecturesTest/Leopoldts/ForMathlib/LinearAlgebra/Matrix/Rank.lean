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
module

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Full row rank and linear independence of the rows

`Matrix.rank_eq_card_iff_linearIndependent_row`: a matrix `A : Matrix m n F` over a field has
full row rank `Fintype.card m` exactly when its rows are linearly independent. Mathlib states the
backward direction as `LinearIndependent.rank_matrix`.
-/

@[expose] public section

namespace Matrix

variable {m n F : Type*} [Fintype m] [Fintype n] [Field F]

/-- A matrix has full row rank exactly when its rows are linearly independent. -/
theorem rank_eq_card_iff_linearIndependent_row (A : Matrix m n F) :
    A.rank = Fintype.card m ↔ LinearIndependent F A.row := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← rank_eq_finrank_span_row, eq_comm]

end Matrix
