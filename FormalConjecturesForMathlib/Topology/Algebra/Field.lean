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

public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Separation.Basic

@[expose] public section

/-!
# Locally, a continuous square root is determined by its value at a point

* `eventually_eq_of_sq_eq_sq`: if $f$ and $g$ are continuous at $a$ with $f(a) = g(a) \neq 0$
  and $f^2 = g^2$ near $a$, then $f = g$ near $a$. This locks the sign of a continuous branch of
  a square root.
-/

open Filter Topology

variable {α 𝕜 : Type*} [TopologicalSpace α] [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [T1Space 𝕜] [NeZero (2 : 𝕜)] {f g : α → 𝕜} {a : α}

/-- Two functions continuous at `a` whose squares agree near `a` and whose common value at `a`
is nonzero agree near `a`; this locks the sign of a continuous branch of a square root. -/
theorem eventually_eq_of_sq_eq_sq (hf : ContinuousAt f a) (hg : ContinuousAt g a) (h : f a = g a)
    (h0 : f a ≠ 0) (hsq : ∀ᶠ x in 𝓝 a, f x ^ 2 = g x ^ 2) : ∀ᶠ x in 𝓝 a, f x = g x := by
  have hsum : f a + g a ≠ 0 := by
    rw [← h, ← two_mul]
    exact mul_ne_zero (NeZero.ne (2 : 𝕜)) h0
  filter_upwards [hsq, (hf.add hg).eventually_ne hsum] with x hx hx'
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp hx).resolve_right fun hne ↦ hx' (by simp [hne])

end
