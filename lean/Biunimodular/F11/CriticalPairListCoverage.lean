/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.List.FinRange

set_option autoImplicit false
namespace Biunimodular.F11

def criticalPairListCoverageCheck {n : ℕ} (entries : List (Fin n × Fin n)) : Bool :=
  let indices := List.finRange n
  indices.all fun i => indices.all fun j => decide (¬i < j) || entries.contains (i, j)

theorem criticalPairListCoverageCheck.sound {n : ℕ} {entries : List (Fin n × Fin n)}
    (h : criticalPairListCoverageCheck entries = true) :
    ∀ i j : Fin n, i < j → (i, j) ∈ entries := by
  intro i j hij
  have hi := List.all_eq_true.mp h i (by simp)
  have hj := List.all_eq_true.mp hi j (by simp)
  simpa [hij] using hj

end Biunimodular.F11
