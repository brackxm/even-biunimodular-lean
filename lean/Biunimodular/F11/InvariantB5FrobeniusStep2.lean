/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.InvariantB5FiniteFieldData

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

/-- Explicit quotient identity for the first nontrivial B-sector Frobenius step. -/
theorem b5_frobenius_step2_identity :
    b5r1 ^ 5 - b5r2 = invariantB5 * b5q2 := by
  let : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  simp only [b5r1, b5r2, b5q2, invariantB5]
  reduce_mod_char
  ring_nf
  reduce_mod_char

end Biunimodular.F11
