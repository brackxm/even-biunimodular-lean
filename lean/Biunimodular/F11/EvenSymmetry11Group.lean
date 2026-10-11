/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public meta import Biunimodular.F11.ProofTactics

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# The normalized even symmetry group for p = 11

The cyclic factor is dilation by `2` on the five nonzero even coordinates,
and the second factor is simultaneous complex conjugation.
-/

/-- The normalized even symmetry group `H = C₅ × {conjugation}`.
We use `Multiplicative` so that the standard free multiplicative-action
quotient API applies directly. -/
abbrev EvenSymmetry11 := Multiplicative (ZMod 5 × ZMod 2)

theorem evenSymmetry11_card : Fintype.card EvenSymmetry11 = 10 := by
  native_decide

end Biunimodular.F11
