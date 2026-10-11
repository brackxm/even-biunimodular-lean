/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.InvariantPolynomialData
import Biunimodular.F11.InvariantFiniteFieldIrreducibility
import Biunimodular.F11.InvariantBMonicTransform

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

/-!
# Characteristic-zero irreducibility endpoints

Both invariant factors are now closed internally:

* `A` is monic, so its irreducible mod-3 reduction transfers directly;
* `B` is handled by the integral monic root-scaled transform in
  `InvariantBMonicTransform`.
-/

theorem invariantA_monic : invariantA.Monic := by
  let low : ℤ[X] :=
    -6320*X^5 + 10298240*X^4 - 1009036608*X^3 +
      1012283392*X^2 - 84262912*X + 692224
  have hlow : low.degree < 6 := by
    simp only [low]
    compute_degree; norm_num
  rw [show invariantA = X^6 + low by simp only [invariantA, low]; ring]
  exact monic_X_pow_add hlow

theorem invariantA_irreducible_over_Z : Irreducible invariantA := by
  apply invariantA_monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 3))
  rw [invariantA_mod3]
  exact invariantA3_irreducible

theorem invariantA_irreducible_over_Q :
    Irreducible (invariantA.map (Int.castRingHom ℚ)) := by
  exact (invariantA_monic.irreducible_iff_irreducible_map_fraction_map).1
    invariantA_irreducible_over_Z

/-- The B-sector characteristic-zero endpoint is now unconditional. -/
theorem invariantB_irreducible_over_Q :
    Irreducible (invariantB.map (Int.castRingHom ℚ)) :=
  invariantB_irreducible_over_Q_closed

end Biunimodular.F11
