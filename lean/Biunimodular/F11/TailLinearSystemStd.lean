/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.TailLinearSystem

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

/-- Standard-`mulVec` version of the four tail equations.  This duplicates the
reflection-friendly statement in `TailLinearSystem.lean`, but is easier to use
with the adjugate/Cramer API and perturbation estimates. -/
theorem tail_linear_system_std_of_autocorr
    (a b c d e f g h j k : ℝ)
    (E1 : 2 * a + 2 * (a * c + b * d) + 2 * (c * e + d * f) + 2 * (e * g + f * h) +
      2 * (g * j + h * k) + 1 = 0)
    (E2 : 2 * c + 2 * (a * e + b * f) + 2 * (c * g + d * h) + 2 * (e * j + f * k) +
      2 * (g * j + h * k) + 1 = 0)
    (E3 : 2 * e + 2 * (a * g + b * h) + 2 * (c * j + d * k) + 2 * (e * j + f * k) +
      2 * (a * c + b * d) + 1 = 0)
    (E4 : 2 * g + 2 * (a * j + b * k) + 2 * (c * j + d * k) + 2 * (e * g + f * h) +
      2 * (a * e + b * f) + 1 = 0)
    (E5 : 2 * j + 2 * (a * j + b * k) + 2 * (c * g + d * h) + 2 * (a * g + b * h) +
      2 * (c * e + d * f) + 1 = 0) :
    (tailMatrix a b c d e f).mulVec (tailVec g h j k) = tailRhs a b c d e f := by
  funext i
  fin_cases i <;>
    simp [tailMatrix, tailRhs, tailVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    nlinarith [E1, E2, E3, E4, E5]

end Biunimodular.F11
