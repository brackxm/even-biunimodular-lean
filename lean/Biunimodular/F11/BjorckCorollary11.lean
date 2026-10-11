/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.BjorckEvenExclusion11
import Biunimodular.F11.PhaseSemanticCompletion11

set_option autoImplicit false

namespace Biunimodular.F11

/-!
The signal-level consequence of the square-class exclusion and the closed
`80 = 10 + 70` classification.  Every Björck--Saffari representative at
length eleven has the two-valued square-class shape covered by
`IsSquareClassFamily11`.
-/

/-- All seventy non-Gaussian normalized even biunimodular signals lie outside
the translated, modulated, projectively rescaled square-class family. -/
theorem zeroAutocorrSignal11_nonGaussian_outside_squareClass_card :
    Nat.card {z : ZeroAutocorrSignal11 //
      ¬ IsQuadraticGaussianSignal11 z ∧ ¬ IsSquareClassFamily11 z} = 70 := by
  calc
    Nat.card {z : ZeroAutocorrSignal11 //
        ¬ IsQuadraticGaussianSignal11 z ∧ ¬ IsSquareClassFamily11 z} =
        Nat.card {z : ZeroAutocorrSignal11 //
          ¬ IsQuadraticGaussianSignal11 z} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun z =>
        ⟨fun h => h.1, fun h => ⟨h, zeroAutocorrSignal11_not_squareClassFamily z⟩⟩)
    _ = 70 := zeroAutocorrSignal11_classification.2.2

end Biunimodular.F11
