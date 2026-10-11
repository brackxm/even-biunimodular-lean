/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.PhaseSemanticCompletion11

set_option autoImplicit false
namespace Biunimodular.F11.Results
noncomputable section
/-- Unconditional fixed-slice and physical-phase classification. -/
theorem phaseSolution11_classification_with_fixedSlice :
    (Nat.card Even11FixedSlicePoint = 32 ∧
      Nat.card {p : Even11FixedSlicePoint // even11FixedSliceIsReal p} = 16 ∧
      Fintype.card SplitQuotientRoot = 8 ∧
      Fintype.card NonGaussianSplitQuotientRoot = 7) ∧
    (Nat.card PhaseSolution11 = 80 ∧
      Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 = 0} = 10 ∧
      Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 ≠ 0} = 70) :=
  phaseSolution11_classification_complete

end
end Biunimodular.F11.Results
