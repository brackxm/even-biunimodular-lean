/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion2BasisData
import Biunimodular.F11.HomogeneousSparseDegree

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion2Leading : Fin 3 → FixedSliceSparseExponent :=
  ![⟨1, 0, 0, 0, 1, 0⟩, ⟨1, 0, 0, 1, 0, 0⟩, ⟨0, 1, 0, 1, 1, 0⟩]

theorem homogeneousCompletion2_leading_check :
    ∀ k : Fin 3, rationalSparseLeadingCheck (homogeneousCompletion2G k) (homogeneousCompletion2Leading k) := by
  unfold rationalSparseLeadingCheck rationalSparseZeroCheck
  native_decide

end Biunimodular.F11
