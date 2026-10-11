/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CriticalPairListCoverage

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion2PairList : List (Fin 3 × Fin 3) :=
  [(0, 1), (0, 2), (1, 2)]

def homogeneousCompletion2Pairs : Fin 3 → Fin 3 × Fin 3 :=
  fun r => homogeneousCompletion2PairList.get r

theorem homogeneousCompletion2_pair_coverage :
    ∀ i j : Fin 3, i < j → ∃ r, homogeneousCompletion2Pairs r = (i, j) := by
  have h : criticalPairListCoverageCheck homogeneousCompletion2PairList = true := by native_decide
  intro i j hij
  obtain ⟨r, hr⟩ := List.mem_iff_get.mp (criticalPairListCoverageCheck.sound h i j hij)
  exact ⟨r, hr⟩

end Biunimodular.F11
