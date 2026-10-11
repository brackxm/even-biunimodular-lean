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

def homogeneousCompletion3PairList : List (Fin 7 × Fin 7) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (0, 6), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (2, 3), (2, 4), (2, 5), (2, 6), (3, 4), (3, 5), (3, 6), (4, 5), (4, 6), (5, 6)]

def homogeneousCompletion3Pairs : Fin 21 → Fin 7 × Fin 7 :=
  fun r => homogeneousCompletion3PairList.get r

theorem homogeneousCompletion3_pair_coverage :
    ∀ i j : Fin 7, i < j → ∃ r, homogeneousCompletion3Pairs r = (i, j) := by
  have h : criticalPairListCoverageCheck homogeneousCompletion3PairList = true := by native_decide
  intro i j hij
  obtain ⟨r, hr⟩ := List.mem_iff_get.mp (criticalPairListCoverageCheck.sound h i j hij)
  exact ⟨r, hr⟩

end Biunimodular.F11
