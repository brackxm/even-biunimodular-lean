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

def homogeneousCompletion1PairList : List (Fin 1 × Fin 1) :=
  []

def homogeneousCompletion1Pairs : Fin 0 → Fin 1 × Fin 1 :=
  fun r => homogeneousCompletion1PairList.get r

theorem homogeneousCompletion1_pair_coverage :
    ∀ i j : Fin 1, i < j → ∃ r, homogeneousCompletion1Pairs r = (i, j) := by
  have h : criticalPairListCoverageCheck homogeneousCompletion1PairList = true := by native_decide
  intro i j hij
  obtain ⟨r, hr⟩ := List.mem_iff_get.mp (criticalPairListCoverageCheck.sound h i j hij)
  exact ⟨r, hr⟩

end Biunimodular.F11
