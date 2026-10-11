/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber4LaurentRankData
import Biunimodular.F11.H252Fiber4LaurentRankReducedData
import Biunimodular.F11.TorusMacaulayRowReduction

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0

theorem h252Fiber4LaurentRank_reduced_rows : ∀ i : Fin 1250,
    torusMacaulayEvaluatedRow (2 : ZMod 109) (h252Fiber4LaurentRankRows[i.val]?.getD []) =
      torusMacaulayEvaluatedRow (2 : ZMod 109) (h252Fiber4LaurentRankReducedRows[i.val]?.getD []) := by native_decide

theorem h252Fiber4LaurentRank_reduced_matrix :
    torusMacaulaySparseMatrix 1250 h252Fiber4LaurentRankRows (2 : ZMod 109) =
      torusMacaulaySparseMatrix 1250 h252Fiber4LaurentRankReducedRows (2 : ZMod 109) :=
  torusMacaulaySparseMatrix_eq_of_evaluated_rows _ _ _ _ h252Fiber4LaurentRank_reduced_rows

end Biunimodular.F11
