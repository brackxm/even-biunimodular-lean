/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber6LaurentRankData
import Biunimodular.F11.H252Fiber6LaurentRankReducedData
import Biunimodular.F11.TorusMacaulayRowReduction

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0

theorem h252Fiber6LaurentRank_reduced_rows : ∀ i : Fin 1250,
    torusMacaulayEvaluatedRow (29 : ZMod 307) (h252Fiber6LaurentRankRows[i.val]?.getD []) =
      torusMacaulayEvaluatedRow (29 : ZMod 307) (h252Fiber6LaurentRankReducedRows[i.val]?.getD []) := by native_decide

theorem h252Fiber6LaurentRank_reduced_matrix :
    torusMacaulaySparseMatrix 1250 h252Fiber6LaurentRankRows (29 : ZMod 307) =
      torusMacaulaySparseMatrix 1250 h252Fiber6LaurentRankReducedRows (29 : ZMod 307) :=
  torusMacaulaySparseMatrix_eq_of_evaluated_rows _ _ _ _ h252Fiber6LaurentRank_reduced_rows

end Biunimodular.F11
