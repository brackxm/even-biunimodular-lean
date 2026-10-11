/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion2Pairs01Data

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

theorem homogeneousCompletion2Pair1_2_sp_check :
    rationalSparseZeroCheck 1 homogeneousCompletion2Pair1_2SPTerms := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion2Pair1_2_last_check :
    rationalSparseZeroCheck 11 homogeneousCompletion2Pair1_2LastTerms := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion2Pair1_3_sp_check :
    rationalSparseZeroCheck 1 homogeneousCompletion2Pair1_3SPTerms := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion2Pair1_3_last_check :
    rationalSparseZeroCheck 11 homogeneousCompletion2Pair1_3LastTerms := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion2Pair2_3_sp_check :
    rationalSparseZeroCheck 1 homogeneousCompletion2Pair2_3SPTerms := by
  unfold rationalSparseZeroCheck
  native_decide

theorem homogeneousCompletion2Pair2_3_last_check :
    rationalSparseZeroCheck 11 homogeneousCompletion2Pair2_3LastTerms := by
  unfold rationalSparseZeroCheck
  native_decide

end Biunimodular.F11
