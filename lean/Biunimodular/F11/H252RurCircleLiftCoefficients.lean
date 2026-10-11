/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252RurInputData
import Biunimodular.F11.H252CircleCertificateData11
import Biunimodular.F11.IntegerCoefficientHomogenization

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Biunimodular.F11

def h252RurOriginalLeading : ℤ := 18737743293912207240844066038256883149889211838532301179907167595325432491327605381791744

theorem h252RurOriginalLeading_pos : 0 < h252RurOriginalLeading := by native_decide

theorem h252RurCircleLift_coefficients :
    integerCoefficientEqual
      (integerCoefficientScale h252RurCommonDen h252CircleLiftCoeffs11)
      (integerCoefficientScale h252RurOriginalLeading
        (integerCoefficientHomogenize h252RurHCoeffs)) = true := by
  native_decide

theorem h252RurHCoeffs_nonempty : h252RurHCoeffs ≠ [] := by native_decide

theorem h252RurHCoeffs_tail_length : h252RurHCoeffs.tail.length = 252 := by native_decide

end Biunimodular.F11
