/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252RurHData
import Biunimodular.F11.H252RurN1Data
import Biunimodular.F11.H252RurN2Data
import Biunimodular.F11.H252RurN3Data
import Biunimodular.F11.H252RurN4Data
import Biunimodular.F11.H252RurN5Data
import Biunimodular.F11.H252RurN6Data
import Biunimodular.F11.H252RurDData

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Biunimodular.F11

def h252RurCommonDen : ℤ := 227982122657029825499349751487471497284702040439422508455930508132324537121982974680260149248

theorem h252RurCommonDen_pos : 0 < h252RurCommonDen := by native_decide

theorem h252RurD_derivative_coefficients :
    integerCoefficientDerivative h252RurHCoeffs = h252RurDCoeffs := by
  native_decide

end Biunimodular.F11
