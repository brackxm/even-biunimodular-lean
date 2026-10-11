/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5Leading01Checks
import Biunimodular.F11.HomogeneousCompletion5Leading02Checks
import Biunimodular.F11.HomogeneousCompletion5Leading03Checks
import Biunimodular.F11.HomogeneousCompletion5Leading04Checks
import Biunimodular.F11.HomogeneousCompletion5Leading05Checks
import Biunimodular.F11.HomogeneousCompletion5Leading06Checks
import Biunimodular.F11.HomogeneousCompletion5Leading07Checks
import Biunimodular.F11.HomogeneousCompletion5Leading08Checks
import Biunimodular.F11.HomogeneousCompletion5Leading09Checks
import Biunimodular.F11.HomogeneousCompletion5Leading10Checks
import Biunimodular.F11.HomogeneousCompletion5Leading11Checks
import Biunimodular.F11.HomogeneousCompletion5Leading12Checks
import Biunimodular.F11.HomogeneousCompletion5Leading13Checks
import Biunimodular.F11.HomogeneousCompletion5Leading14Checks
import Biunimodular.F11.HomogeneousCompletion5Leading15Checks
import Biunimodular.F11.HomogeneousCompletion5Leading16Checks
import Biunimodular.F11.HomogeneousCompletion5Leading17Checks
import Biunimodular.F11.HomogeneousCompletion5Leading18Checks
import Biunimodular.F11.HomogeneousCompletion5Leading19Checks
import Biunimodular.F11.HomogeneousCompletion5Leading20Checks
import Biunimodular.F11.HomogeneousCompletion5Leading21Checks
import Biunimodular.F11.HomogeneousCompletion5Leading22Checks
import Biunimodular.F11.HomogeneousCompletion5Leading23Checks
import Biunimodular.F11.HomogeneousCompletion5Leading24Checks
import Biunimodular.F11.HomogeneousCompletion5Leading25Checks
import Biunimodular.F11.HomogeneousCompletion5Leading26Checks
import Biunimodular.F11.HomogeneousCompletion5Leading27Checks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

theorem homogeneousCompletion5_leading_check :
    ∀ k : Fin 27, rationalSparseLeadingCheck (homogeneousCompletion5G k) (homogeneousCompletion5Leading k) := by
  intro k
  fin_cases k
  · exact homogeneousCompletion5_leading_column0_check
  · exact homogeneousCompletion5_leading_column1_check
  · exact homogeneousCompletion5_leading_column2_check
  · exact homogeneousCompletion5_leading_column3_check
  · exact homogeneousCompletion5_leading_column4_check
  · exact homogeneousCompletion5_leading_column5_check
  · exact homogeneousCompletion5_leading_column6_check
  · exact homogeneousCompletion5_leading_column7_check
  · exact homogeneousCompletion5_leading_column8_check
  · exact homogeneousCompletion5_leading_column9_check
  · exact homogeneousCompletion5_leading_column10_check
  · exact homogeneousCompletion5_leading_column11_check
  · exact homogeneousCompletion5_leading_column12_check
  · exact homogeneousCompletion5_leading_column13_check
  · exact homogeneousCompletion5_leading_column14_check
  · exact homogeneousCompletion5_leading_column15_check
  · exact homogeneousCompletion5_leading_column16_check
  · exact homogeneousCompletion5_leading_column17_check
  · exact homogeneousCompletion5_leading_column18_check
  · exact homogeneousCompletion5_leading_column19_check
  · exact homogeneousCompletion5_leading_column20_check
  · exact homogeneousCompletion5_leading_column21_check
  · exact homogeneousCompletion5_leading_column22_check
  · exact homogeneousCompletion5_leading_column23_check
  · exact homogeneousCompletion5_leading_column24_check
  · exact homogeneousCompletion5_leading_column25_check
  · exact homogeneousCompletion5_leading_column26_check


end Biunimodular.F11
