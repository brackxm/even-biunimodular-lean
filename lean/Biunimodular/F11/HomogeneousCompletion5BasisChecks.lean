/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion5Forward01Checks
import Biunimodular.F11.HomogeneousCompletion5Forward02Checks
import Biunimodular.F11.HomogeneousCompletion5Forward03Checks
import Biunimodular.F11.HomogeneousCompletion5Forward04Checks
import Biunimodular.F11.HomogeneousCompletion5Forward05Checks
import Biunimodular.F11.HomogeneousCompletion5Forward06Checks
import Biunimodular.F11.HomogeneousCompletion5Forward07Checks
import Biunimodular.F11.HomogeneousCompletion5Forward08Checks
import Biunimodular.F11.HomogeneousCompletion5Forward09Checks
import Biunimodular.F11.HomogeneousCompletion5Forward10Checks
import Biunimodular.F11.HomogeneousCompletion5Forward11Checks
import Biunimodular.F11.HomogeneousCompletion5Forward12Checks
import Biunimodular.F11.HomogeneousCompletion5Forward13Checks
import Biunimodular.F11.HomogeneousCompletion5Forward14Checks
import Biunimodular.F11.HomogeneousCompletion5Forward15Checks
import Biunimodular.F11.HomogeneousCompletion5Forward16Checks
import Biunimodular.F11.HomogeneousCompletion5Forward17Checks
import Biunimodular.F11.HomogeneousCompletion5Forward18Checks
import Biunimodular.F11.HomogeneousCompletion5Forward19Checks
import Biunimodular.F11.HomogeneousCompletion5Forward20Checks
import Biunimodular.F11.HomogeneousCompletion5Forward21Checks
import Biunimodular.F11.HomogeneousCompletion5Forward22Checks
import Biunimodular.F11.HomogeneousCompletion5Forward23Checks
import Biunimodular.F11.HomogeneousCompletion5Forward24Checks
import Biunimodular.F11.HomogeneousCompletion5Forward25Checks
import Biunimodular.F11.HomogeneousCompletion5Forward26Checks
import Biunimodular.F11.HomogeneousCompletion5Forward27Checks
import Biunimodular.F11.HomogeneousCompletion5Reverse01Checks
import Biunimodular.F11.HomogeneousCompletion5Reverse02Checks
import Biunimodular.F11.HomogeneousCompletion5Reverse03Checks
import Biunimodular.F11.HomogeneousCompletion5Reverse04Checks
import Biunimodular.F11.HomogeneousCompletion5Reverse05Checks
import Biunimodular.F11.HomogeneousCompletion5Residual01Checks
import Biunimodular.F11.HomogeneousCompletion5Residual02Checks
import Biunimodular.F11.HomogeneousCompletion5Residual03Checks
import Biunimodular.F11.HomogeneousCompletion5Residual04Checks
import Biunimodular.F11.HomogeneousCompletion5Residual05Checks

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

theorem homogeneousCompletion5_forward_check :
    ∀ j : Fin 27, rationalSparseZeroCheck (homogeneousCompletion5ForwardDen j)
      (homogeneousCompletion5ForwardTerms j) := by
  intro j
  fin_cases j
  · exact homogeneousCompletion5_forward_column0_check
  · exact homogeneousCompletion5_forward_column1_check
  · exact homogeneousCompletion5_forward_column2_check
  · exact homogeneousCompletion5_forward_column3_check
  · exact homogeneousCompletion5_forward_column4_check
  · exact homogeneousCompletion5_forward_column5_check
  · exact homogeneousCompletion5_forward_column6_check
  · exact homogeneousCompletion5_forward_column7_check
  · exact homogeneousCompletion5_forward_column8_check
  · exact homogeneousCompletion5_forward_column9_check
  · exact homogeneousCompletion5_forward_column10_check
  · exact homogeneousCompletion5_forward_column11_check
  · exact homogeneousCompletion5_forward_column12_check
  · exact homogeneousCompletion5_forward_column13_check
  · exact homogeneousCompletion5_forward_column14_check
  · exact homogeneousCompletion5_forward_column15_check
  · exact homogeneousCompletion5_forward_column16_check
  · exact homogeneousCompletion5_forward_column17_check
  · exact homogeneousCompletion5_forward_column18_check
  · exact homogeneousCompletion5_forward_column19_check
  · exact homogeneousCompletion5_forward_column20_check
  · exact homogeneousCompletion5_forward_column21_check
  · exact homogeneousCompletion5_forward_column22_check
  · exact homogeneousCompletion5_forward_column23_check
  · exact homogeneousCompletion5_forward_column24_check
  · exact homogeneousCompletion5_forward_column25_check
  · exact homogeneousCompletion5_forward_column26_check


theorem homogeneousCompletion5_reverse_check :
    ∀ j : Fin 5, rationalSparseZeroCheck (homogeneousCompletion5ReverseDen j)
      (homogeneousCompletion5ReverseTerms j) := by
  intro j
  fin_cases j
  · exact homogeneousCompletion5_reverse_column0_check
  · exact homogeneousCompletion5_reverse_column1_check
  · exact homogeneousCompletion5_reverse_column2_check
  · exact homogeneousCompletion5_reverse_column3_check
  · exact homogeneousCompletion5_reverse_column4_check


theorem homogeneousCompletion5_residual_check :
    ∀ j : Fin 5, rationalSparseZeroCheck (homogeneousCompletion5ResidualDen j)
      (homogeneousCompletion5ResidualTerms j) := by
  intro j
  fin_cases j
  · exact homogeneousCompletion5_residual_column0_check
  · exact homogeneousCompletion5_residual_column1_check
  · exact homogeneousCompletion5_residual_column2_check
  · exact homogeneousCompletion5_residual_column3_check
  · exact homogeneousCompletion5_residual_column4_check


end Biunimodular.F11
