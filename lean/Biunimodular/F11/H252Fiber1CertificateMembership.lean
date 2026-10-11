/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber1CertificateBlock049Semantics
import Biunimodular.F11.TorusFiberProjectionMembership

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
noncomputable section
private theorem h252Fiber1CertificateOriginal_mem : ∀ j,
    torusSparsePolynomial (h252Fiber1CertificateOriginal j) ∈ h252FiberProjectionIdeal 0 := by
  intro j
  fin_cases j
  · rw [torusFiberProjection_mem_iff]
    change h252FiberProjection 0 * rurInverseSparseEval
      (rurInverseSparseOfZ5 h252FiberCRTQ1) (h252LocalizedTorusVar 0)
      (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
      (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0
    rw [rurInverseSparseEval_ofZ5]
    exact h252FiberProjection_annihilator 0
  · rw [torusFiberProjection_mem_iff]
    change h252FiberProjection 0 * rurInverseSparseEval torusFiberOriginal1
      (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2)
      (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4)
      (h252LocalizedTorusVar 6) = 0
    rw [torusFiberOriginal1_quotient_zero, mul_zero]
  · rw [torusFiberProjection_mem_iff]
    change h252FiberProjection 0 * rurInverseSparseEval torusFiberOriginal2
      (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2)
      (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4)
      (h252LocalizedTorusVar 6) = 0
    rw [torusFiberOriginal2_quotient_zero, mul_zero]
  · rw [torusFiberProjection_mem_iff]
    change h252FiberProjection 0 * rurInverseSparseEval torusFiberOriginal3
      (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2)
      (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4)
      (h252LocalizedTorusVar 6) = 0
    rw [torusFiberOriginal3_quotient_zero, mul_zero]
  · rw [torusFiberProjection_mem_iff]
    change h252FiberProjection 0 * rurInverseSparseEval torusFiberOriginal4
      (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2)
      (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4)
      (h252LocalizedTorusVar 6) = 0
    rw [torusFiberOriginal4_quotient_zero, mul_zero]
  · rw [torusFiberProjection_mem_iff]
    change h252FiberProjection 0 * rurInverseSparseEval torusFiberOriginal5
      (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2)
      (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4)
      (h252LocalizedTorusVar 6) = 0
    rw [torusFiberOriginal5_quotient_zero, mul_zero]
  · rw [torusFiberProjection_mem_iff]
    change h252FiberProjection 0 * rurInverseSparseEval torusFiberOriginal6
      (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2)
      (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4)
      (h252LocalizedTorusVar 6) = 0
    rw [torusFiberOriginal6_quotient_zero, mul_zero]
  · rw [torusFiberProjection_mem_iff]
    change h252FiberProjection 0 * rurInverseSparseEval torusFiberOriginal7
      (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2)
      (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4)
      (h252LocalizedTorusVar 6) = 0
    rw [torusFiberOriginal7_quotient_zero, mul_zero]
  · rw [torusFiberProjection_mem_iff]
    change h252FiberProjection 0 * rurInverseSparseEval torusFiberOriginal8
      (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2)
      (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4)
      (h252LocalizedTorusVar 6) = 0
    rw [torusFiberOriginal8_quotient_zero, mul_zero]
  · rw [torusFiberProjection_mem_iff]
    change h252FiberProjection 0 * rurInverseSparseEval torusFiberOriginal9
      (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2)
      (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4)
      (h252LocalizedTorusVar 6) = 0
    rw [torusFiberOriginal9_quotient_zero, mul_zero]
  · rw [torusFiberProjection_mem_iff]
    change h252FiberProjection 0 * rurInverseSparseEval torusFiberOriginal10
      (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1) (h252LocalizedTorusVar 2)
      (h252LocalizedTorusVar 3) (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4)
      (h252LocalizedTorusVar 6) = 0
    rw [torusFiberOriginal10_quotient_zero, mul_zero]

theorem h252Fiber1Certificate_mem_projection : ∀ i, i < 60 →
    torusSparsePolynomial (h252Fiber1CertificateBasis i) ∈ h252FiberProjectionIdeal 0 := by
  apply h252Fiber1CertificateBlock049_mem (h252FiberProjectionIdeal 0)
  intro i hi
  simpa only [h252Fiber1CertificateBasis, dite_eq_left hi] using h252Fiber1CertificateOriginal_mem ⟨i,hi⟩
end

end Biunimodular.F11
