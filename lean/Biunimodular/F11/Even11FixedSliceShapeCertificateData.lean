/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FixedSliceShapeCertificateDataLiterals158

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Biunimodular.F11

/-! Generated exact data for the complete 32-point fixed-slice shape certificate.
-/

theorem fixedSliceProvenanceIdentity :
    fixedSliceSparseScaledSystemIdentity fixedSliceProvenanceTargets
      fixedSliceProvenanceMultipliers fixedSliceOriginalSystem := by
  unfold fixedSliceSparseScaledSystemIdentity fixedSliceSparseSystemIdentity
  native_decide

theorem fixedSliceReductionIdentity :
    fixedSliceSparseScaledSystemIdentity fixedSliceReductionTargets
      fixedSliceReductionMultipliers fixedSliceGroebnerSystem := by
  unfold fixedSliceSparseScaledSystemIdentity fixedSliceSparseSystemIdentity
  native_decide

theorem fixedSliceReverseIdentity :
    fixedSliceSparseScaledSystemIdentity fixedSliceReverseTargets
      fixedSliceReverseMultipliers fixedSliceShapeSystem := by
  unfold fixedSliceSparseScaledSystemIdentity fixedSliceSparseSystemIdentity
  native_decide

theorem fixedSliceProvenanceScales_ne_zero :
    ∀ target ∈ fixedSliceProvenanceTargets, target.1 ≠ 0 := by
  native_decide

theorem fixedSliceReductionScales_ne_zero :
    ∀ target ∈ fixedSliceReductionTargets, target.1 ≠ 0 := by
  native_decide

theorem fixedSliceReverseScales_ne_zero :
    ∀ target ∈ fixedSliceReverseTargets, target.1 ≠ 0 := by
  native_decide

private theorem fixedSliceProvenanceTargets_projection :
    fixedSliceProvenanceTargets.map Prod.snd = fixedSliceGroebnerSystem := by
  native_decide

private theorem fixedSliceReductionTargets_projection :
    fixedSliceReductionTargets.map Prod.snd = fixedSliceShapeSystem := by
  native_decide

private theorem fixedSliceReverseTargets_projection :
    fixedSliceReverseTargets.map Prod.snd = fixedSliceOriginalSystem := by
  native_decide

theorem fixedSliceShapeSystem_vanish
    (x5 x4 x3 x2 x1 trace : ℂ)
    (hzero : ∀ generator ∈ fixedSliceOriginalSystem,
      fixedSliceSparseEval generator x5 x4 x3 x2 x1 trace = 0) :
    ∀ shape ∈ fixedSliceShapeSystem,
      fixedSliceSparseEval shape x5 x4 x3 x2 x1 trace = 0 := by
  have hgroebner := fixedSliceSparseScaledSystemIdentity.vanish_targets
    fixedSliceProvenanceIdentity fixedSliceProvenanceTargets_projection
      x5 x4 x3 x2 x1 trace fixedSliceProvenanceScales_ne_zero hzero
  exact fixedSliceSparseScaledSystemIdentity.vanish_targets
    fixedSliceReductionIdentity fixedSliceReductionTargets_projection
      x5 x4 x3 x2 x1 trace fixedSliceReductionScales_ne_zero hgroebner

theorem fixedSliceOriginalSystem_vanish_of_shape
    (x5 x4 x3 x2 x1 trace : ℂ)
    (hzero : ∀ shape ∈ fixedSliceShapeSystem,
      fixedSliceSparseEval shape x5 x4 x3 x2 x1 trace = 0) :
    ∀ generator ∈ fixedSliceOriginalSystem,
      fixedSliceSparseEval generator x5 x4 x3 x2 x1 trace = 0 := by
  exact fixedSliceSparseScaledSystemIdentity.vanish_targets
    fixedSliceReverseIdentity fixedSliceReverseTargets_projection
      x5 x4 x3 x2 x1 trace fixedSliceReverseScales_ne_zero hzero

end Biunimodular.F11
