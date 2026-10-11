/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousRegular2Data

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-!
-/


theorem homogeneousRegular2_syzygy_identity :
    fixedSliceSparseSystemIdentity (List.replicate 1 [])
      homogeneousRegular2Syzygies (homogeneousRegularOriginals.take 2) := by
  unfold fixedSliceSparseSystemIdentity
  native_decide

theorem homogeneousRegular2_last_identity :
    fixedSliceSparseSystemIdentity homogeneousRegular2LastComponents
      homogeneousRegular2LastWitnesses (homogeneousRegularOriginals.take 1) := by
  unfold fixedSliceSparseSystemIdentity
  native_decide

theorem homogeneousRegular2_scales_positive :
    ∀ d ∈ homogeneousRegular2Scales, 0 < d := by native_decide

theorem homogeneousRegular2_last_mem :
    ∀ p ∈ homogeneousRegular2LastComponents,
      homogeneousSparsePolynomial p ∈
        Ideal.span (Set.range (fun g : {g // g ∈ homogeneousRegularOriginals.take 1} =>
          homogeneousSparsePolynomial g.val)) := by
  apply homogeneousRegular2_last_identity.mem_ideal
  intro g hg
  exact Ideal.subset_span ⟨⟨g, hg⟩, rfl⟩

end Biunimodular.F11
