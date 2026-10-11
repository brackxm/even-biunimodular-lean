/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousRegular3Data

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-!
-/


theorem homogeneousRegular3_syzygy_identity :
    fixedSliceSparseSystemIdentity (List.replicate 4 [])
      homogeneousRegular3Syzygies (homogeneousRegularOriginals.take 3) := by
  unfold fixedSliceSparseSystemIdentity
  native_decide

theorem homogeneousRegular3_last_identity :
    fixedSliceSparseSystemIdentity homogeneousRegular3LastComponents
      homogeneousRegular3LastWitnesses (homogeneousRegularOriginals.take 2) := by
  unfold fixedSliceSparseSystemIdentity
  native_decide

theorem homogeneousRegular3_scales_positive :
    ∀ d ∈ homogeneousRegular3Scales, 0 < d := by native_decide

theorem homogeneousRegular3_last_mem :
    ∀ p ∈ homogeneousRegular3LastComponents,
      homogeneousSparsePolynomial p ∈
        Ideal.span (Set.range (fun g : {g // g ∈ homogeneousRegularOriginals.take 2} =>
          homogeneousSparsePolynomial g.val)) := by
  apply homogeneousRegular3_last_identity.mem_ideal
  intro g hg
  exact Ideal.subset_span ⟨⟨g, hg⟩, rfl⟩

end Biunimodular.F11
