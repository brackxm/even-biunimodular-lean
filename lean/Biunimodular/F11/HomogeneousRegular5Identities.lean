/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousRegular5Data

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-!
-/


theorem homogeneousRegular5_syzygy_identity :
    fixedSliceSparseSystemIdentity (List.replicate 25 [])
      homogeneousRegular5Syzygies (homogeneousRegularOriginals.take 5) := by
  unfold fixedSliceSparseSystemIdentity
  native_decide

theorem homogeneousRegular5_last_identity :
    fixedSliceSparseSystemIdentity homogeneousRegular5LastComponents
      homogeneousRegular5LastWitnesses (homogeneousRegularOriginals.take 4) := by
  unfold fixedSliceSparseSystemIdentity
  native_decide

theorem homogeneousRegular5_scales_positive :
    ∀ d ∈ homogeneousRegular5Scales, 0 < d := by native_decide

theorem homogeneousRegular5_last_mem :
    ∀ p ∈ homogeneousRegular5LastComponents,
      homogeneousSparsePolynomial p ∈
        Ideal.span (Set.range (fun g : {g // g ∈ homogeneousRegularOriginals.take 4} =>
          homogeneousSparsePolynomial g.val)) := by
  apply homogeneousRegular5_last_identity.mem_ideal
  intro g hg
  exact Ideal.subset_span ⟨⟨g, hg⟩, rfl⟩

end Biunimodular.F11
