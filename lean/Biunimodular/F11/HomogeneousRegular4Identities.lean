/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousRegular4Data

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-!
-/


theorem homogeneousRegular4_syzygy_identity :
    fixedSliceSparseSystemIdentity (List.replicate 11 [])
      homogeneousRegular4Syzygies (homogeneousRegularOriginals.take 4) := by
  unfold fixedSliceSparseSystemIdentity
  native_decide

theorem homogeneousRegular4_last_identity :
    fixedSliceSparseSystemIdentity homogeneousRegular4LastComponents
      homogeneousRegular4LastWitnesses (homogeneousRegularOriginals.take 3) := by
  unfold fixedSliceSparseSystemIdentity
  native_decide

theorem homogeneousRegular4_scales_positive :
    ∀ d ∈ homogeneousRegular4Scales, 0 < d := by native_decide

theorem homogeneousRegular4_last_mem :
    ∀ p ∈ homogeneousRegular4LastComponents,
      homogeneousSparsePolynomial p ∈
        Ideal.span (Set.range (fun g : {g // g ∈ homogeneousRegularOriginals.take 3} =>
          homogeneousSparsePolynomial g.val)) := by
  apply homogeneousRegular4_last_identity.mem_ideal
  intro g hg
  exact Ideal.subset_span ⟨⟨g, hg⟩, rfl⟩

end Biunimodular.F11
