/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousRegular1Data

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-!
-/


theorem homogeneousRegular1_syzygy_identity :
    fixedSliceSparseSystemIdentity (List.replicate 1 [])
      homogeneousRegular1Syzygies (homogeneousRegularOriginals.take 1) := by
  unfold fixedSliceSparseSystemIdentity
  native_decide

theorem homogeneousRegular1_last_identity :
    fixedSliceSparseSystemIdentity homogeneousRegular1LastComponents
      homogeneousRegular1LastWitnesses (homogeneousRegularOriginals.take 0) := by
  unfold fixedSliceSparseSystemIdentity
  native_decide

theorem homogeneousRegular1_scales_positive :
    ∀ d ∈ homogeneousRegular1Scales, 0 < d := by native_decide

theorem homogeneousRegular1_last_mem :
    ∀ p ∈ homogeneousRegular1LastComponents,
      homogeneousSparsePolynomial p ∈
        Ideal.span (Set.range (fun g : {g // g ∈ homogeneousRegularOriginals.take 0} =>
          homogeneousSparsePolynomial g.val)) := by
  apply homogeneousRegular1_last_identity.mem_ideal
  intro g hg
  exact Ideal.subset_span ⟨⟨g, hg⟩, rfl⟩

end Biunimodular.F11
