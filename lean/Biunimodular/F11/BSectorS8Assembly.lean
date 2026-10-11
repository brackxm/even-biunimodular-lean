/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.DegreeEightS8FiniteBridge
import Biunimodular.F11.DegreeEight875Normalization

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# The B-sector `S_8` theorem: assembly

The group-theory endpoint uses the specialized finite 8/7/5 generation
certificate instead of Jordan's general prime-cycle theorem.  The heavier
mod-37/mod-211 polynomial arithmetic is preserved independently in
`BSectorFiniteArithmetic` and is not a dependency of this assembly layer.
-/

/-- A full symmetric image for a permutation action on eight letters.
The concrete polynomial action and its root count are established separately. -/
structure BSectorGaloisS8Certificate where
  permutationData : DegreeEightGaloisPermutationData
  image_eq_top : permutationData.image = ⊤

/-- Once Dedekind produces the three concrete cycle elements, the proved
8/7/5 generation theorem finishes the group identification. -/
def assemble_bSector_S8
    (hperm : DegreeEightGaloisPermutationData) :
    BSectorGaloisS8Certificate where
  permutationData := hperm
  image_eq_top := degreeEight_image_eq_top_of_875 degreeEight875Generation hperm

end Biunimodular.F11
