/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousSparseOrder

set_option autoImplicit false
namespace Biunimodular.F11

def homogeneousExponentSup (a b : FixedSliceSparseExponent) : FixedSliceSparseExponent :=
  ⟨max a.x5 b.x5, max a.x4 b.x4, max a.x3 b.x3,
    max a.x2 b.x2, max a.x1 b.x1, max a.trace b.trace⟩

def homogeneousExponentSub (a b : FixedSliceSparseExponent) : FixedSliceSparseExponent :=
  ⟨a.x5 - b.x5, a.x4 - b.x4, a.x3 - b.x3,
    a.x2 - b.x2, a.x1 - b.x1, a.trace - b.trace⟩

noncomputable section

theorem homogeneousExponent_sup (a b : FixedSliceSparseExponent) :
    homogeneousExponent (homogeneousExponentSup a b) = homogeneousExponent a ⊔ homogeneousExponent b := by
  ext i
  fin_cases i <;> simp [homogeneousExponentSup, homogeneousExponentFunction]

theorem homogeneousExponent_sub (a b : FixedSliceSparseExponent) :
    homogeneousExponent (homogeneousExponentSub a b) = homogeneousExponent a - homogeneousExponent b := by
  ext i
  fin_cases i <;> simp [homogeneousExponentSub, homogeneousExponentFunction]

end
end Biunimodular.F11
