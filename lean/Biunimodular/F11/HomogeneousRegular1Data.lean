/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousRegularOriginalData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-!
-/

def homogeneousRegular1S1_1 : FixedSliceSparsePolynomial :=
  []

def homogeneousRegular1Syzygies : List (List FixedSliceSparsePolynomial) :=
  [[homogeneousRegular1S1_1]]

def homogeneousRegular1LastWitnesses : List (List FixedSliceSparsePolynomial) :=
  [[]]

def homogeneousRegular1LastComponents : List FixedSliceSparsePolynomial :=
  [homogeneousRegular1S1_1]

def homogeneousRegular1Scales : List ℕ :=
  [1]

end Biunimodular.F11
