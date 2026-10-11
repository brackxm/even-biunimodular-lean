/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusOriginalGeneratorsData

set_option autoImplicit false
namespace Biunimodular.F11

/-- Computable membership check in exactly the original seven generators.
Kept separate from the scheme proof so coefficient checks need fewer imports. -/
def torusSpanningMembershipTerms
    (m1 m2 m3 m4 m5 m6 m7 target : List RurInverseTerm7) :=
  [(m1, rurInverseGenerator1), (m2, rurInverseGenerator2),
    (m3, rurInverseGenerator3), (m4, rurInverseGenerator4),
    (m5, rurInverseGenerator5), (m6, rurInverseGenerator6),
    (m7, rurInverseGenerator7),
    (rurInverseSparseScale (-1) target, rurInverseSparseOne)]

end Biunimodular.F11
