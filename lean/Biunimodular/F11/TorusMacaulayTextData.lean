/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusMacaulaySparseMatrix

set_option autoImplicit false
namespace Biunimodular.F11

/-- Compact untrusted data. Every use is covered by the inverse and exact
column checks; parsing itself is not an algebraic assumption. -/
def torusMacaulayParseSparseRow (text : String) : TorusMacaulayRow :=
  (text.splitOn ";").filterMap fun entry =>
    match (torusMacaulayParseIntegerRow entry).toList with
    | [] => none
    | index :: coefficients => some (index.toNat, coefficients)

end Biunimodular.F11
