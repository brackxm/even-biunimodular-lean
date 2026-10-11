/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusMacaulayTextData

set_option autoImplicit false
namespace Biunimodular.F11

/-- Share repeated coefficient polynomials in untrusted matrix data. The
result remains an ordinary sparse matrix covered by all exact checks. -/
def torusMacaulayParseIndexedRow (coefficients : Array (List ℤ)) (text : String) :
    TorusMacaulayRow :=
  (text.splitOn ";").filterMap fun entry =>
    match (torusMacaulayParseIntegerRow entry).toList with
    | column :: index :: _ => some (column.toNat, coefficients[index.toNat]?.getD [])
    | _ => none

end Biunimodular.F11
