/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false

namespace Biunimodular.F11

/-!
Exact reduced principal-minor data for the unnormalised six-coordinate
even Fourier matrix at p = 11.  Coefficients are in ascending powers of
`α = 2 cos(2π/11)` after reduction modulo
`α^5 + α^4 - 4α^3 - 3α^2 + 3α + 1`.
-/

abbrev MinorCoeff := Fin 5 → ℤ

def even11PrincipalMinorRemainders : List MinorCoeff := [
  ![1, 0, 0, 0, 0],
  ![0, 1, 0, 0, 0],
  ![-2, 1, 0, 0, 0],
  ![2, 0, -4, 0, 1],
  ![0, 0, -4, 0, 1],
  ![-5, -1, 7, 0, -2],
  ![-17, -3, 19, 0, -4],
  ![-2, 0, 1, 0, 0],
  ![-4, 0, 1, 0, 0],
  ![-1, -4, -3, 2, 1],
  ![3, -18, -5, 6, 1],
  ![-5, 1, 4, -1, -1],
  ![-9, 9, 22, -5, -7],
  ![12, 1, -3, -1, -1],
  ![66, 33, -55, -11, 11],
  ![-1, 2, 3, -1, -1],
  ![-3, 2, 3, -1, -1],
  ![-1, 5, -1, -2, 0],
  ![9, -1, -23, 0, 6],
  ![-3, -1, -2, 1, 1],
  ![-5, -17, 0, 7, 1],
  ![-9, -12, 15, 4, -3],
  ![33, -66, -33, 22, 11],
  ![2, -3, -5, 1, 1],
  ![8, -3, -13, 3, 3],
  ![2, -11, -3, 2, 1],
  ![-22, -11, 55, 0, -11],
  ![6, -11, -9, 6, 3],
  ![22, 11, 33, 0, -11],
  ![22, 33, 0, -11, 0],
  ![0, 363, 0, -121, 0],
  ![0, -3, 0, 1, 0],
  ![-2, -3, 0, 1, 0],
  ![-2, -1, -3, 0, 1],
  ![-6, 11, 9, -6, -3],
  ![2, 1, -5, 0, 1],
  ![-2, 11, 3, -2, -1],
  ![-8, 3, 13, -3, -3],
  ![-22, 33, 55, -11, -11],
  ![-3, 6, 3, -2, -1],
  ![9, 12, -15, -4, 3],
  ![5, 17, 0, -7, -1],
  ![33, 11, 22, -11, -11],
  ![-9, 1, 23, 0, -6],
  ![11, -55, 11, 22, 0],
  ![33, -22, -33, 11, 11],
  ![121, -242, -363, 121, 121],
  ![-6, -3, 5, 1, -1],
  ![-12, -1, 3, 1, 1],
  ![9, -9, -22, 5, 7],
  ![55, -11, -44, 11, 11],
  ![-3, 18, 5, -6, -1],
  ![11, 44, 33, -22, -11],
  ![44, 0, -11, 0, 0],
  ![242, 0, -121, 0, 0],
  ![17, 3, -19, 0, 4],
  ![55, 11, -77, 0, 22],
  ![0, 0, 44, 0, -11],
  ![-242, 0, 484, 0, -121],
  ![22, -11, 0, 0, 0],
  ![0, -121, 0, 0, 0],
  ![-121, 0, 0, 0, 0],
  ![-1331, 0, 0, 0, 0]
]

theorem even11PrincipalMinorRemainders_length :
    even11PrincipalMinorRemainders.length = 63 := by
  native_decide

theorem even11PrincipalMinorRemainders_all_nonzero :
    ∀ c ∈ even11PrincipalMinorRemainders, c ≠ 0 := by
  native_decide

/-- The exact certificate has one row for every nonempty subset of six
coordinates, encoded by masks 1,...,63. -/
def even11PrincipalMinorMasks : List Nat := List.range 63 |>.map (· + 1)

theorem even11PrincipalMinorMasks_eq :
    even11PrincipalMinorMasks = List.range' 1 63 := by
  native_decide

end Biunimodular.F11
