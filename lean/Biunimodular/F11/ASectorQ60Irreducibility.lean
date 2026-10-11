/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IrreducibleSquaredCoordinate
import Biunimodular.F11.ASectorF30PhysicalPolynomialBridge11

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11

open Polynomial
noncomputable section

/-- The degree-sixty monic polynomial of twice the phase coordinate. -/
def aSectorG60 : ℚ[X] := (aSectorG30.map (Int.castRingHom ℚ)).comp (X ^ 2)

theorem aSectorG60_irreducible : Irreducible aSectorG60 := by
  apply irreducible_comp_square_of_norm_not_square _
    (aSectorG30_monic.map (Int.castRingHom ℚ)) aSectorG30_irreducible_over_Q
  have hd : (aSectorG30.map (Int.castRingHom ℚ)).natDegree = 30 :=
    (aSectorG30_monic.natDegree_map (Int.castRingHom ℚ)).trans aSectorG30_natDegree
  rw [hd]
  norm_num [aSectorG30]

/-- The the degree-sixty phase factor Q60. -/
def p150Q60KQ11 : ℚ[X] := (p150F30Y11.comp (X ^ 2)).map (Int.castRingHom ℚ)

theorem p150Q60KQ11_eq_scaled_G60 :
    p150Q60KQ11 = aSectorG60.comp (C 2 * X) := by
  rw [p150Q60KQ11, p150F30Y11_eq_aSectorG30_comp_four]
  simp only [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_X, Polynomial.map_pow, aSectorG60,
    Polynomial.comp_assoc]
  congr 1
  simp only [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
    Polynomial.pow_comp]
  rw [mul_pow, ← C_pow]
  norm_num

theorem p150Q60KQ11_irreducible : Irreducible p150Q60KQ11 := by
  let e := Polynomial.algEquivCMulXAddC (2 : ℚ) 0
  have h := (MulEquiv.irreducible_iff e).mpr aSectorG60_irreducible
  simpa only [e, Polynomial.algEquivCMulXAddC_apply, Polynomial.C_0, add_zero,
    ← Polynomial.comp_eq_aeval, ← p150Q60KQ11_eq_scaled_G60] using h

end
end Biunimodular.F11
