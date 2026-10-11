/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Mathlib.Data.Matrix.Reflection
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

open Matrix

noncomputable section

/-- The 4×4 linear tail matrix obtained from E₁-E₂, E₃, E₄, E₅. -/
def tailMatrix (a b c d e f : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![e - c, f - d, -e, -f;
     a,     b,     c + e, d + f;
     1 + e, f,     a + c, b + d;
     a + c, b + d, 1 + a, b]

/-- The right hand side of the tail linear system. -/
def tailRhs (a b c d e f : ℝ) : Fin 4 → ℝ :=
  ![-(a - c + a*c + b*d + c*e + d*f - a*e - b*f),
    -(e + a*c + b*d + (1/2 : ℝ)),
    -(a*e + b*f + (1/2 : ℝ)),
    -(c*e + d*f + (1/2 : ℝ))]

def tailVec (g h j k : ℝ) : Fin 4 → ℝ := ![g,h,j,k]

/--
The four combinations of the autocorrelation equations used by the finite scanner.
The first row is `(E₁-E₂)/2`; the remaining rows are `E₃/2,E₄/2,E₅/2`.
-/
theorem tail_linear_system_of_autocorr
    (a b c d e f g h j k : ℝ)
    (E1 : 2 * a + 2 * (a * c + b * d) + 2 * (c * e + d * f) + 2 * (e * g + f * h) +
      2 * (g * j + h * k) + 1 = 0)
    (E2 : 2 * c + 2 * (a * e + b * f) + 2 * (c * g + d * h) + 2 * (e * j + f * k) +
      2 * (g * j + h * k) + 1 = 0)
    (E3 : 2 * e + 2 * (a * g + b * h) + 2 * (c * j + d * k) + 2 * (e * j + f * k) +
      2 * (a * c + b * d) + 1 = 0)
    (E4 : 2 * g + 2 * (a * j + b * k) + 2 * (c * j + d * k) + 2 * (e * g + f * h) +
      2 * (a * e + b * f) + 1 = 0)
    (E5 : 2 * j + 2 * (a * j + b * k) + 2 * (c * g + d * h) + 2 * (a * g + b * h) +
      2 * (c * e + d * f) + 1 = 0) :
    (tailMatrix a b c d e f).mulVecᵣ (tailVec g h j k) = tailRhs a b c d e f := by
  rw [Matrix.mulVecᵣ_eq]
  funext i
  fin_cases i <;>
    simp [tailMatrix, tailRhs, tailVec, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    nlinarith [E1, E2, E3, E4, E5]

end

end Biunimodular.F11
