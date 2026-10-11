/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Biunimodular.F11.Even11PrincipalMinorData

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# Polynomial model of the six-coordinate even Fourier matrix at p = 11

Let `α = ζ₁₁ + ζ₁₁⁻¹ = 2 cos(2π/11)`. Its minimal polynomial is

  α^5 + α^4 - 4 α^3 - 3 α^2 + 3 α + 1.

The unnormalised restricted Fourier operator has entries

  M[t,0] = 1,
  M[t,r] = ζ₁₁^(tr) + ζ₁₁^(-tr),  r > 0.

The latter are represented by the Chebyshev recurrence
`S_(n+1) = α S_n - S_(n-1)` and reduced to degree < 5.
The companion certificate checks every nonempty principal minor of this
matrix, i.e. all 63 support patterns.
-/

/-- Minimal polynomial of `2 cos(2π/11)`. -/
def alpha11Minpoly : ℤ[X] :=
  X^5 + X^4 - 4*X^3 - 3*X^2 + 3*X + 1

/-- Reduced representatives of `ζ^n + ζ^{-n}` for `n=0,...,5`. -/
def even11CosRep : Fin 6 → ℤ[X]
  | 0 => 2
  | 1 => X
  | 2 => X^2 - 2
  | 3 => X^3 - 3*X
  | 4 => X^4 - 4*X^2 + 2
  | 5 => -X^4 - X^3 + 3*X^2 + 2*X - 1

/-- Fold an exponent modulo 11 using `S_n = S_{11-n}`. -/
def even11FoldExponent (n : Nat) : Fin 6 :=
  let r := n % 11
  if h : r ≤ 5 then
    ⟨r, by omega⟩
  else
    ⟨11-r, by omega⟩

/-- Polynomial-entry model of the unnormalised even Fourier matrix. -/
def even11FourierPolyEntry (t r : Fin 6) : ℤ[X] :=
  if r = 0 then 1
  else even11CosRep (even11FoldExponent (t.1 * r.1))

/-- The first row is `(1,2,2,2,2,2)`, exactly as in the formula. -/
theorem even11FourierPolyEntry_row_zero :
    (fun r : Fin 6 => even11FourierPolyEntry 0 r) = ![1,2,2,2,2,2] := by
  funext r
  fin_cases r <;>
    norm_num [even11FourierPolyEntry, even11FoldExponent, even11CosRep]

/-- The first column is identically one. -/
theorem even11FourierPolyEntry_col_zero :
    ∀ t : Fin 6, even11FourierPolyEntry t 0 = 1 := by
  intro t
  simp [even11FourierPolyEntry]

end

end Biunimodular.F11
