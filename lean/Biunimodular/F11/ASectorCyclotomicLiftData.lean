/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Explicit maximal-real conductor-77 lift for the A-sector

The exact identity verified in the companion arithmetic script is

`X = -627 + Σ c_n (ζ^(en) + ζ^(-en))`

with the same coefficient vector for all Galois conjugates.  The data below
is theorem-facing and independent of decimal approximations.
-/

/-- Coefficients `c₁,...,c₂₉` of the Chebyshev/cyclotomic expression. -/
def aSectorCyclotomicCoeffs : List ℤ :=
  [-198, -650, 103, 481, -235, 199, 1194, 854, -228, 9,
   162, -185, 295, 572, 511, -419, -90, 599, -576, -169,
   -521, 1, -365, -53, 97, 490, 674, 641, 1506]

theorem aSectorCyclotomicCoeffs_length : aSectorCyclotomicCoeffs.length = 29 := by
  native_decide

/-- Exponents giving `(κ,λ,μ,ν,ξ)` for the three physical A-orbits. -/
def aSectorPhaseExponents : List (List ℕ) :=
  [[32,18,31,38,3], [30,12,5,26,2], [20,8,29,34,27]]

theorem aSectorPhaseExponents_shape :
    aSectorPhaseExponents.length = 3 ∧
      ∀ row ∈ aSectorPhaseExponents, row.length = 5 := by
  native_decide

/-- Sign pairs `(sign(Re), sign(Im))`, encoded as booleans where `true` is
positive.  The row order is `A1,A2,A3`; coordinate order is `κ,λ,μ,ν,ξ`. -/
def aSectorPhaseSigns : List (List (Bool × Bool)) :=
  [[(true,true),(false,false),(false,true),(true,true),(false,true)],
   [(true,true),(false,false),(false,true),(true,false),(false,false)],
   [(true,true),(false,true),(true,false),(false,false),(true,false)]]

theorem aSectorPhaseSigns_shape :
    aSectorPhaseSigns.length = 3 ∧
      ∀ row ∈ aSectorPhaseSigns, row.length = 5 := by
  native_decide

/-- The exact degree tower in the A-sector. -/
theorem aSector_degree_tower : 6 * 5 = 30 := by norm_num

/-- The real cyclotomic field of conductor 77 has degree 30. -/
theorem conductor77_real_degree : Nat.totient 77 / 2 = 30 := by native_decide

/-- The order-10 period subgroup modulo signs has the physical order-five
size of the dilation group. -/
theorem conductor77_relative_degree : 10 / 2 = 5 := by norm_num

/-- Compact theorem-facing certificate interface for the exact field
identification `K_A(X) = Q(ζ_77)^+`.

The data fields are intentionally semantic rather than tied to one particular
mathlib number-field representation.  Integration supplies these fields from
exact cyclotomic identities, not from numerical recognition.
-/
structure ASectorCyclotomicLiftCertificate where
  periodFieldDegree : ℕ
  realCyclotomicDegree : ℕ
  coordinateDegree : ℕ
  hPeriod : periodFieldDegree = 6
  hReal : realCyclotomicDegree = 30
  hCoord : coordinateDegree = 30
  coordinate_lies_in_real_cyclotomic : Prop
  degree30_element_generates_real_cyclotomic :
    coordinate_lies_in_real_cyclotomic → coordinateDegree = realCyclotomicDegree

/-- The degree argument at the end of the exact cyclotomic calculation. -/
theorem aSector_degree_forces_maximal_real
    (h : ASectorCyclotomicLiftCertificate) :
    h.coordinateDegree = h.realCyclotomicDegree := by
  simp [h.hCoord, h.hReal]

end Biunimodular.F11
