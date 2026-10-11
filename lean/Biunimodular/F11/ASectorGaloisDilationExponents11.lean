/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorConductor77Certificates
import Biunimodular.F11.ASectorCyclotomicLiftData

set_option autoImplicit false

namespace Biunimodular.F11

/-- Canonical representative of an exponent modulo `77` and sign. -/
def canonicalSignedExponent77 (n : ℕ) : ℕ :=
  min (n % 77) ((77 - n % 77) % 77)

/-- The multiplier `62 = 6³` in the relative order-five Galois group. -/
def relativeGaloisExponentStep77 (n : ℕ) : ℕ :=
  canonicalSignedExponent77 (62 * n)

/-- Physical dilation in the ordered coordinates
`(κ, λ, μ, ν, ξ)`. -/
def dilateASectorExponentRow11 : List ℕ → List ℕ
  | a :: b :: c :: d :: e :: [] => [b, d, e, c, a]
  | row => row

/-- The three displayed exponent sets are exactly the three signed
cosets of the period subgroup `H₀` based at `3`, `2`, and `8`. -/
theorem aSectorPhaseExponents_H0_cosets :
    (aSectorPhaseExponents[0]!).toFinset =
      conductor77H0.image
        (fun h => canonicalSignedExponent77 (3 * h.val)) ∧
    (aSectorPhaseExponents[1]!).toFinset =
      conductor77H0.image
        (fun h => canonicalSignedExponent77 (2 * h.val)) ∧
    (aSectorPhaseExponents[2]!).toFinset =
      conductor77H0.image
        (fun h => canonicalSignedExponent77 (8 * h.val)) := by
  native_decide

/-- Multiplication of cyclotomic exponents by `62` induces precisely
the physical dilation permutation on each of the three A-sector rows. -/
theorem aSectorPhaseExponents_galois_dilation :
    ∀ row ∈ aSectorPhaseExponents,
      row.map relativeGaloisExponentStep77 =
        dilateASectorExponentRow11 row := by
  have h : aSectorPhaseExponents.Forall (fun row =>
      row.map relativeGaloisExponentStep77 =
        dilateASectorExponentRow11 row) := by native_decide
  exact List.forall_iff_forall_mem.mp h

/-- The exponent action has order five on all three physical A rows. -/
theorem aSectorPhaseExponents_galois_five_cycle :
    ∀ row ∈ aSectorPhaseExponents,
      (List.range 5).foldl
        (fun r _ => r.map relativeGaloisExponentStep77) row = row := by
  have h : aSectorPhaseExponents.Forall (fun row =>
      (List.range 5).foldl
        (fun r _ => r.map relativeGaloisExponentStep77) row = row) := by
    native_decide
  exact List.forall_iff_forall_mem.mp h

end Biunimodular.F11
