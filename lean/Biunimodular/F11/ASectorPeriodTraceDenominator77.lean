/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodOrderCoordinates77

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- The certified scaled inverse bounds every algebraic integer's basis
coordinates by 77, without computing an adjugate or assuming maximality. -/
theorem periodBasis_integral_denominator_bound77 {x : conductor77PeriodField}
    (hx : IsIntegral ℤ x) (i : Fin 6) :
    ∃ z : ℤ, (z : ℚ) = 77 * conductor77PeriodBasis.repr x i := by
  classical
  let G : Matrix (Fin 6) (Fin 6) ℚ :=
    periodOrderTraceGramData77.map (Int.castRingHom ℚ)
  let H : Matrix (Fin 6) (Fin 6) ℚ :=
    periodOrderTraceDualData77.map (Int.castRingHom ℚ)
  let c : Fin 6 → ℚ := fun j => conductor77PeriodBasis.repr x j
  let t : Fin 6 → ℚ := fun j =>
    Algebra.trace ℚ conductor77PeriodField (x * conductor77PeriodBasis j)
  have ht : Matrix.vecMul c G = t := by
    funext j
    exact (periodBasis_trace_coordinates77 x j).symm
  have hGH : G * H = (77 : ℚ) • 1 := by
    have h := congrArg (Int.castRingHom ℚ).mapMatrix
      periodOrderTraceGramData77_mul_dual
    rw [map_mul, map_ofNat] at h
    simpa only [G, H, RingHom.mapMatrix_apply, Matrix.smul_one_eq_diagonal,
      Matrix.diagonal_ofNat] using h
  have he : Matrix.vecMul t H = (77 : ℚ) • c := by
    rw [← ht, Matrix.vecMul_vecMul, hGH, Matrix.vecMul_smul, Matrix.vecMul_one]
  have hsum : IsIntegral ℤ (Matrix.vecMul t H i) := by
    change IsIntegral ℤ (∑ j : Fin 6,
      t j * (periodOrderTraceDualData77 j i : ℚ))
    apply IsIntegral.sum
    intro j _
    obtain ⟨z, hz⟩ := periodBasis_trace_integral77 hx j
    have htj : IsIntegral ℤ (t j) := by
      rw [show t j = (z : ℚ) from hz.symm]
      exact isIntegral_algebraMap
    exact htj.mul isIntegral_algebraMap
  rw [he] at hsum
  exact IsIntegrallyClosed.isIntegral_iff.mp hsum

/-- The original discriminant bound follows from the stronger denominator-77
bound, retaining the existing interface for the integer-order proofs. -/
theorem periodBasis_integral_denominator77 {x : conductor77PeriodField}
    (hx : IsIntegral ℤ x) (i : Fin 6) :
    ∃ z : ℤ, (z : ℚ) = (7^5 * 11^3 : ℚ) * conductor77PeriodBasis.repr x i := by
  obtain ⟨z, hz⟩ := periodBasis_integral_denominator_bound77 hx i
  refine ⟨(7^4 * 11^2 : ℤ) * z, ?_⟩
  push_cast
  rw [hz]
  ring

/-- Multiplying any algebraic integer by the order discriminant places it
in the actual integer period order. -/
theorem periodIntegerSpan77_discriminant_smul_mem {x : conductor77PeriodField}
    (hx : IsIntegral ℤ x) : (7^5 * 11^3 : ℚ) • x ∈ periodIntegerSpan77 := by
  rw [periodIntegerSpan77_mem_iff_coordinates]
  intro i
  simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    using periodBasis_integral_denominator77 hx i

end
end Biunimodular.F11
