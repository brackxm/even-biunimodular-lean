/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodOrderCoordinates77
import Mathlib.LinearAlgebra.Matrix.Adjugate

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- The trace pairing bounds every algebraic integer's basis denominator by
the computed order discriminant. No maximality assumption is used. -/
theorem periodBasis_integral_denominator77 {x : conductor77PeriodField}
    (hx : IsIntegral ℤ x) (i : Fin 6) :
    ∃ z : ℤ, (z : ℚ) = (7^5 * 11^3 : ℚ) * conductor77PeriodBasis.repr x i := by
  classical
  let G : Matrix (Fin 6) (Fin 6) ℚ :=
    periodOrderTraceGramData77.map (Int.castRingHom ℚ)
  let c : Fin 6 → ℚ := fun j => conductor77PeriodBasis.repr x j
  let t : Fin 6 → ℚ := fun j =>
    Algebra.trace ℚ conductor77PeriodField (x * conductor77PeriodBasis j)
  have ht : Matrix.vecMul c G = t := by
    funext j
    exact (periodBasis_trace_coordinates77 x j).symm
  have hdet : G.det = (7^5 * 11^3 : ℚ) := by
    have h := (Int.castRingHom ℚ).map_det periodOrderTraceGramData77
    rw [periodOrderTraceGramData77_det] at h
    convert h.symm using 1 <;> norm_num [G, Int.castRingHom]
  have hadj : G.adjugate =
      periodOrderTraceGramData77.adjugate.map (Int.castRingHom ℚ) := by
    exact ((Int.castRingHom ℚ).map_adjugate periodOrderTraceGramData77).symm
  have he : Matrix.vecMul t G.adjugate = (7^5 * 11^3 : ℚ) • c := by
    rw [← ht, Matrix.vecMul_vecMul, Matrix.mul_adjugate, hdet,
      Matrix.vecMul_smul, Matrix.vecMul_one]
  have hsum : IsIntegral ℤ (Matrix.vecMul t G.adjugate i) := by
    rw [hadj]
    change IsIntegral ℤ (∑ j : Fin 6,
      t j * (periodOrderTraceGramData77.adjugate j i : ℚ))
    apply IsIntegral.sum
    intro j _
    obtain ⟨z, hz⟩ := periodBasis_trace_integral77 hx j
    have htj : IsIntegral ℤ (t j) := by
      rw [show t j = (z : ℚ) from hz.symm]
      exact isIntegral_algebraMap
    exact htj.mul isIntegral_algebraMap
  rw [he] at hsum
  exact IsIntegrallyClosed.isIntegral_iff.mp hsum

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
