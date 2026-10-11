/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodIntegerOrder77

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

theorem periodBasis_trace_product77 (i j : Fin 6) :
    Algebra.trace ℚ conductor77PeriodField
      (conductor77PeriodBasis i * conductor77PeriodBasis j) =
        (periodOrderTraceGramData77 i j : ℚ) := by
  have h := congrFun (congrFun conductor77PeriodBasis_traceMatrix i) j
  simpa [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Matrix.map_apply,
    Int.castRingHom] using h

theorem periodBasis_trace_coordinates77 (x : conductor77PeriodField) (j : Fin 6) :
    Algebra.trace ℚ conductor77PeriodField (x * conductor77PeriodBasis j) =
      ∑ i : Fin 6, conductor77PeriodBasis.repr x i * (periodOrderTraceGramData77 i j : ℚ) := by
  calc
    _ = Algebra.trace ℚ conductor77PeriodField
        ((∑ i : Fin 6, conductor77PeriodBasis.repr x i • conductor77PeriodBasis i) *
          conductor77PeriodBasis j) := by rw [conductor77PeriodBasis.sum_repr]
    _ = _ := by
      simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
        periodBasis_trace_product77, smul_eq_mul]

/-- Traces against every integral period are integers for any algebraic integer. -/
theorem periodBasis_trace_integral77 {x : conductor77PeriodField} (hx : IsIntegral ℤ x)
    (j : Fin 6) :
    ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ conductor77PeriodField
      (x * conductor77PeriodBasis j) := by
  have hj : IsIntegral ℤ (conductor77PeriodBasis j) := by
    rw [conductor77PeriodBasis_apply]
    exact periodFieldOrbit77_isIntegral_int j
  exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace (hx.mul hj))

/-- A possible larger-order class with denominator `p`, in the actual basis. -/
def periodFraction77 (p : ℤ) (v : Fin 6 → ℤ) : conductor77PeriodField :=
  ∑ i : Fin 6, ((v i : ℚ) / (p : ℚ)) • conductor77PeriodBasis i

theorem periodFraction77_repr (p : ℤ) (v : Fin 6 → ℤ) :
    conductor77PeriodBasis.repr (periodFraction77 p v) = fun i => (v i : ℚ) / (p : ℚ) :=
  conductor77PeriodBasis.repr_sum_self _

def periodIntegerCombination77 (v : Fin 6 → ℤ) : conductor77PeriodField :=
  ∑ i : Fin 6, (v i : ℚ) • conductor77PeriodBasis i

def periodIntegerMultiplicationMatrix77 (v : Fin 6 → ℤ) : Matrix (Fin 6) (Fin 6) ℤ :=
  fun i j => ∑ k : Fin 6, v k * periodOrderProductCoefficients77 k j i

theorem periodIntegerCombination77_leftMulMatrix (v : Fin 6 → ℤ) :
    Algebra.leftMulMatrix conductor77PeriodBasis (periodIntegerCombination77 v) =
      (periodIntegerMultiplicationMatrix77 v).map (Int.castRingHom ℚ) := by
  ext i j
  simp only [periodIntegerCombination77, map_sum, map_smul, Matrix.sum_apply,
    conductor77PeriodBasis_apply, conductor77PeriodBasis_leftMulMatrix,
    Matrix.map_apply, periodIntegerMultiplicationMatrix77,
    map_sum, map_mul]
  simp [Int.castRingHom]
  apply Finset.sum_congr rfl
  intro k _
  rfl

theorem periodFraction77_eq_smul (p : ℤ) (v : Fin 6 → ℤ) :
    periodFraction77 p v = (p : ℚ)⁻¹ • periodIntegerCombination77 v := by
  simp only [periodFraction77, periodIntegerCombination77, Finset.smul_sum,
    smul_smul, div_eq_mul_inv, mul_comm]

theorem periodIntegerCombination77_trace_pow (v : Fin 6 → ℤ) (k : ℕ) :
    Algebra.trace ℚ conductor77PeriodField (periodIntegerCombination77 v ^ k) =
      ((Matrix.trace (periodIntegerMultiplicationMatrix77 v ^ k) : ℤ) : ℚ) := by
  rw [Algebra.trace_eq_matrix_trace conductor77PeriodBasis, map_pow,
    periodIntegerCombination77_leftMulMatrix]
  have hpow := (Int.castRingHom ℚ).mapMatrix.map_pow (periodIntegerMultiplicationMatrix77 v) k
  have htrace := AddMonoidHom.map_trace (Int.castRingHom ℚ)
    (periodIntegerMultiplicationMatrix77 v ^ k)
  simp only [RingHom.mapMatrix_apply] at hpow
  rw [← hpow]
  simpa [Int.castRingHom] using htrace.symm

theorem periodFraction77_trace_pow (p : ℤ) (v : Fin 6 → ℤ) (k : ℕ) :
    Algebra.trace ℚ conductor77PeriodField (periodFraction77 p v ^ k) =
      ((Matrix.trace (periodIntegerMultiplicationMatrix77 v ^ k) : ℤ) : ℚ) / (p : ℚ)^k := by
  rw [periodFraction77_eq_smul, smul_pow, map_smul, periodIntegerCombination77_trace_pow]
  simp only [smul_eq_mul, inv_pow, div_eq_mul_inv, mul_comm]

/-- Every integral larger-order candidate must satisfy all power-trace divisibilities. -/
theorem periodFraction77_power_trace_divisibility (p : ℤ) (hp : p ≠ 0)
    (v : Fin 6 → ℤ) (hx : IsIntegral ℤ (periodFraction77 p v)) (k : ℕ) :
    p^k ∣ Matrix.trace (periodIntegerMultiplicationMatrix77 v ^ k) := by
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_trace (L := ℚ) (hx.pow k))
  rw [periodFraction77_trace_pow] at hz
  refine ⟨z, ?_⟩
  apply Int.cast_injective (α := ℚ)
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  push_cast
  exact (eq_div_iff (pow_ne_zero k hpQ)).mp hz |>.symm.trans (mul_comm _ _)

/-- Integrality forces the coefficient vector into the trace-Gram kernel
modulo its denominator. This is the bridge to the finite prime scans. -/
theorem periodFraction77_trace_divisibility (p : ℤ) (hp : p ≠ 0) (v : Fin 6 → ℤ)
    (hx : IsIntegral ℤ (periodFraction77 p v)) (j : Fin 6) :
    p ∣ ∑ i : Fin 6, v i * periodOrderTraceGramData77 i j := by
  obtain ⟨z, hz⟩ := periodBasis_trace_integral77 hx j
  rw [periodBasis_trace_coordinates77, periodFraction77_repr] at hz
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  refine ⟨z, ?_⟩
  apply Int.cast_injective (α := ℚ)
  push_cast
  calc
    _ = (p : ℚ) * (∑ i : Fin 6, (v i : ℚ) / (p : ℚ) * (periodOrderTraceGramData77 i j : ℚ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      field_simp
    _ = (p : ℚ) * (z : ℚ) := by rw [← hz]

end
end Biunimodular.F11
