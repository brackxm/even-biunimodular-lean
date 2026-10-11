/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusSparseLeading
import Biunimodular.F11.TorusOriginalGeneratorsData
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

theorem torusSparseSumProducts_mem_ideal
    (I : Ideal (MvPolynomial (Fin 7) ℂ))
    (ps : List (List RurInverseTerm7 × List RurInverseTerm7))
    (hI : ∀ p ∈ ps, torusSparsePolynomial p.2 ∈ I) :
    (ps.map fun p => torusSparsePolynomial p.1 * torusSparsePolynomial p.2).sum ∈ I := by
  induction ps with
  | nil => exact I.zero_mem
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons]
    exact I.add_mem (I.mul_mem_left _ (hI p (by simp)))
      (ih (fun q hq => hI q (by simp [hq])))

/-- A short checked reduction identity transfers membership from the
already proved reducer polynomials to its new polynomial. -/
theorem torusSparseIdealCertificate_sound
    (I : Ideal (MvPolynomial (Fin 7) ℂ))
    (ps : List (List RurInverseTerm7 × List RurInverseTerm7))
    (target : List RurInverseTerm7)
    (hI : ∀ p ∈ ps, torusSparsePolynomial p.2 ∈ I)
    (h : rurInverseSparseNormalize (rurInverseSparseSumProducts
      (ps ++ [(rurInverseSparseScale (-1) target, rurInverseSparseOne)])) = []) :
    torusSparsePolynomial target ∈ I := by
  have hs := rurInverseSparseZeroCheck_sound _ h
    (MvPolynomial.X 0 : MvPolynomial (Fin 7) ℂ) (MvPolynomial.X 1)
    (MvPolynomial.X 2) (MvPolynomial.X 3) (MvPolynomial.X 5)
    (MvPolynomial.X 4) (MvPolynomial.X 6)
  have hone : torusSparsePolynomial rurInverseSparseOne = 1 := by
    simp [torusSparsePolynomial, rurInverseSparseOne, rurInverseSparseEval,
      rurInverseSparseTermEval]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, rurInverseSparseEval_scale,
    Int.cast_neg, Int.cast_one] at hs
  change (ps.map fun p => torusSparsePolynomial p.1 * torusSparsePolynomial p.2).sum +
    (-1 : MvPolynomial (Fin 7) ℂ) * torusSparsePolynomial target *
      torusSparsePolynomial rurInverseSparseOne = 0 at hs
  rw [hone, mul_one] at hs
  have he : torusSparsePolynomial target =
      (ps.map fun p => torusSparsePolynomial p.1 * torusSparsePolynomial p.2).sum := by
    linear_combination -hs
  rw [he]
  exact torusSparseSumProducts_mem_ideal I ps hI

/-- Clearing denominators is sound because a nonzero integer is a unit in
the complex polynomial ring. -/
theorem torusSparseIdealCertificate_scaled_sound
    (I : Ideal (MvPolynomial (Fin 7) ℂ))
    (ps : List (List RurInverseTerm7 × List RurInverseTerm7))
    (target : List RurInverseTerm7) (d : ℤ) (hd : d ≠ 0)
    (hI : ∀ p ∈ ps, torusSparsePolynomial p.2 ∈ I)
    (h : rurInverseSparseNormalize (rurInverseSparseSumProducts
      (ps ++ [(rurInverseSparseScale (-1) (rurInverseSparseScale d target),
        rurInverseSparseOne)])) = []) :
    torusSparsePolynomial target ∈ I := by
  have hm := torusSparseIdealCertificate_sound I ps (rurInverseSparseScale d target) hI h
  have hu : IsUnit (d : MvPolynomial (Fin 7) ℂ) := by
    have hc : (d : ℂ) ≠ 0 := by exact_mod_cast hd
    simpa only [map_intCast] using (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  apply (I.unit_mul_mem_iff_mem hu).mp
  simpa only [torusSparsePolynomial, rurInverseSparseEval_scale] using hm

end
end Biunimodular.F11
