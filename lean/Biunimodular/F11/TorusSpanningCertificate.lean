/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusSparseLeading
import Biunimodular.F11.TorusSpanningMembershipTerms
import Biunimodular.F11.RurInverseGeneratorSemantics
import Biunimodular.F11.TorusReferenceSpanningCriterion
import Biunimodular.F11.H252SchemeDimensionCriterion

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11

noncomputable section

theorem rurInverseSparseEval_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : List RurInverseTerm7) (z1 z2 z3 z4 w z5 x : R) :
    f (rurInverseSparseEval p z1 z2 z3 z4 w z5 x) =
      rurInverseSparseEval p (f z1) (f z2) (f z3) (f z4) (f w) (f z5) (f x) := by
  induction p with
  | nil => simp [rurInverseSparseEval]
  | cons t p ih =>
    simpa [rurInverseSparseEval, rurInverseSparseTermEval] using ih

/-- A checked seven-generator identity puts the actual complex polynomial in
the original localized ideal. The large eliminant is not an extra generator. -/
theorem torusSpanningMembership_sound
    (m1 m2 m3 m4 m5 m6 m7 target : List RurInverseTerm7)
    (h : rurInverseSparseNormalize (rurInverseSparseSumProducts
      (torusSpanningMembershipTerms m1 m2 m3 m4 m5 m6 m7 target)) = []) :
    torusSparsePolynomial target ∈ h252LocalizedTorusIdeal := by
  have hs := rurInverseSparseZeroCheck_sound _ h
    (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1)
    (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
    (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6)
  simp only [torusSpanningMembershipTerms, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil,
    rurInverseGenerator1_quotient_zero, rurInverseGenerator2_quotient_zero,
    rurInverseGenerator3_quotient_zero, rurInverseGenerator4_quotient_zero,
    rurInverseGenerator5_quotient_zero, rurInverseGenerator6_quotient_zero,
    rurInverseGenerator7_quotient_zero, rurInverseSparseOne_eval,
    rurInverseSparseEval_scale, Int.cast_neg, Int.cast_one,
    mul_zero, zero_add, add_zero, mul_one] at hs
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change (Ideal.Quotient.mk h252LocalizedTorusIdeal) (torusSparsePolynomial target) = 0
  rw [torusSparsePolynomial, rurInverseSparseEval_map]
  change rurInverseSparseEval target (h252LocalizedTorusVar 0) (h252LocalizedTorusVar 1)
    (h252LocalizedTorusVar 2) (h252LocalizedTorusVar 3)
    (h252LocalizedTorusVar 5) (h252LocalizedTorusVar 4) (h252LocalizedTorusVar 6) = 0
  linear_combination -hs

/-- The verified low-degree certificates give a dimension bound on the
actual localized quotient. -/
theorem h252LocalizedTorus_dimension_of_spanning_certificates
    {ι : Type*} (g : ι → List RurInverseTerm7) (e : ι → RurInverseExponent7)
    (hI : ∀ i, torusSparsePolynomial (g i) ∈ h252LocalizedTorusIdeal)
    (hL : ∀ i, torusSparseLeadingCheck (g i) (e i))
    (hC : ∀ l ∈ torusReferenceLeadingExponents,
      ∃ i, torusSparseExponent (e i) ≤ Finsupp.equivFunOnFinite.symm l) :
    FiniteDimensional ℂ H252LocalizedTorusAlgebra ∧
      Module.finrank ℂ H252LocalizedTorusAlgebra ≤ 252 := by
  exact torusReferenceSpanningBound torusGrevlexOrder h252LocalizedTorusIdeal
    (fun i => torusSparsePolynomial (g i)) (fun i => (hL i).sound.1) hI (by
      intro l hl
      obtain ⟨i, hi⟩ := hC l hl
      exact ⟨i, by simpa only [(hL i).sound.2] using hi⟩)

theorem h252ComplexPhaseKCoordinate_surjective_of_spanning_certificates
    {ι : Type*} (g : ι → List RurInverseTerm7) (e : ι → RurInverseExponent7)
    (hI : ∀ i, torusSparsePolynomial (g i) ∈ h252LocalizedTorusIdeal)
    (hL : ∀ i, torusSparseLeadingCheck (g i) (e i))
    (hC : ∀ l ∈ torusReferenceLeadingExponents,
      ∃ i, torusSparseExponent (e i) ≤ Finsupp.equivFunOnFinite.symm l) :
    Function.Surjective h252ComplexPhaseKCoordinate := by
  have hB := h252LocalizedTorus_dimension_of_spanning_certificates g e hI hL hC
  let _ := hB.1
  exact h252ComplexPhaseKCoordinate_surjective_of_dimension hB.2

/-- The final assembly concerns the original ten-equation algebra. All
remaining assumptions are finite, explicit certificate checks. -/
theorem h252ComplexPhase_scheme_of_spanning_certificates
    {ι : Type*} (g : ι → List RurInverseTerm7) (e : ι → RurInverseExponent7)
    (hI : ∀ i, torusSparsePolynomial (g i) ∈ h252LocalizedTorusIdeal)
    (hL : ∀ i, torusSparseLeadingCheck (g i) (e i))
    (hC : ∀ l ∈ torusReferenceLeadingExponents,
      ∃ i, torusSparseExponent (e i) ≤ Finsupp.equivFunOnFinite.symm l) :
    IsReduced H252ComplexPhaseAlgebra ∧
      Module.finrank ℂ H252ComplexPhaseAlgebra = 252 ∧
      Nat.card (H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ) = 252 := by
  have hs := h252ComplexPhaseKCoordinate_surjective_of_spanning_certificates g e hI hL hC
  exact ⟨h252ComplexPhase_isReduced_of_surjective hs,
    h252ComplexPhase_finrank_of_surjective hs, h252ComplexPhase_point_count_of_surjective hs⟩

end
end Biunimodular.F11
