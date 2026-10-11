/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceProjectiveChart
import Biunimodular.F11.FixedSliceProjectiveChartAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial HomogeneousLocalization AlgebraicGeometry
attribute [local instance] MvPolynomial.gradedAlgebra

private abbrev StandardGrading := homogeneousSubmodule (Fin 6) ℂ
private abbrev ProjectiveChartPoints :=
  {x : ProjectiveSpectrum StandardGrading // x ∈ ProjectiveSpectrum.basicOpen StandardGrading (X 0)}

def fixedSliceProjectiveChartPrimeEquiv :
    ProjectiveChartPoints ≃ PrimeSpectrum FixedSliceProjectiveChartRing :=
  (TopCat.homeoOfIso (projIsoSpecTopComponent
    (isHomogeneous_X ℂ (0 : Fin 6)) (by norm_num : 0 < (1 : ℕ)))).toEquiv

theorem fixedSliceProjectiveChartPrimeEquiv_equations (x : ProjectiveChartPoints) :
    x.val ∈ fixedSliceProjectiveZeroLocus ↔
      fixedSliceProjectiveChartIdeal ≤ (fixedSliceProjectiveChartPrimeEquiv x).asIdeal := by
  change fixedSliceHomogeneousIdeal ≤ x.val.asHomogeneousIdeal.toIdeal ↔ _
  rw [fixedSliceHomogeneousIdeal, Ideal.span_le, fixedSliceProjectiveChartIdeal, Ideal.span_le]
  simp only [Set.subset_def, Set.mem_range, exists_imp, forall_apply_eq_imp_iff,
    even11FixedSliceHomogeneousGenerators, fixedSliceHomogeneousGenerators, List.mem_ofFn]
  constructor
  · intro h i
    have hi := h _ ⟨i, rfl⟩
    exact (ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier x
      ⟨2, ⟨fixedSliceHomogeneousQuadric even11FourierNormalized i.succ,
        fixedSliceHomogeneousQuadric_isHomogeneous _ _⟩,
        ⟨X 0 ^ 2, by simpa using (isHomogeneous_X ℂ (0 : Fin 6)).pow 2⟩,
        ⟨2, rfl⟩⟩).mpr hi
  · intro h p hp
    obtain ⟨i, rfl⟩ := hp
    exact (ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier x
      ⟨2, ⟨fixedSliceHomogeneousQuadric even11FourierNormalized i.succ,
        fixedSliceHomogeneousQuadric_isHomogeneous _ _⟩,
        ⟨X 0 ^ 2, by simpa using (isHomogeneous_X ℂ (0 : Fin 6)).pow 2⟩,
        ⟨2, rfl⟩⟩).mp (h i)

private def zeroLocusEquivChartZeroLocus :
    fixedSliceProjectiveZeroLocus ≃
      {x : ProjectiveChartPoints // x.val ∈ fixedSliceProjectiveZeroLocus} where
  toFun x := ⟨⟨x.val, fixedSliceProjectiveZeroLocus_subset_chart x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every projective prime of the original homogeneous equations corresponds
to a prime of their actual rank-32 chart algebra. -/
def fixedSliceProjectiveZeroLocusEquivSpectrum :
    fixedSliceProjectiveZeroLocus ≃ PrimeSpectrum FixedSliceProjectiveChartAlgebra :=
  zeroLocusEquivChartZeroLocus.trans
    ((fixedSliceProjectiveChartPrimeEquiv.subtypeEquiv
      fixedSliceProjectiveChartPrimeEquiv_equations).trans
      fixedSliceProjectiveChartIdeal.primeSpectrumQuotientOrderIsoZeroLocus.toEquiv.symm)

def fixedSliceProjectiveChartSpectrumEquivPoints :
    PrimeSpectrum FixedSliceProjectiveChartAlgebra ≃ Even11FixedSlicePoint := by
  let e : Even11FixedSlicePoint ≃ FixedSliceTraceRoot :=
    Equiv.ofBijective
      (even11FixedSliceTraceRootMap even11FixedSliceTraceGeometryCertificate.trace_isRoot)
      even11FixedSliceTraceGeometryCertificate.trace_bijective
  letI : Finite Even11FixedSlicePoint := Finite.of_equiv FixedSliceTraceRoot e.symm
  let a : FixedSliceProjectiveChartAlgebra ≃ₐ[ℂ] (Even11FixedSlicePoint → ℂ) :=
    (fixedSliceProjectiveChartEquivNormalized.trans
      fixedSliceNormalizedAffineChartEquivFive).trans fixedSliceFiveAlgebraEquivFunctions
  exact (PrimeSpectrum.comapEquiv a.toRingEquiv).toEquiv.trans
    ((PrimeSpectrum.sigmaToPiHomeo (fun _ : Even11FixedSlicePoint => ℂ)).symm.toEquiv.trans
      (Equiv.sigmaUnique Even11FixedSlicePoint (fun _ => PrimeSpectrum ℂ)))

/-- The full homogeneous projective zero locus, including nonclosed primes,
consists of exactly the 32 certified fixed-slice points. -/
def fixedSliceProjectiveZeroLocusEquivPoints :
    fixedSliceProjectiveZeroLocus ≃ Even11FixedSlicePoint :=
  fixedSliceProjectiveZeroLocusEquivSpectrum.trans fixedSliceProjectiveChartSpectrumEquivPoints

theorem fixedSliceProjectiveZeroLocus_card : Nat.card fixedSliceProjectiveZeroLocus = 32 := by
  rw [Nat.card_congr fixedSliceProjectiveZeroLocusEquivPoints]
  exact even11FixedSliceGeometryCertificate.cardinality_core.1

end
end Biunimodular.F11
