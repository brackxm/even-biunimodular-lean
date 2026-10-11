/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceProjectiveSpectrumPoints
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev FixedSliceProjectiveAmbient : Scheme :=
  AlgebraicGeometry.Proj (homogeneousSubmodule (Fin 6) ℂ)

def fixedSliceProjectiveAmbientChart : FixedSliceProjectiveAmbient.Opens :=
  Proj.basicOpen (homogeneousSubmodule (Fin 6) ℂ) (X 0)

/-- The actual ambient projective chart, as an affine scheme. -/
def fixedSliceProjectiveAmbientChartIsoSpec :
    fixedSliceProjectiveAmbientChart.toScheme ≅ Spec (.of FixedSliceProjectiveChartRing) :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimageIso
    (projIsoSpec (homogeneousSubmodule (Fin 6) ℂ) (X 0)
      (isHomogeneous_X ℂ (0 : Fin 6)) (by norm_num : 0 < (1 : ℕ)))

theorem fixedSliceProjectiveAmbientChartIsoSpec_apply
    (x : fixedSliceProjectiveAmbientChart) :
    fixedSliceProjectiveAmbientChartIsoSpec.hom x = fixedSliceProjectiveChartPrimeEquiv x :=
  ProjectiveSpectrum.Proj.toSpec_base_apply_eq _ x

theorem fixedSliceProjectiveAmbientChartIsoSpec_inv_apply
    (p : PrimeSpectrum FixedSliceProjectiveChartRing) :
    fixedSliceProjectiveAmbientChartIsoSpec.inv p = fixedSliceProjectiveChartPrimeEquiv.symm p := by
  apply fixedSliceProjectiveChartPrimeEquiv.injective
  rw [← fixedSliceProjectiveAmbientChartIsoSpec_apply]
  simp

/-- The projective fixed-slice scheme: its original equations in the
single projective chart containing their full homogeneous zero locus. -/
def fixedSliceProjectiveScheme : Scheme :=
  Spec (.of FixedSliceProjectiveChartAlgebra)

def fixedSliceProjectiveSchemeι : fixedSliceProjectiveScheme ⟶ FixedSliceProjectiveAmbient :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk fixedSliceProjectiveChartIdeal)) ≫
    fixedSliceProjectiveAmbientChartIsoSpec.inv ≫ fixedSliceProjectiveAmbientChart.ι

theorem fixedSliceProjectiveSchemeι_apply
    (p : PrimeSpectrum FixedSliceProjectiveChartAlgebra) :
    fixedSliceProjectiveSchemeι p = (fixedSliceProjectiveZeroLocusEquivSpectrum.symm p).val := by
  change (fixedSliceProjectiveAmbientChartIsoSpec.inv
    (PrimeSpectrum.comap (Ideal.Quotient.mk fixedSliceProjectiveChartIdeal) p)).val = _
  rw [fixedSliceProjectiveAmbientChartIsoSpec_inv_apply]
  rfl

/-- The scheme embedding has exactly the original five-quadric projective
zero locus as its image. -/
theorem fixedSliceProjectiveSchemeι_range :
    Set.range fixedSliceProjectiveSchemeι = fixedSliceProjectiveZeroLocus := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    rw [fixedSliceProjectiveSchemeι_apply]
    exact (fixedSliceProjectiveZeroLocusEquivSpectrum.symm p).property
  · intro hx
    refine ⟨fixedSliceProjectiveZeroLocusEquivSpectrum ⟨x, hx⟩, ?_⟩
    rw [fixedSliceProjectiveSchemeι_apply, Equiv.symm_apply_apply]

instance fixedSliceProjectiveSchemeι_closedImmersion : IsClosedImmersion fixedSliceProjectiveSchemeι := by
  let : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk fixedSliceProjectiveChartIdeal))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsPreimmersion fixedSliceProjectiveSchemeι := by
    unfold fixedSliceProjectiveSchemeι
    have hq : IsPreimmersion
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk fixedSliceProjectiveChartIdeal))) :=
      inferInstance
    have hi : IsPreimmersion fixedSliceProjectiveAmbientChartIsoSpec.inv := inferInstance
    have hc : IsPreimmersion fixedSliceProjectiveAmbientChart.ι := inferInstance
    exact @IsPreimmersion.comp _ _ _ _ _ hq
      (@IsPreimmersion.comp _ _ _ _ _ hi hc)
  apply IsClosedImmersion.of_isPreimmersion
  rw [fixedSliceProjectiveSchemeι_range]
  exact fixedSliceProjectiveZeroLocus_isClosed

end
end Biunimodular.F11
