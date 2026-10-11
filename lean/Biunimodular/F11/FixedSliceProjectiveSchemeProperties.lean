/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceProjectiveScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Properties

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open AlgebraicGeometry

/-- The structure map of the actual closed projective fixed-slice scheme. -/
def fixedSliceProjectiveSchemeToComplex : fixedSliceProjectiveScheme ⟶ Spec (.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ FixedSliceProjectiveChartAlgebra))

instance fixedSliceProjectiveSchemeToComplex_finite : IsFinite fixedSliceProjectiveSchemeToComplex := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℂ FixedSliceProjectiveChartAlgebra)))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

instance fixedSliceProjectiveSchemeToComplex_etale : Etale fixedSliceProjectiveSchemeToComplex := by
  change Etale (Spec.map (CommRingCat.ofHom (algebraMap ℂ FixedSliceProjectiveChartAlgebra)))
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr inferInstance

instance fixedSliceProjectiveScheme_reduced : AlgebraicGeometry.IsReduced fixedSliceProjectiveScheme := by
  change AlgebraicGeometry.IsReduced (Spec (.of FixedSliceProjectiveChartAlgebra))
  infer_instance

end
end Biunimodular.F11
