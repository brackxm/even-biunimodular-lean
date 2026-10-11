/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceEtaleAlgebras
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.HopkinsLevitzki

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

instance fixedSliceNormalizedAffineChart_moduleFinite :
    Module.Finite ℂ FixedSliceNormalizedAffineChartAlgebra :=
  Module.finite_of_finrank_pos (by rw [fixedSliceNormalizedAffineChart_finrank]; norm_num)

instance fixedSliceNormalizedAffineChart_nontrivial :
    Nontrivial FixedSliceNormalizedAffineChartAlgebra :=
  Module.nontrivial_of_finrank_pos (R := ℂ)
    (by rw [fixedSliceNormalizedAffineChart_finrank]; norm_num)

instance fixedSliceNormalizedAffineChart_artinian :
    IsArtinianRing FixedSliceNormalizedAffineChartAlgebra :=
  IsArtinianRing.of_finite ℂ FixedSliceNormalizedAffineChartAlgebra

/-- The actual chart is zero-dimensional in the ring-theoretic sense. -/
theorem fixedSliceNormalizedAffineChart_krullDimension :
    ringKrullDim FixedSliceNormalizedAffineChartAlgebra = 0 :=
  ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance

/-- There are no infinitesimal differentials in the actual homogeneous chart. -/
theorem fixedSliceNormalizedAffineChart_differential_eq_zero
    (x : KaehlerDifferential ℂ FixedSliceNormalizedAffineChartAlgebra) : x = 0 :=
  Subsingleton.elim _ _

end
end Biunimodular.F11
