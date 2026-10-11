/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousRegular1Identities
import Biunimodular.F11.HomogeneousRegular2Identities
import Biunimodular.F11.HomogeneousRegular3Identities
import Biunimodular.F11.HomogeneousRegular4Identities
import Biunimodular.F11.HomogeneousRegular5Identities
import Biunimodular.F11.HomogeneousRegularOriginalBridge
import Biunimodular.F11.IdealListUnitScaling
import Biunimodular.F11.ColonFromSyzygies
import Biunimodular.F11.FixedSliceHomogeneousQuadricNonzero

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

theorem homogeneousRegularOriginals_normalized_prefix_ideal (n : ℕ) :
    Ideal.ofList (even11FixedSliceHomogeneousGenerators.take n) =
      Ideal.ofList ((homogeneousRegularOriginals.take n).map homogeneousSparsePolynomial) := by
  have hc : (Real.sqrt 11 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 11))
  have hu : IsUnit (C ((Real.sqrt 11 : ℂ)⁻¹) : MvPolynomial (Fin 6) ℂ) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hc)).map C
  obtain ⟨u, hu⟩ := hu
  rw [homogeneousRegularOriginals_normalized]
  simp only [← List.map_take]
  rw [← hu]
  exact ideal_ofList_map_unit_mul _ u

def homogeneousRegularLastComponents : Fin 5 → List FixedSliceSparsePolynomial
  | 0 => homogeneousRegular1LastComponents
  | 1 => homogeneousRegular2LastComponents
  | 2 => homogeneousRegular3LastComponents
  | 3 => homogeneousRegular4LastComponents
  | 4 => homogeneousRegular5LastComponents

/-- Every exported last syzygy component belongs to the corresponding
prefix ideal of the original normalized homogeneous equations.
Completeness of the exported syzygies is a separate obligation. -/
theorem homogeneousRegularCertificates_last_mem (j : Fin 5) :
    ∀ p ∈ homogeneousRegularLastComponents j,
      homogeneousSparsePolynomial p ∈
        Ideal.ofList (even11FixedSliceHomogeneousGenerators.take j.val) := by
  rw [homogeneousRegularOriginals_normalized_prefix_ideal,
    ← ideal_span_range_list_map]
  fin_cases j
  · exact homogeneousRegular1_last_mem
  · exact homogeneousRegular2_last_mem
  · exact homogeneousRegular3_last_mem
  · exact homogeneousRegular4_last_mem
  · exact homogeneousRegular5_last_mem

end
end Biunimodular.F11
