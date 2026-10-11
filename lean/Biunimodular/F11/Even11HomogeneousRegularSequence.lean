/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletionOriginalPrefix5
import Biunimodular.F11.PrefixColonUnitScaling
import Biunimodular.F11.FixedSliceHomogeneousRegularCriterion
import Biunimodular.F11.HomogeneousRegularOriginalBridge

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

/-- Every prefix colon condition holds for the original unnormalized five
homogeneous Fourier quadrics. -/
theorem homogeneousRegularOriginals_prefix_colon :
    ∀ i (hi : i < (homogeneousRegularOriginals.map homogeneousSparsePolynomial).length)
      (x : MvPolynomial (Fin 6) ℂ),
      (homogeneousRegularOriginals.map homogeneousSparsePolynomial)[i] * x ∈
        Ideal.ofList ((homogeneousRegularOriginals.map homogeneousSparsePolynomial).take i) →
      x ∈ Ideal.ofList ((homogeneousRegularOriginals.map homogeneousSparsePolynomial).take i) := by
  intro i hi x hx
  have hlt : i < 5 := by simpa [homogeneousRegularOriginals] using hi
  rw [← List.map_take] at hx ⊢
  interval_cases i
  · change homogeneousSparsePolynomial homogeneousRegularOriginal1 * x ∈
      Ideal.ofList ((homogeneousRegularOriginals.take 0).map homogeneousSparsePolynomial) at hx
    exact homogeneousCompletion1_original_colon x hx
  · change homogeneousSparsePolynomial homogeneousRegularOriginal2 * x ∈
      Ideal.ofList ((homogeneousRegularOriginals.take 1).map homogeneousSparsePolynomial) at hx
    exact homogeneousCompletion2_original_colon x hx
  · change homogeneousSparsePolynomial homogeneousRegularOriginal3 * x ∈
      Ideal.ofList ((homogeneousRegularOriginals.take 2).map homogeneousSparsePolynomial) at hx
    exact homogeneousCompletion3_original_colon x hx
  · change homogeneousSparsePolynomial homogeneousRegularOriginal4 * x ∈
      Ideal.ofList ((homogeneousRegularOriginals.take 3).map homogeneousSparsePolynomial) at hx
    exact homogeneousCompletion4_original_colon x hx
  · change homogeneousSparsePolynomial homogeneousRegularOriginal5 * x ∈
      Ideal.ofList ((homogeneousRegularOriginals.take 4).map homogeneousSparsePolynomial) at hx
    exact homogeneousCompletion5_original_colon x hx

/-- The the actual normalized five homogeneous Fourier quadrics form a
regular sequence in the six-variable complex polynomial ring. -/
theorem even11FixedSliceHomogeneousGenerators_regular :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin 6) ℂ)
      even11FixedSliceHomogeneousGenerators := by
  apply even11FixedSliceHomogeneousGenerators_regular_of_colon
  have hc : (Real.sqrt 11 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 11))
  have hu : IsUnit (C ((Real.sqrt 11 : ℂ)⁻¹) : MvPolynomial (Fin 6) ℂ) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero hc)).map C
  obtain ⟨u, hu⟩ := hu
  have hnormalized : even11FixedSliceHomogeneousGenerators =
      (homogeneousRegularOriginals.map homogeneousSparsePolynomial).map
        (fun p => (u : MvPolynomial (Fin 6) ℂ) * p) := by
    rw [homogeneousRegularOriginals_normalized, hu]
  rw [hnormalized]
  exact prefix_colon_map_unit_mul _ u homogeneousRegularOriginals_prefix_colon

end
end Biunimodular.F11
