/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousRegularOriginalData
import Biunimodular.F11.FixedSliceNormalizedAffineChart

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

theorem homogeneousRegularOriginals_polynomial :
    homogeneousRegularOriginals.map homogeneousSparsePolynomial =
      fixedSliceHomogeneousGenerators even11Fourier := by
  have hf (j i : Fin 6) : even11Fourier (Pi.single i 1) j =
      (even11FourierPolyEntry j i).eval₂ (Int.castRingHom ℂ) even11Alpha :=
    (even11FourierPolyEntry_eval j i).symm
  simp only [fixedSliceHomogeneousGenerators, fixedSliceHomogeneousQuadric,
    fixedSliceFourierLinearForm, hf]
  norm_num [homogeneousRegularOriginals, homogeneousRegularOriginal1,
    homogeneousRegularOriginal2, homogeneousRegularOriginal3,
    homogeneousRegularOriginal4, homogeneousRegularOriginal5,
    homogeneousSparsePolynomial, fixedSliceAlphaEval, Fin.sum_univ_succ, Fin.succ,
    even11FourierPolyEntry, even11FoldExponent, even11CosRep,
    Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow]
  and_intros <;> ring

theorem homogeneousRegularOriginals_normalized :
    even11FixedSliceHomogeneousGenerators =
      (homogeneousRegularOriginals.map homogeneousSparsePolynomial).map
        (fun p => C ((Real.sqrt 11 : ℂ)⁻¹) * p) := by
  rw [homogeneousRegularOriginals_polynomial]
  simp only [even11FixedSliceHomogeneousGenerators, even11FourierNormalized,
    fixedSliceHomogeneousGenerators, List.map_ofFn,
    fixedSliceHomogeneousQuadric_smul]
  rfl

end
end Biunimodular.F11
