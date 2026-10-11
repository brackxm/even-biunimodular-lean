/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletionOriginalPrefix
import Biunimodular.F11.HomogeneousCompletion5Colon

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

theorem homogeneousCompletion5_previous_original :
    homogeneousCompletion5PreviousIdeal =
      Ideal.ofList ((homogeneousRegularOriginals.take 4).map homogeneousSparsePolynomial) := by
  have hs : (List.ofFn (fun i : Fin 4 => homogeneousCompletion5Original i.castSucc)) =
      (homogeneousRegularOriginals.take 4).map
        (fun p => (⟨1, by decide, p⟩ : RationalSparsePolynomial)) := by native_decide
  have heq := congrArg (List.map rationalSparsePolynomial) hs
  simp only [List.map_ofFn, List.map_map, Function.comp_def,
    rationalSparsePolynomial_integer] at heq
  rw [← heq, ideal_ofList_ofFn]
  rfl

theorem homogeneousCompletion5_last_original :
    homogeneousCompletion5OriginalPoly (Fin.last 4) = homogeneousSparsePolynomial homogeneousRegularOriginal5 := by
  change rationalSparsePolynomial ⟨1, by decide, homogeneousRegularOriginal5⟩ = _
  exact rationalSparsePolynomial_integer _

theorem homogeneousCompletion5_original_colon (x : MvPolynomial (Fin 6) ℂ)
    (hx : homogeneousSparsePolynomial homogeneousRegularOriginal5 * x ∈
      Ideal.ofList ((homogeneousRegularOriginals.take 4).map homogeneousSparsePolynomial)) :
    x ∈ Ideal.ofList ((homogeneousRegularOriginals.take 4).map homogeneousSparsePolynomial) := by
  rw [← homogeneousCompletion5_previous_original] at hx ⊢
  apply homogeneousCompletion5_colon x
  rwa [homogeneousCompletion5_last_original]

end
end Biunimodular.F11
