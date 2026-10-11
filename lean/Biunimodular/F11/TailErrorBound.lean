/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.TailLinearSystemStd
public import Biunimodular.F11.TailPerturbationCore

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

/-- Error seen by the center linear system when an exact solution uses nearby
first-three phase coordinates. -/
def centerTailError
    (a b c d e f A B C D E F g h j k : ℝ) : Fin 4 → ℝ :=
  fun i =>
    (tailRhs a b c d e f i - tailRhs A B C D E F i) -
      ((tailMatrix a b c d e f - tailMatrix A B C D E F).mulVec (tailVec g h j k)) i

lemma centerTailError_le_twentyTwo_delta
    {δ a b c d e f A B C D E F g h j k : ℝ}
    (hδ : 0 ≤ δ)
    (hclose : close6 δ a b c d e f A B C D E F)
    (hu : unit6 a b c d e f)
    (hU : unit6 A B C D E F)
    (hg : |g| ≤ 1) (hh : |h| ≤ 1) (hj : |j| ≤ 1) (hk : |k| ≤ 1) :
    ∀ i : Fin 4,
      |centerTailError a b c d e f A B C D E F g h j k i| ≤ 22*δ := by
  have hR := tailRhs_diff_le_fourteen_delta hδ hclose hu hU
  have hM := tailMatrix_mulVec_diff_le_eight_delta hδ hclose hg hh hj hk
  intro i
  unfold centerTailError
  calc
    |(tailRhs a b c d e f i - tailRhs A B C D E F i) -
        ((tailMatrix a b c d e f - tailMatrix A B C D E F).mulVec (tailVec g h j k)) i|
      ≤ |tailRhs a b c d e f i - tailRhs A B C D E F i| +
        |((tailMatrix a b c d e f - tailMatrix A B C D E F).mulVec (tailVec g h j k)) i| := abs_sub _ _
    _ ≤ 14*δ + 8*δ := add_le_add (hR i) (hM i)
    _ = 22*δ := by ring

lemma center_tail_equation
    {a b c d e f A B C D E F g h j k : ℝ}
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) = tailRhs a b c d e f) :
    (tailMatrix A B C D E F).mulVec (tailVec g h j k) =
      tailRhs A B C D E F + centerTailError a b c d e f A B C D E F g h j k := by
  funext i
  have hi := congrFun hsol i
  fin_cases i <;>
    simp [centerTailError, tailMatrix, tailRhs, tailVec, Matrix.mulVec, dotProduct,
      Fin.sum_univ_four] at hi ⊢ <;>
    linear_combination hi

end

end Biunimodular.F11
