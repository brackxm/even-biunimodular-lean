/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.CramerBound4
public import Biunimodular.F11.TailErrorBound

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

private def m4 (A B C D E F : ℝ) := tailMatrix A B C D E F
private def r4 (A B C D E F : ℝ) := tailRhs A B C D E F

/-- Explicit determinant of the center tail matrix. -/
def tailDetR (A B C D E F : ℝ) : ℝ :=
  let M := tailMatrix A B C D E F
  det4r
    (M 0 0) (M 0 1) (M 0 2) (M 0 3)
    (M 1 0) (M 1 1) (M 1 2) (M 1 3)
    (M 2 0) (M 2 1) (M 2 2) (M 2 3)
    (M 3 0) (M 3 1) (M 3 2) (M 3 3)

/-- Center Cramer numerator for `g`. -/
def tailCramerG (A B C D E F : ℝ) : ℝ :=
  let M := tailMatrix A B C D E F; let R := tailRhs A B C D E F
  cramer0r (R 0) (R 1) (R 2) (R 3)
    (M 0 1) (M 0 2) (M 0 3)
    (M 1 1) (M 1 2) (M 1 3)
    (M 2 1) (M 2 2) (M 2 3)
    (M 3 1) (M 3 2) (M 3 3)

/-- Center Cramer numerator for `h`. -/
def tailCramerH (A B C D E F : ℝ) : ℝ :=
  let M := tailMatrix A B C D E F; let R := tailRhs A B C D E F
  cramer1r (R 0) (R 1) (R 2) (R 3)
    (M 0 0) (M 0 2) (M 0 3)
    (M 1 0) (M 1 2) (M 1 3)
    (M 2 0) (M 2 2) (M 2 3)
    (M 3 0) (M 3 2) (M 3 3)

/-- Center Cramer numerator for `j`. -/
def tailCramerJ (A B C D E F : ℝ) : ℝ :=
  let M := tailMatrix A B C D E F; let R := tailRhs A B C D E F
  cramer2r (R 0) (R 1) (R 2) (R 3)
    (M 0 0) (M 0 1) (M 0 3)
    (M 1 0) (M 1 1) (M 1 3)
    (M 2 0) (M 2 1) (M 2 3)
    (M 3 0) (M 3 1) (M 3 3)

/-- Center Cramer numerator for `k`. -/
def tailCramerK (A B C D E F : ℝ) : ℝ :=
  let M := tailMatrix A B C D E F; let R := tailRhs A B C D E F
  cramer3r (R 0) (R 1) (R 2) (R 3)
    (M 0 0) (M 0 1) (M 0 2)
    (M 1 0) (M 1 1) (M 1 2)
    (M 2 0) (M 2 1) (M 2 2)
    (M 3 0) (M 3 1) (M 3 2)

lemma tailMatrix_entries_le_two
    {A B C D E F : ℝ}
    (hU : unit6 A B C D E F) :
    ∀ i j : Fin 4, |tailMatrix A B C D E F i j| ≤ 2 := by
  rcases hU with ⟨hA,hB,hC,hD,hE,hF⟩
  have hA' := abs_le.mp hA; have hB' := abs_le.mp hB
  have hC' := abs_le.mp hC; have hD' := abs_le.mp hD
  have hE' := abs_le.mp hE; have hF' := abs_le.mp hF
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [tailMatrix] <;>
    rw [abs_le] <;>
    constructor <;> linarith

private lemma center_scalar_equations
    {a b c d e f A B C D E F g h j k : ℝ}
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) = tailRhs a b c d e f) :
    let M := tailMatrix A B C D E F
    let R := tailRhs A B C D E F
    let Y := centerTailError a b c d e f A B C D E F g h j k
    (M 0 0*g + M 0 1*h + M 0 2*j + M 0 3*k = R 0 + Y 0) ∧
    (M 1 0*g + M 1 1*h + M 1 2*j + M 1 3*k = R 1 + Y 1) ∧
    (M 2 0*g + M 2 1*h + M 2 2*j + M 2 3*k = R 2 + Y 2) ∧
    (M 3 0*g + M 3 1*h + M 3 2*j + M 3 3*k = R 3 + Y 3) := by
  have hc := center_tail_equation (A := A) (B := B) (C := C)
    (D := D) (E := E) (F := F) hsol
  exact ⟨by
      simpa [Matrix.mulVec, dotProduct, tailVec, Fin.sum_univ_four] using congrFun hc 0,
    by simpa [Matrix.mulVec, dotProduct, tailVec, Fin.sum_univ_four] using congrFun hc 1,
    by simpa [Matrix.mulVec, dotProduct, tailVec, Fin.sum_univ_four] using congrFun hc 2,
    by simpa [Matrix.mulVec, dotProduct, tailVec, Fin.sum_univ_four] using congrFun hc 3⟩

lemma tail_cramer_G_error_identity
    {a b c d e f A B C D E F g h j k : ℝ}
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) = tailRhs a b c d e f) :
    let Y := centerTailError a b c d e f A B C D E F g h j k
    tailDetR A B C D E F * g - tailCramerG A B C D E F =
      let M := tailMatrix A B C D E F
      cramer0r (Y 0) (Y 1) (Y 2) (Y 3)
        (M 0 1) (M 0 2) (M 0 3)
        (M 1 1) (M 1 2) (M 1 3)
        (M 2 1) (M 2 2) (M 2 3)
        (M 3 1) (M 3 2) (M 3 3) := by
  dsimp
  rcases center_scalar_equations (A := A) (B := B) (C := C)
    (D := D) (E := E) (F := F) hsol with ⟨h0,h1,h2,h3⟩
  have hc := cramer0_identity h0 h1 h2 h3
  simp only [tailDetR, tailCramerG] at hc ⊢
  rw [hc]
  simp only [cramer0r]
  ring

lemma tail_cramer_H_error_identity
    {a b c d e f A B C D E F g h j k : ℝ}
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) = tailRhs a b c d e f) :
    let Y := centerTailError a b c d e f A B C D E F g h j k
    tailDetR A B C D E F * h - tailCramerH A B C D E F =
      let M := tailMatrix A B C D E F
      cramer1r (Y 0) (Y 1) (Y 2) (Y 3)
        (M 0 0) (M 0 2) (M 0 3)
        (M 1 0) (M 1 2) (M 1 3)
        (M 2 0) (M 2 2) (M 2 3)
        (M 3 0) (M 3 2) (M 3 3) := by
  dsimp
  rcases center_scalar_equations (A := A) (B := B) (C := C)
    (D := D) (E := E) (F := F) hsol with ⟨h0,h1,h2,h3⟩
  have hc := cramer1_identity h0 h1 h2 h3
  simp only [tailDetR, tailCramerH] at hc ⊢
  rw [hc]
  simp only [cramer1r]
  ring

lemma tail_cramer_J_error_identity
    {a b c d e f A B C D E F g h j k : ℝ}
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) = tailRhs a b c d e f) :
    let Y := centerTailError a b c d e f A B C D E F g h j k
    tailDetR A B C D E F * j - tailCramerJ A B C D E F =
      let M := tailMatrix A B C D E F
      cramer2r (Y 0) (Y 1) (Y 2) (Y 3)
        (M 0 0) (M 0 1) (M 0 3)
        (M 1 0) (M 1 1) (M 1 3)
        (M 2 0) (M 2 1) (M 2 3)
        (M 3 0) (M 3 1) (M 3 3) := by
  dsimp
  rcases center_scalar_equations (A := A) (B := B) (C := C)
    (D := D) (E := E) (F := F) hsol with ⟨h0,h1,h2,h3⟩
  have hc := cramer2_identity h0 h1 h2 h3
  simp only [tailDetR, tailCramerJ] at hc ⊢
  rw [hc]
  simp only [cramer2r]
  ring

lemma tail_cramer_K_error_identity
    {a b c d e f A B C D E F g h j k : ℝ}
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) = tailRhs a b c d e f) :
    let Y := centerTailError a b c d e f A B C D E F g h j k
    tailDetR A B C D E F * k - tailCramerK A B C D E F =
      let M := tailMatrix A B C D E F
      cramer3r (Y 0) (Y 1) (Y 2) (Y 3)
        (M 0 0) (M 0 1) (M 0 2)
        (M 1 0) (M 1 1) (M 1 2)
        (M 2 0) (M 2 1) (M 2 2)
        (M 3 0) (M 3 1) (M 3 2) := by
  dsimp
  rcases center_scalar_equations (A := A) (B := B) (C := C)
    (D := D) (E := E) (F := F) hsol with ⟨h0,h1,h2,h3⟩
  have hc := cramer3_identity h0 h1 h2 h3
  simp only [tailDetR, tailCramerK] at hc ⊢
  rw [hc]
  simp only [cramer3r]
  ring

/-- Uniform cross-multiplied perturbation estimate for all four reconstructed tail coordinates. -/
theorem tail_cramer_error_le
    {δ a b c d e f A B C D E F g h j k : ℝ}
    (hδ : 0 ≤ δ)
    (hclose : close6 δ a b c d e f A B C D E F)
    (hu : unit6 a b c d e f)
    (hU : unit6 A B C D E F)
    (hg : |g| ≤ 1) (hh : |h| ≤ 1) (hj : |j| ≤ 1) (hk : |k| ≤ 1)
    (hsol : (tailMatrix a b c d e f).mulVec (tailVec g h j k) = tailRhs a b c d e f) :
    |tailDetR A B C D E F * g - tailCramerG A B C D E F| ≤ 192*(22*δ) ∧
    |tailDetR A B C D E F * h - tailCramerH A B C D E F| ≤ 192*(22*δ) ∧
    |tailDetR A B C D E F * j - tailCramerJ A B C D E F| ≤ 192*(22*δ) ∧
    |tailDetR A B C D E F * k - tailCramerK A B C D E F| ≤ 192*(22*δ) := by
  let Y := centerTailError a b c d e f A B C D E F g h j k
  have hY : ∀ i : Fin 4, |Y i| ≤ 22*δ := centerTailError_le_twentyTwo_delta hδ hclose hu hU hg hh hj hk
  have hM : ∀ i j : Fin 4, |tailMatrix A B C D E F i j| ≤ 2 := tailMatrix_entries_le_two hU
  have hnonneg : 0 ≤ 22*δ := mul_nonneg (by norm_num) hδ
  have gId := tail_cramer_G_error_identity (A := A) (B := B) (C := C)
    (D := D) (E := E) (F := F) hsol
  have hId := tail_cramer_H_error_identity (A := A) (B := B) (C := C)
    (D := D) (E := E) (F := F) hsol
  have jId := tail_cramer_J_error_identity (A := A) (B := B) (C := C)
    (D := D) (E := E) (F := F) hsol
  have kId := tail_cramer_K_error_identity (A := A) (B := B) (C := C)
    (D := D) (E := E) (F := F) hsol
  have gBd := abs_cramer0r_le_192 hnonneg (hY 0) (hY 1) (hY 2) (hY 3)
    (hM 0 1) (hM 0 2) (hM 0 3) (hM 1 1) (hM 1 2) (hM 1 3)
    (hM 2 1) (hM 2 2) (hM 2 3) (hM 3 1) (hM 3 2) (hM 3 3)
  have hBd := abs_cramer1r_le_192 hnonneg (hY 0) (hY 1) (hY 2) (hY 3)
    (hM 0 0) (hM 0 2) (hM 0 3) (hM 1 0) (hM 1 2) (hM 1 3)
    (hM 2 0) (hM 2 2) (hM 2 3) (hM 3 0) (hM 3 2) (hM 3 3)
  have jBd := abs_cramer2r_le_192 hnonneg (hY 0) (hY 1) (hY 2) (hY 3)
    (hM 0 0) (hM 0 1) (hM 0 3) (hM 1 0) (hM 1 1) (hM 1 3)
    (hM 2 0) (hM 2 1) (hM 2 3) (hM 3 0) (hM 3 1) (hM 3 3)
  have kBd := abs_cramer3r_le_192 hnonneg (hY 0) (hY 1) (hY 2) (hY 3)
    (hM 0 0) (hM 0 1) (hM 0 2) (hM 1 0) (hM 1 1) (hM 1 2)
    (hM 2 0) (hM 2 1) (hM 2 2) (hM 3 0) (hM 3 1) (hM 3 2)
  dsimp at gId hId jId kId
  rw [gId, hId, jId, kId]
  exact ⟨gBd, hBd, jBd, kBd⟩

end

end Biunimodular.F11
