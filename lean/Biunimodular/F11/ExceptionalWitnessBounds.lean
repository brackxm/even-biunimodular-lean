/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ExceptionalWitnessBoundsFixed

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

abbrev Vec4Q := Fin 4 → ℚ

/-- The four rational coefficients of an exceptional left-null witness. -/
def witnessVec (w : ExceptionalWitness) : Vec4Q :=
  ![w.w0, w.w1, w.w2, w.w3]

/-- Evaluation of a witness on each column of its center matrix. -/
def witnessCenterM (w : ExceptionalWitness) : Vec4Q :=
  fun j => dotWitness w (fun i => centerTailMatrixQ w.aIdx w.cIdx w.eIdx i j)

/-- Evaluation of a witness on its center right-hand side. -/
def witnessCenterR (w : ExceptionalWitness) : ℚ :=
  dotWitness w (centerTailRhsQ w.aIdx w.cIdx w.eIdx)

/-- Rational ℓ¹ norm of a witness. -/
def witnessL1 (w : ExceptionalWitness) : ℚ :=
  ∑ i : Fin 4, |witnessVec w i|

lemma absQ_eq_abs (x : ℚ) : absQ x = |x| := by
  by_cases hx : x < 0
  · simp [absQ, hx, abs_of_neg hx]
  · simp [absQ, hx, abs_of_nonneg (le_of_not_gt hx)]

end Biunimodular.F11
