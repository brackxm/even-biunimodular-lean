/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.P150RootIsolation11

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
open Polynomial
noncomputable section

def coordinateHornerEvalQ11 (t : ℚ) (cs : List ℚ) : ℚ :=
  cs.foldr (fun c v => c + t * v) 0

theorem coordinateHornerEvalQ11_real (t : ℚ) (cs : List ℚ) :
    ((polynomialOfCoefficientsQ11 cs).map (algebraMap ℚ ℝ)).eval (t : ℝ) =
      (coordinateHornerEvalQ11 t cs : ℝ) := by
  induction cs with
  | nil => simp [coordinateHornerEvalQ11]
  | cons c cs ih =>
    rw [polynomialOfCoefficientsQ11_cons]
    simp only [Polynomial.map_add, Polynomial.map_C, Polynomial.map_mul, Polynomial.map_X,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X, ih]
    simp [coordinateHornerEvalQ11]

theorem coordinateRootEndpointCertificate11 :
    ∀ i : Fin 40,
      let I := squaredKRootIntervals40[i.val]!
      0 < I.box.lo ∧ I.box.lo < I.box.hi ∧ I.box.hi < 1 ∧
        coordinateHornerEvalQ11 I.box.lo (p150FactorCoefficientsQ11 I.factor) *
          coordinateHornerEvalQ11 I.box.hi (p150FactorCoefficientsQ11 I.factor) < 0 := by
  native_decide

abbrev CoordinateFactorIntervalIndex11 (f : KFactor) :=
  {i : Fin 40 // i ∈ p150FactorRootIndices11 f}

theorem coordinateFactorIntervalIndex11_card (f : KFactor) :
    Fintype.card (CoordinateFactorIntervalIndex11 f) =
      (match f with | .g5 => 5 | .f30 => 15 | .f40 => 20) := by
  cases f <;> native_decide

theorem coordinateFactorIntervals11_separated (f : KFactor) :
    ∀ i j : CoordinateFactorIntervalIndex11 f, i ≠ j →
      (squaredKRootIntervals40[i.val.val]!).box.hi <
        (squaredKRootIntervals40[j.val.val]!).box.lo ∨
      (squaredKRootIntervals40[j.val.val]!).box.hi <
        (squaredKRootIntervals40[i.val.val]!).box.lo := by
  cases f <;> native_decide

end
end Biunimodular.F11
