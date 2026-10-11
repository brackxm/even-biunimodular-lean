/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusMacaulaySparseMatrix
import Biunimodular.F11.IntegerCoefficientRescale
import Biunimodular.F11.IntegerCoefficientDifferential

set_option autoImplicit false
namespace Biunimodular.F11

def torusMacaulayRootScalingCheck (n : ℕ) (scale : ℤ) (degree : ℕ)
    (rows integral : Array TorusMacaulayRow) : Prop :=
  ∀ i : Fin n, List.Forall₂ (fun e f => e.1 = f.1 ∧
    integerCoefficientEqual (integerCoefficientRescale scale f.2)
      (integerCoefficientScale (scale^degree) e.2) = true)
    (rows[i.val]?.getD []) (integral[i.val]?.getD [])

instance (n : ℕ) (scale : ℤ) (degree : ℕ) (rows integral : Array TorusMacaulayRow) :
    Decidable (torusMacaulayRootScalingCheck n scale degree rows integral) := by
  unfold torusMacaulayRootScalingCheck
  infer_instance

theorem torusMacaulayRootScaling_row {R : Type*} [CommRing R]
    (scale : ℤ) (degree : ℕ) (rows integral : TorusMacaulayRow)
    (h : List.Forall₂ (fun e f => e.1 = f.1 ∧
      integerCoefficientEqual (integerCoefficientRescale scale f.2)
        (integerCoefficientScale (scale^degree) e.2) = true) rows integral)
    (a : R) (j : ℕ) :
    (integral.map fun e => if e.1 = j then integerCoefficientEval ((scale : R)*a) e.2 else 0).sum =
      (scale : R)^degree * (rows.map fun e => if e.1 = j then integerCoefficientEval a e.2 else 0).sum := by
  induction h with
  | nil => simp
  | cons h ht ih =>
    have he := integerCoefficientEval_eq_of_equal a _ _ h.2
    rw [integerCoefficientRescale_eval, integerCoefficientEval_scale, Int.cast_pow] at he
    simp only [List.map_cons, List.sum_cons, mul_add, ih]
    rw [← h.1, he]
    split_ifs <;> simp

theorem torusMacaulayRootScalingCheck_sound {R : Type*} [CommRing R]
    (n : ℕ) (scale : ℤ) (degree : ℕ) (rows integral : Array TorusMacaulayRow)
    (h : torusMacaulayRootScalingCheck n scale degree rows integral) (a : R) :
    torusMacaulaySparseMatrix n integral ((scale : R)*a) =
      (scale : R)^degree • torusMacaulaySparseMatrix n rows a := by
  ext i j
  exact torusMacaulayRootScaling_row scale degree _ _ (h i) a j.val

end Biunimodular.F11
