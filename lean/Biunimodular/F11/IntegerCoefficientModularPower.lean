/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientModular

set_option autoImplicit false
namespace Biunimodular.F11

def integerCoefficientParseText (text : String) : List ℤ :=
  (text.splitOn " ").map fun s => s.toInt?.getD 0

def integerCoefficientReduceMod (p : ℕ) (coefficients : List ℤ) : List ℤ :=
  coefficients.map fun c => c % (p : ℤ)

theorem integerCoefficientEval_reduceMod {R : Type*} [CommRing R]
    (p : ℕ) [CharP R p] (a : R) (cs : List ℤ) :
    integerCoefficientEval a (integerCoefficientReduceMod p cs) =
      integerCoefficientEval a cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [integerCoefficientReduceMod, List.map_cons, integerCoefficientEval] at ih ⊢
    rw [ih, ← CharP.intCast_eq_intCast_mod R p]

def integerCoefficientModPow (p : ℕ) (cs : List ℤ) : ℕ → List ℤ
  | 0 => [1]
  | n+1 => integerCoefficientReduceMod p
      (integerCoefficientMul (integerCoefficientModPow p cs n) cs)

theorem integerCoefficientEval_modPow {R : Type*} [CommRing R]
    (p : ℕ) [CharP R p] (a : R) (cs : List ℤ) (n : ℕ) :
    integerCoefficientEval a (integerCoefficientModPow p cs n) =
      integerCoefficientEval a cs ^ n := by
  induction n with
  | zero => simp [integerCoefficientModPow, integerCoefficientEval]
  | succ n ih =>
    rw [integerCoefficientModPow, integerCoefficientEval_reduceMod,
      integerCoefficientEval_mul, ih, pow_succ]

end Biunimodular.F11
