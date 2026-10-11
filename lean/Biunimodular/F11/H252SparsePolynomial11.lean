/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252CircleCertificateData11

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# A computable six-variable sparse-polynomial checker

The exact H252 torus certificate is large enough that sending its fully
expanded identity to `ring` is unnecessarily expensive.  These definitions
give the generated certificate a small computable normalizer.  The generated
coefficient identity is checked by `native_decide`; the lemmas below prove
once and for all that normalization, addition, and multiplication preserve
evaluation in `ℂ`.
-/

structure H252SparseExponent6 where
  z1 : ℕ
  z2 : ℕ
  z3 : ℕ
  z4 : ℕ
  w : ℕ
  z5 : ℕ
  deriving DecidableEq, Repr

structure H252SparseTerm6 where
  coefficient : ℤ
  exponent : H252SparseExponent6
  deriving DecidableEq, Repr

def h252SparseExponentMul11
    (a b : H252SparseExponent6) : H252SparseExponent6 :=
  ⟨a.z1 + b.z1, a.z2 + b.z2, a.z3 + b.z3,
    a.z4 + b.z4, a.w + b.w, a.z5 + b.z5⟩

def h252SparseTermMul11 (a b : H252SparseTerm6) : H252SparseTerm6 :=
  ⟨a.coefficient * b.coefficient,
    h252SparseExponentMul11 a.exponent b.exponent⟩

def h252SparseExponentLT11
    (a b : H252SparseExponent6) : Bool :=
  if a.z1 != b.z1 then a.z1 < b.z1
  else if a.z2 != b.z2 then a.z2 < b.z2
  else if a.z3 != b.z3 then a.z3 < b.z3
  else if a.z4 != b.z4 then a.z4 < b.z4
  else if a.w != b.w then a.w < b.w
  else a.z5 < b.z5

def h252SparseExponentLE11
    (a b : H252SparseExponent6) : Bool :=
  if a = b then true else h252SparseExponentLT11 a b

def h252SparseInsert11 (term : H252SparseTerm6) :
    List H252SparseTerm6 → List H252SparseTerm6
  | [] => if term.coefficient = 0 then [] else [term]
  | head :: tail =>
      if term.exponent = head.exponent then
        let coefficient := term.coefficient + head.coefficient
        if coefficient = 0 then tail
        else ⟨coefficient, head.exponent⟩ :: tail
      else if h252SparseExponentLT11 term.exponent head.exponent then
        term :: head :: tail
      else
        head :: h252SparseInsert11 term tail

private def h252SparseNormalizeSorted11 :
    List H252SparseTerm6 → List H252SparseTerm6
  | [] => []
  | term :: tail =>
      h252SparseInsert11 term (h252SparseNormalizeSorted11 tail)

def h252SparseNormalize11
    (terms : List H252SparseTerm6) : List H252SparseTerm6 :=
  h252SparseNormalizeSorted11
    (terms.mergeSort fun a b =>
      h252SparseExponentLE11 a.exponent b.exponent)

def h252SparseAdd11
    (a b : List H252SparseTerm6) : List H252SparseTerm6 :=
  h252SparseNormalize11 (a ++ b)

def h252SparseMul11
    (a b : List H252SparseTerm6) : List H252SparseTerm6 :=
  h252SparseNormalize11
    (a.flatMap fun termA => b.map fun termB =>
      h252SparseTermMul11 termA termB)

def h252SparseOfZ5CoefficientsAux11 :
    List ℤ → ℕ → List H252SparseTerm6
  | [], _ => []
  | coefficient :: coefficients, exponent =>
      if coefficient = 0 then
        h252SparseOfZ5CoefficientsAux11 coefficients (exponent + 1)
      else
        ⟨coefficient, ⟨0, 0, 0, 0, 0, exponent⟩⟩ ::
          h252SparseOfZ5CoefficientsAux11 coefficients (exponent + 1)

def h252SparseOfZ5Coefficients11
    (coefficients : List ℤ) : List H252SparseTerm6 :=
  h252SparseOfZ5CoefficientsAux11 coefficients 0

noncomputable section

def h252SparseTermEval11 (term : H252SparseTerm6)
    (z1 z2 z3 z4 w z5 : ℂ) : ℂ :=
  (term.coefficient : ℂ) * z1 ^ term.exponent.z1 *
    z2 ^ term.exponent.z2 * z3 ^ term.exponent.z3 *
    z4 ^ term.exponent.z4 * w ^ term.exponent.w *
    z5 ^ term.exponent.z5

def h252SparseEval11 (terms : List H252SparseTerm6)
    (z1 z2 z3 z4 w z5 : ℂ) : ℂ :=
  (terms.map fun term =>
    h252SparseTermEval11 term z1 z2 z3 z4 w z5).sum

@[simp] private theorem h252SparseEval_nil11 (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 [] z1 z2 z3 z4 w z5 = 0 := rfl

private theorem h252SparseEval_cons11 (term : H252SparseTerm6)
    (terms : List H252SparseTerm6) (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 (term :: terms) z1 z2 z3 z4 w z5 =
      h252SparseTermEval11 term z1 z2 z3 z4 w z5 +
        h252SparseEval11 terms z1 z2 z3 z4 w z5 := rfl

private theorem h252SparseTermEval_mul11 (a b : H252SparseTerm6)
    (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseTermEval11 (h252SparseTermMul11 a b) z1 z2 z3 z4 w z5 =
      h252SparseTermEval11 a z1 z2 z3 z4 w z5 *
        h252SparseTermEval11 b z1 z2 z3 z4 w z5 := by
  simp only [h252SparseTermEval11, h252SparseTermMul11,
    h252SparseExponentMul11, Int.cast_mul, pow_add]
  ring

private theorem h252SparseEval_insert11 (term : H252SparseTerm6)
    (terms : List H252SparseTerm6) (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 (h252SparseInsert11 term terms) z1 z2 z3 z4 w z5 =
      h252SparseTermEval11 term z1 z2 z3 z4 w z5 +
        h252SparseEval11 terms z1 z2 z3 z4 w z5 := by
  induction terms with
  | nil =>
      by_cases hzero : term.coefficient = 0
      · simp [h252SparseInsert11,
          h252SparseTermEval11, hzero]
      · simp [h252SparseInsert11, h252SparseEval_cons11, hzero]
  | cons head tail ih =>
      by_cases hexponent : term.exponent = head.exponent
      · by_cases hzero : term.coefficient + head.coefficient = 0
        · have hcast :
              ((term.coefficient : ℂ) + (head.coefficient : ℂ)) = 0 := by
            exact_mod_cast hzero
          rw [h252SparseInsert11, ite_eq_left hexponent, ite_eq_left hzero,
            h252SparseEval_cons11]
          simp only [h252SparseTermEval11]
          rw [hexponent]
          linear_combination
            -(z1 ^ head.exponent.z1 * z2 ^ head.exponent.z2 *
              z3 ^ head.exponent.z3 * z4 ^ head.exponent.z4 *
              w ^ head.exponent.w * z5 ^ head.exponent.z5) * hcast
        · rw [h252SparseInsert11, ite_eq_left hexponent, ite_eq_right hzero,
            h252SparseEval_cons11, h252SparseEval_cons11]
          simp only [h252SparseTermEval11, Int.cast_add]
          rw [hexponent]
          ring
      · by_cases hlt : h252SparseExponentLT11 term.exponent head.exponent
        · rw [h252SparseInsert11, ite_eq_right hexponent, ite_eq_left hlt,
            h252SparseEval_cons11, h252SparseEval_cons11]
        · rw [h252SparseInsert11, ite_eq_right hexponent, ite_eq_right hlt,
            h252SparseEval_cons11, h252SparseEval_cons11]
          rw [ih]
          ring

private theorem h252SparseEval_normalizeSorted11
    (terms : List H252SparseTerm6)
    (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 (h252SparseNormalizeSorted11 terms)
        z1 z2 z3 z4 w z5 =
      h252SparseEval11 terms z1 z2 z3 z4 w z5 := by
  induction terms with
  | nil => rfl
  | cons term tail ih =>
      rw [h252SparseNormalizeSorted11, h252SparseEval_insert11, ih]
      rfl

private theorem h252SparseEval_mergeSort11
    (terms : List H252SparseTerm6) (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11
        (terms.mergeSort fun a b =>
          h252SparseExponentLE11 a.exponent b.exponent)
        z1 z2 z3 z4 w z5 =
      h252SparseEval11 terms z1 z2 z3 z4 w z5 := by
  exact ((List.mergeSort_perm terms fun a b =>
    h252SparseExponentLE11 a.exponent b.exponent).map fun term =>
      h252SparseTermEval11 term z1 z2 z3 z4 w z5).sum_eq

theorem h252SparseEval_normalize11 (terms : List H252SparseTerm6)
    (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 (h252SparseNormalize11 terms) z1 z2 z3 z4 w z5 =
      h252SparseEval11 terms z1 z2 z3 z4 w z5 := by
  rw [h252SparseNormalize11, h252SparseEval_normalizeSorted11,
    h252SparseEval_mergeSort11]

private theorem h252SparseEval_append11
    (a b : List H252SparseTerm6) (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 (a ++ b) z1 z2 z3 z4 w z5 =
      h252SparseEval11 a z1 z2 z3 z4 w z5 +
        h252SparseEval11 b z1 z2 z3 z4 w z5 := by
  simp [h252SparseEval11, List.map_append, List.sum_append]

theorem h252SparseEval_add11
    (a b : List H252SparseTerm6) (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 (h252SparseAdd11 a b) z1 z2 z3 z4 w z5 =
      h252SparseEval11 a z1 z2 z3 z4 w z5 +
        h252SparseEval11 b z1 z2 z3 z4 w z5 := by
  rw [h252SparseAdd11, h252SparseEval_normalize11,
    h252SparseEval_append11]

private theorem h252SparseEval_map_mul11 (term : H252SparseTerm6)
    (terms : List H252SparseTerm6) (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 (terms.map (h252SparseTermMul11 term))
        z1 z2 z3 z4 w z5 =
      h252SparseTermEval11 term z1 z2 z3 z4 w z5 *
        h252SparseEval11 terms z1 z2 z3 z4 w z5 := by
  induction terms with
  | nil => simp
  | cons head tail ih =>
      rw [List.map_cons, h252SparseEval_cons11, h252SparseEval_cons11]
      rw [h252SparseTermEval_mul11, ih]
      ring

private theorem h252SparseEval_flatMap_mul11
    (a b : List H252SparseTerm6) (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11
        (a.flatMap fun termA => b.map (h252SparseTermMul11 termA))
        z1 z2 z3 z4 w z5 =
      h252SparseEval11 a z1 z2 z3 z4 w z5 *
        h252SparseEval11 b z1 z2 z3 z4 w z5 := by
  induction a with
  | nil => simp
  | cons head tail ih =>
      rw [List.flatMap_cons, h252SparseEval_append11,
        h252SparseEval_map_mul11, ih]
      rw [h252SparseEval_cons11]
      ring

theorem h252SparseEval_mul11
    (a b : List H252SparseTerm6) (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 (h252SparseMul11 a b) z1 z2 z3 z4 w z5 =
      h252SparseEval11 a z1 z2 z3 z4 w z5 *
        h252SparseEval11 b z1 z2 z3 z4 w z5 := by
  rw [h252SparseMul11, h252SparseEval_normalize11,
    h252SparseEval_flatMap_mul11]

private theorem h252SparseEval_ofZ5CoefficientsAux11
    (coefficients : List ℤ) (exponent : ℕ)
    (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11
        (h252SparseOfZ5CoefficientsAux11 coefficients exponent)
        z1 z2 z3 z4 w z5 =
      z5 ^ exponent * h252EvalCoefficientsC coefficients z5 := by
  induction coefficients generalizing exponent with
  | nil => simp [h252SparseOfZ5CoefficientsAux11, h252EvalCoefficientsC]
  | cons coefficient coefficients ih =>
      by_cases hzero : coefficient = 0
      · rw [h252SparseOfZ5CoefficientsAux11, ite_eq_left hzero, ih,
          h252EvalCoefficientsC, hzero, Int.cast_zero, zero_add, pow_succ]
        ring
      · rw [h252SparseOfZ5CoefficientsAux11, ite_eq_right hzero,
          h252SparseEval_cons11, ih]
        simp only [h252SparseTermEval11, h252EvalCoefficientsC, pow_zero,
          mul_one]
        rw [pow_succ]
        ring

theorem h252SparseEval_ofZ5Coefficients11
    (coefficients : List ℤ) (z1 z2 z3 z4 w z5 : ℂ) :
    h252SparseEval11 (h252SparseOfZ5Coefficients11 coefficients)
        z1 z2 z3 z4 w z5 =
      h252EvalCoefficientsC coefficients z5 := by
  rw [h252SparseOfZ5Coefficients11,
    h252SparseEval_ofZ5CoefficientsAux11]
  simp

end

end Biunimodular.F11
