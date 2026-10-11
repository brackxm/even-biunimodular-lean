/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.IntegerCoefficientPolynomialMap
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Decide

set_option autoImplicit false

namespace Biunimodular.F11

/-! Exact seven-variable integer certificate arithmetic for inverse RUR identities. -/

structure RurInverseExponent7 where
  z1 : ℕ
  z2 : ℕ
  z3 : ℕ
  z4 : ℕ
  w : ℕ
  z5 : ℕ
  x : ℕ
  deriving DecidableEq, Repr

structure RurInverseTerm7 where
  coefficient : ℤ
  exponent : RurInverseExponent7
  deriving DecidableEq, Repr

def rurInverseSparseExponentMul
    (a b : RurInverseExponent7) : RurInverseExponent7 :=
  ⟨a.z1 + b.z1, a.z2 + b.z2, a.z3 + b.z3,
    a.z4 + b.z4, a.w + b.w, a.z5 + b.z5, a.x + b.x⟩

def rurInverseSparseTermMul (a b : RurInverseTerm7) : RurInverseTerm7 :=
  ⟨a.coefficient * b.coefficient,
    rurInverseSparseExponentMul a.exponent b.exponent⟩

def rurInverseSparseExponentLT
    (a b : RurInverseExponent7) : Bool :=
  if a.z1 != b.z1 then a.z1 < b.z1
  else if a.z2 != b.z2 then a.z2 < b.z2
  else if a.z3 != b.z3 then a.z3 < b.z3
  else if a.z4 != b.z4 then a.z4 < b.z4
  else if a.w != b.w then a.w < b.w
  else if a.z5 != b.z5 then a.z5 < b.z5
  else a.x < b.x

def rurInverseSparseExponentLE
    (a b : RurInverseExponent7) : Bool :=
  if a = b then true else rurInverseSparseExponentLT a b

def rurInverseSparseInsert (term : RurInverseTerm7) :
    List RurInverseTerm7 → List RurInverseTerm7
  | [] => if term.coefficient = 0 then [] else [term]
  | head :: tail =>
      if term.exponent = head.exponent then
        let coefficient := term.coefficient + head.coefficient
        if coefficient = 0 then tail
        else ⟨coefficient, head.exponent⟩ :: tail
      else if rurInverseSparseExponentLT term.exponent head.exponent then
        term :: head :: tail
      else
        head :: rurInverseSparseInsert term tail

private def rurInverseSparseNormalizeSorted :
    List RurInverseTerm7 → List RurInverseTerm7
  | [] => []
  | term :: tail =>
      rurInverseSparseInsert term (rurInverseSparseNormalizeSorted tail)

def rurInverseSparseNormalize
    (terms : List RurInverseTerm7) : List RurInverseTerm7 :=
  rurInverseSparseNormalizeSorted
    (terms.mergeSort fun a b =>
      rurInverseSparseExponentLE a.exponent b.exponent)

def rurInverseSparseAdd
    (a b : List RurInverseTerm7) : List RurInverseTerm7 :=
  rurInverseSparseNormalize (a ++ b)

def rurInverseSparseMul
    (a b : List RurInverseTerm7) : List RurInverseTerm7 :=
  rurInverseSparseNormalize
    (a.flatMap fun termA => b.map fun termB =>
      rurInverseSparseTermMul termA termB)

variable {R : Type*} [CommRing R]


def rurInverseSparseTermEval (term : RurInverseTerm7)
    (z1 z2 z3 z4 w z5 x : R) : R :=
  (term.coefficient : R) * z1 ^ term.exponent.z1 *
    z2 ^ term.exponent.z2 * z3 ^ term.exponent.z3 *
    z4 ^ term.exponent.z4 * w ^ term.exponent.w *
    z5 ^ term.exponent.z5 * x ^ term.exponent.x

def rurInverseSparseEval (terms : List RurInverseTerm7)
    (z1 z2 z3 z4 w z5 x : R) : R :=
  (terms.map fun term =>
    rurInverseSparseTermEval term z1 z2 z3 z4 w z5 x).sum

@[simp] private theorem rurInverseSparseEval_nil (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval [] z1 z2 z3 z4 w z5 x = 0 := rfl

private theorem rurInverseSparseEval_cons (term : RurInverseTerm7)
    (terms : List RurInverseTerm7) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (term :: terms) z1 z2 z3 z4 w z5 x =
      rurInverseSparseTermEval term z1 z2 z3 z4 w z5 x +
        rurInverseSparseEval terms z1 z2 z3 z4 w z5 x := rfl

private theorem rurInverseSparseTermEval_mul (a b : RurInverseTerm7)
    (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseTermEval (rurInverseSparseTermMul a b) z1 z2 z3 z4 w z5 x =
      rurInverseSparseTermEval a z1 z2 z3 z4 w z5 x *
        rurInverseSparseTermEval b z1 z2 z3 z4 w z5 x := by
  simp only [rurInverseSparseTermEval, rurInverseSparseTermMul,
    rurInverseSparseExponentMul, Int.cast_mul, pow_add]
  ring

private theorem rurInverseSparseEval_insert (term : RurInverseTerm7)
    (terms : List RurInverseTerm7) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (rurInverseSparseInsert term terms) z1 z2 z3 z4 w z5 x =
      rurInverseSparseTermEval term z1 z2 z3 z4 w z5 x +
        rurInverseSparseEval terms z1 z2 z3 z4 w z5 x := by
  induction terms with
  | nil =>
      by_cases hzero : term.coefficient = 0
      · simp [rurInverseSparseInsert,
          rurInverseSparseTermEval, hzero]
      · simp [rurInverseSparseInsert, rurInverseSparseEval_cons, hzero]
  | cons head tail ih =>
      by_cases hexponent : term.exponent = head.exponent
      · by_cases hzero : term.coefficient + head.coefficient = 0
        · have hcast :
              ((term.coefficient : R) + (head.coefficient : R)) = 0 := by
            simpa only [Int.cast_add, Int.cast_zero] using
              congrArg (fun c : ℤ => (c : R)) hzero
          rw [rurInverseSparseInsert, ite_eq_left hexponent, ite_eq_left hzero,
            rurInverseSparseEval_cons]
          simp only [rurInverseSparseTermEval]
          rw [hexponent]
          linear_combination
            -(z1 ^ head.exponent.z1 * z2 ^ head.exponent.z2 *
              z3 ^ head.exponent.z3 * z4 ^ head.exponent.z4 *
              w ^ head.exponent.w * z5 ^ head.exponent.z5 * x ^ head.exponent.x) * hcast
        · rw [rurInverseSparseInsert, ite_eq_left hexponent, ite_eq_right hzero,
            rurInverseSparseEval_cons, rurInverseSparseEval_cons]
          simp only [rurInverseSparseTermEval, Int.cast_add]
          rw [hexponent]
          ring
      · by_cases hlt : rurInverseSparseExponentLT term.exponent head.exponent
        · rw [rurInverseSparseInsert, ite_eq_right hexponent, ite_eq_left hlt,
            rurInverseSparseEval_cons, rurInverseSparseEval_cons]
        · rw [rurInverseSparseInsert, ite_eq_right hexponent, ite_eq_right hlt,
            rurInverseSparseEval_cons, rurInverseSparseEval_cons]
          rw [ih]
          ring

private theorem rurInverseSparseEval_normalizeSorted
    (terms : List RurInverseTerm7)
    (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (rurInverseSparseNormalizeSorted terms)
        z1 z2 z3 z4 w z5 x =
      rurInverseSparseEval terms z1 z2 z3 z4 w z5 x := by
  induction terms with
  | nil => rfl
  | cons term tail ih =>
      rw [rurInverseSparseNormalizeSorted, rurInverseSparseEval_insert, ih]
      rfl

private theorem rurInverseSparseEval_mergeSort
    (terms : List RurInverseTerm7) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval
        (terms.mergeSort fun a b =>
          rurInverseSparseExponentLE a.exponent b.exponent)
        z1 z2 z3 z4 w z5 x =
      rurInverseSparseEval terms z1 z2 z3 z4 w z5 x := by
  exact ((List.mergeSort_perm terms fun a b =>
    rurInverseSparseExponentLE a.exponent b.exponent).map fun term =>
      rurInverseSparseTermEval term z1 z2 z3 z4 w z5 x).sum_eq

theorem rurInverseSparseEval_normalize (terms : List RurInverseTerm7)
    (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (rurInverseSparseNormalize terms) z1 z2 z3 z4 w z5 x =
      rurInverseSparseEval terms z1 z2 z3 z4 w z5 x := by
  rw [rurInverseSparseNormalize, rurInverseSparseEval_normalizeSorted,
    rurInverseSparseEval_mergeSort]

private theorem rurInverseSparseEval_append
    (a b : List RurInverseTerm7) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (a ++ b) z1 z2 z3 z4 w z5 x =
      rurInverseSparseEval a z1 z2 z3 z4 w z5 x +
        rurInverseSparseEval b z1 z2 z3 z4 w z5 x := by
  simp [rurInverseSparseEval, List.map_append, List.sum_append]

theorem rurInverseSparseEval_add
    (a b : List RurInverseTerm7) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (rurInverseSparseAdd a b) z1 z2 z3 z4 w z5 x =
      rurInverseSparseEval a z1 z2 z3 z4 w z5 x +
        rurInverseSparseEval b z1 z2 z3 z4 w z5 x := by
  rw [rurInverseSparseAdd, rurInverseSparseEval_normalize,
    rurInverseSparseEval_append]

private theorem rurInverseSparseEval_map_mul (term : RurInverseTerm7)
    (terms : List RurInverseTerm7) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (terms.map (rurInverseSparseTermMul term))
        z1 z2 z3 z4 w z5 x =
      rurInverseSparseTermEval term z1 z2 z3 z4 w z5 x *
        rurInverseSparseEval terms z1 z2 z3 z4 w z5 x := by
  induction terms with
  | nil => simp
  | cons head tail ih =>
      rw [List.map_cons, rurInverseSparseEval_cons, rurInverseSparseEval_cons]
      rw [rurInverseSparseTermEval_mul, ih]
      ring

private theorem rurInverseSparseEval_flatMap_mul
    (a b : List RurInverseTerm7) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval
        (a.flatMap fun termA => b.map (rurInverseSparseTermMul termA))
        z1 z2 z3 z4 w z5 x =
      rurInverseSparseEval a z1 z2 z3 z4 w z5 x *
        rurInverseSparseEval b z1 z2 z3 z4 w z5 x := by
  induction a with
  | nil => simp
  | cons head tail ih =>
      rw [List.flatMap_cons, rurInverseSparseEval_append,
        rurInverseSparseEval_map_mul, ih]
      rw [rurInverseSparseEval_cons]
      ring

theorem rurInverseSparseEval_mul
    (a b : List RurInverseTerm7) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (rurInverseSparseMul a b) z1 z2 z3 z4 w z5 x =
      rurInverseSparseEval a z1 z2 z3 z4 w z5 x *
        rurInverseSparseEval b z1 z2 z3 z4 w z5 x := by
  rw [rurInverseSparseMul, rurInverseSparseEval_normalize,
    rurInverseSparseEval_flatMap_mul]


def rurInverseSparseScale (c : ℤ) (p : List RurInverseTerm7) : List RurInverseTerm7 :=
  p.map fun t => ⟨c * t.coefficient, t.exponent⟩

theorem rurInverseSparseEval_scale (c : ℤ) (p : List RurInverseTerm7)
    (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (rurInverseSparseScale c p) z1 z2 z3 z4 w z5 x =
      (c : R) * rurInverseSparseEval p z1 z2 z3 z4 w z5 x := by
  induction p with
  | nil => simp [rurInverseSparseScale, rurInverseSparseEval]
  | cons t ts ih =>
    simp only [rurInverseSparseScale, List.map_cons, rurInverseSparseEval_cons] at *
    rw [ih]
    simp only [rurInverseSparseTermEval, Int.cast_mul]
    ring

def rurInverseSparseOfXAux : List ℤ → ℕ → List RurInverseTerm7
  | [], _ => []
  | c :: cs, e =>
    if c = 0 then rurInverseSparseOfXAux cs (e + 1)
    else ⟨c, ⟨0, 0, 0, 0, 0, 0, e⟩⟩ :: rurInverseSparseOfXAux cs (e + 1)

def rurInverseSparseOfX (cs : List ℤ) : List RurInverseTerm7 := rurInverseSparseOfXAux cs 0

theorem rurInverseSparseEval_ofXAux (cs : List ℤ) (e : ℕ)
    (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (rurInverseSparseOfXAux cs e) z1 z2 z3 z4 w z5 x =
      x ^ e * integerCoefficientEval x cs := by
  induction cs generalizing e with
  | nil => simp [rurInverseSparseOfXAux, integerCoefficientEval]
  | cons c cs ih =>
    by_cases hc : c = 0
    · rw [rurInverseSparseOfXAux, ite_eq_left hc, ih]
      simp only [integerCoefficientEval, hc, Int.cast_zero, zero_add, pow_succ]
      ring
    · rw [rurInverseSparseOfXAux, ite_eq_right hc, rurInverseSparseEval_cons, ih]
      simp only [rurInverseSparseTermEval, integerCoefficientEval, pow_zero, mul_one]
      rw [pow_succ]
      ring

theorem rurInverseSparseEval_ofX (cs : List ℤ) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (rurInverseSparseOfX cs) z1 z2 z3 z4 w z5 x =
      integerCoefficientEval x cs := by
  rw [rurInverseSparseOfX, rurInverseSparseEval_ofXAux, pow_zero, one_mul]

def rurInverseSparseSumProducts :
    List (List RurInverseTerm7 × List RurInverseTerm7) → List RurInverseTerm7
  | [] => []
  | (a, b) :: ps => rurInverseSparseAdd (rurInverseSparseMul a b) (rurInverseSparseSumProducts ps)

theorem rurInverseSparseEval_sumProducts
    (ps : List (List RurInverseTerm7 × List RurInverseTerm7)) (z1 z2 z3 z4 w z5 x : R) :
    rurInverseSparseEval (rurInverseSparseSumProducts ps) z1 z2 z3 z4 w z5 x =
      (ps.map fun p => rurInverseSparseEval p.1 z1 z2 z3 z4 w z5 x *
        rurInverseSparseEval p.2 z1 z2 z3 z4 w z5 x).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [rurInverseSparseSumProducts, rurInverseSparseEval_add, rurInverseSparseEval_mul, ih]
    rfl

theorem rurInverseSparseZeroCheck_sound
    (ps : List (List RurInverseTerm7 × List RurInverseTerm7))
    (h : rurInverseSparseNormalize (rurInverseSparseSumProducts ps) = [])
    (z1 z2 z3 z4 w z5 x : R) :
    (ps.map fun p => rurInverseSparseEval p.1 z1 z2 z3 z4 w z5 x *
      rurInverseSparseEval p.2 z1 z2 z3 z4 w z5 x).sum = 0 := by
  have he := congrArg (fun p => rurInverseSparseEval p z1 z2 z3 z4 w z5 x) h
  rw [rurInverseSparseEval_normalize, rurInverseSparseEval_sumProducts] at he
  exact he

end Biunimodular.F11
