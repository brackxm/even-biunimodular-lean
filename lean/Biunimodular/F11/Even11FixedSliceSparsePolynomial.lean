/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11PrincipalMinorBridge

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# A computable sparse-polynomial checker for the fixed-slice calculation

The fixed-slice shape certificate is computed over
`ℚ(α)`, where `α = 2 cos (2π / 11)`.  Singular writes every coefficient in
the basis `1, α, …, α⁴`.  The definitions below implement that five-term
coefficient arithmetic directly over the integers, followed by a sparse
six-variable polynomial normalizer.  Consequently generated identities can
be checked by `native_decide`; the lemmas in this file prove once and for all
that the computation preserves evaluation at the concrete complex number
`even11Alpha`.
-/

/-- An integral coefficient in the basis `1, α, …, α⁴`. -/
structure FixedSliceAlphaCoeff where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ
  c3 : ℤ
  c4 : ℤ
  deriving DecidableEq, Repr

def fixedSliceAlphaZero : FixedSliceAlphaCoeff := ⟨0, 0, 0, 0, 0⟩

def fixedSliceAlphaAdd
    (a b : FixedSliceAlphaCoeff) : FixedSliceAlphaCoeff :=
  ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2,
    a.c3 + b.c3, a.c4 + b.c4⟩

def fixedSliceAlphaScale
    (n : ℤ) (a : FixedSliceAlphaCoeff) : FixedSliceAlphaCoeff :=
  ⟨n*a.c0, n*a.c1, n*a.c2, n*a.c3, n*a.c4⟩

/-- Multiplication reduced by
`α⁵ = -α⁴ + 4α³ + 3α² - 3α - 1`.

The formulas are the convolution of two degree-at-most-four representatives,
with powers five through eight reduced by the displayed relation. -/
def fixedSliceAlphaMul
    (a b : FixedSliceAlphaCoeff) : FixedSliceAlphaCoeff :=
  ⟨
    a.c0*b.c0 - a.c1*b.c4 - a.c2*b.c3 + a.c2*b.c4 -
      a.c3*b.c2 + a.c3*b.c3 - 5*a.c3*b.c4 - a.c4*b.c1 +
      a.c4*b.c2 - 5*a.c4*b.c3 + 6*a.c4*b.c4,
    a.c0*b.c1 + a.c1*b.c0 - 3*a.c1*b.c4 - 3*a.c2*b.c3 +
      2*a.c2*b.c4 - 3*a.c3*b.c2 + 2*a.c3*b.c3 - 14*a.c3*b.c4 -
      3*a.c4*b.c1 + 2*a.c4*b.c2 - 14*a.c4*b.c3 + 13*a.c4*b.c4,
    a.c0*b.c2 + a.c1*b.c1 + 3*a.c1*b.c4 + a.c2*b.c0 +
      3*a.c2*b.c3 - 6*a.c2*b.c4 + 3*a.c3*b.c2 - 6*a.c3*b.c3 +
      17*a.c3*b.c4 + 3*a.c4*b.c1 - 6*a.c4*b.c2 + 17*a.c4*b.c3 -
      32*a.c4*b.c4,
    a.c0*b.c3 + a.c1*b.c2 + 4*a.c1*b.c4 + a.c2*b.c1 +
      4*a.c2*b.c3 - a.c2*b.c4 + a.c3*b.c0 + 4*a.c3*b.c2 -
      a.c3*b.c3 + 14*a.c3*b.c4 + 4*a.c4*b.c1 - a.c4*b.c2 +
      14*a.c4*b.c3 - 7*a.c4*b.c4,
    a.c0*b.c4 + a.c1*b.c3 - a.c1*b.c4 + a.c2*b.c2 -
      a.c2*b.c3 + 5*a.c2*b.c4 + a.c3*b.c1 - a.c3*b.c2 +
      5*a.c3*b.c3 - 6*a.c3*b.c4 + a.c4*b.c0 - a.c4*b.c1 +
      5*a.c4*b.c2 - 6*a.c4*b.c3 + 20*a.c4*b.c4
  ⟩

noncomputable def fixedSliceAlphaEval
    (c : FixedSliceAlphaCoeff) : ℂ :=
  c.c0 + c.c1 * even11Alpha + c.c2 * even11Alpha ^ 2 +
    c.c3 * even11Alpha ^ 3 + c.c4 * even11Alpha ^ 4

@[simp] theorem fixedSliceAlphaEval_zero :
    fixedSliceAlphaEval fixedSliceAlphaZero = 0 := by
  simp [fixedSliceAlphaEval, fixedSliceAlphaZero]

theorem fixedSliceAlphaEval_add (a b : FixedSliceAlphaCoeff) :
    fixedSliceAlphaEval (fixedSliceAlphaAdd a b) =
      fixedSliceAlphaEval a + fixedSliceAlphaEval b := by
  simp only [fixedSliceAlphaEval, fixedSliceAlphaAdd, Int.cast_add]
  ring

theorem fixedSliceAlphaEval_scale (n : ℤ) (a : FixedSliceAlphaCoeff) :
    fixedSliceAlphaEval (fixedSliceAlphaScale n a) =
      (n : ℂ) * fixedSliceAlphaEval a := by
  simp only [fixedSliceAlphaEval, fixedSliceAlphaScale, Int.cast_mul]
  ring

theorem fixedSliceAlphaEval_mul (a b : FixedSliceAlphaCoeff) :
    fixedSliceAlphaEval (fixedSliceAlphaMul a b) =
      fixedSliceAlphaEval a * fixedSliceAlphaEval b := by
  have hmin := alpha11Minpoly_even11Alpha
  simp [alpha11Minpoly, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow] at hmin
  simp only [fixedSliceAlphaEval, fixedSliceAlphaMul, Int.cast_add,
    Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
  ring_nf at hmin ⊢
  linear_combination
    -(a.c1*b.c4 + a.c2*b.c3 + a.c3*b.c2 + a.c4*b.c1) * hmin -
    (a.c2*b.c4 + a.c3*b.c3 + a.c4*b.c2) *
      (even11Alpha - 1) * hmin +
    -(a.c3*b.c4 + a.c4*b.c3) *
      (even11Alpha^2 - even11Alpha + 5) * hmin +
    -(a.c4*b.c4) *
      (even11Alpha^3 - even11Alpha^2 + 5*even11Alpha - 6) * hmin

/-- Exponents in the affine variables `(x5,x4,x3,x2,x1,t)`. -/
structure FixedSliceSparseExponent where
  x5 : ℕ
  x4 : ℕ
  x3 : ℕ
  x2 : ℕ
  x1 : ℕ
  trace : ℕ
  deriving DecidableEq, Repr

structure FixedSliceSparseTerm where
  coefficient : FixedSliceAlphaCoeff
  exponent : FixedSliceSparseExponent
  deriving DecidableEq, Repr

abbrev FixedSliceSparsePolynomial := List FixedSliceSparseTerm

def fixedSliceSparseExponentMul
    (a b : FixedSliceSparseExponent) : FixedSliceSparseExponent :=
  ⟨a.x5 + b.x5, a.x4 + b.x4, a.x3 + b.x3,
    a.x2 + b.x2, a.x1 + b.x1, a.trace + b.trace⟩

def fixedSliceSparseTermMul
    (a b : FixedSliceSparseTerm) : FixedSliceSparseTerm :=
  ⟨fixedSliceAlphaMul a.coefficient b.coefficient,
    fixedSliceSparseExponentMul a.exponent b.exponent⟩

def fixedSliceSparseExponentLT
    (a b : FixedSliceSparseExponent) : Bool :=
  if a.x5 != b.x5 then a.x5 < b.x5
  else if a.x4 != b.x4 then a.x4 < b.x4
  else if a.x3 != b.x3 then a.x3 < b.x3
  else if a.x2 != b.x2 then a.x2 < b.x2
  else if a.x1 != b.x1 then a.x1 < b.x1
  else a.trace < b.trace

def fixedSliceSparseExponentLE
    (a b : FixedSliceSparseExponent) : Bool :=
  if a = b then true else fixedSliceSparseExponentLT a b

def fixedSliceSparseInsert (term : FixedSliceSparseTerm) :
    FixedSliceSparsePolynomial → FixedSliceSparsePolynomial
  | [] => if term.coefficient = fixedSliceAlphaZero then [] else [term]
  | head :: tail =>
      if term.exponent = head.exponent then
        let coefficient := fixedSliceAlphaAdd term.coefficient head.coefficient
        if coefficient = fixedSliceAlphaZero then tail
        else ⟨coefficient, head.exponent⟩ :: tail
      else if fixedSliceSparseExponentLT term.exponent head.exponent then
        term :: head :: tail
      else
        head :: fixedSliceSparseInsert term tail

private def fixedSliceSparseNormalizeSorted :
    FixedSliceSparsePolynomial → FixedSliceSparsePolynomial
  | [] => []
  | term :: tail =>
      fixedSliceSparseInsert term (fixedSliceSparseNormalizeSorted tail)

def fixedSliceSparseNormalize
    (terms : FixedSliceSparsePolynomial) : FixedSliceSparsePolynomial :=
  fixedSliceSparseNormalizeSorted
    (terms.mergeSort fun a b =>
      fixedSliceSparseExponentLE a.exponent b.exponent)

def fixedSliceSparseAdd
    (a b : FixedSliceSparsePolynomial) : FixedSliceSparsePolynomial :=
  fixedSliceSparseNormalize (a ++ b)

def fixedSliceSparseMul
    (a b : FixedSliceSparsePolynomial) : FixedSliceSparsePolynomial :=
  fixedSliceSparseNormalize
    (a.flatMap fun termA => b.map fun termB =>
      fixedSliceSparseTermMul termA termB)

def fixedSliceSparseScale
    (n : ℤ) (polynomial : FixedSliceSparsePolynomial) :
    FixedSliceSparsePolynomial :=
  polynomial.map fun term =>
    ⟨fixedSliceAlphaScale n term.coefficient, term.exponent⟩

def fixedSliceSparseSumProducts
    (terms : List (FixedSliceSparsePolynomial ×
      FixedSliceSparsePolynomial)) : FixedSliceSparsePolynomial :=
  match terms with
  | [] => []
  | pair :: tail => fixedSliceSparseAdd
      (fixedSliceSparseMul pair.1 pair.2)
      (fixedSliceSparseSumProducts tail)

def fixedSliceSparseLinearCombinations
    (multipliers : List (List FixedSliceSparsePolynomial))
    (generators : List FixedSliceSparsePolynomial) :
    List FixedSliceSparsePolynomial :=
  multipliers.map fun row =>
    fixedSliceSparseSumProducts (List.zip row generators)

def fixedSliceSparseSystemIdentity
    (targets : List FixedSliceSparsePolynomial)
    (multipliers : List (List FixedSliceSparsePolynomial))
    (generators : List FixedSliceSparsePolynomial) : Prop :=
  targets.map fixedSliceSparseNormalize =
    (fixedSliceSparseLinearCombinations multipliers generators).map
      fixedSliceSparseNormalize

noncomputable def fixedSliceSparseTermEval (term : FixedSliceSparseTerm)
    (x5 x4 x3 x2 x1 trace : ℂ) : ℂ :=
  fixedSliceAlphaEval term.coefficient * x5 ^ term.exponent.x5 *
    x4 ^ term.exponent.x4 * x3 ^ term.exponent.x3 *
    x2 ^ term.exponent.x2 * x1 ^ term.exponent.x1 *
    trace ^ term.exponent.trace

noncomputable def fixedSliceSparseEval
    (terms : FixedSliceSparsePolynomial)
    (x5 x4 x3 x2 x1 trace : ℂ) : ℂ :=
  (terms.map fun term =>
    fixedSliceSparseTermEval term x5 x4 x3 x2 x1 trace).sum

def fixedSliceSparseTraceOnly
    (terms : FixedSliceSparsePolynomial) : Prop :=
  ∀ term ∈ terms,
    term.exponent.x5 = 0 ∧ term.exponent.x4 = 0 ∧
      term.exponent.x3 = 0 ∧ term.exponent.x2 = 0 ∧
      term.exponent.x1 = 0

theorem fixedSliceSparseEval_traceOnly
    {terms : FixedSliceSparsePolynomial}
    (hterms : fixedSliceSparseTraceOnly terms)
    (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval terms x5 x4 x3 x2 x1 trace =
      fixedSliceSparseEval terms 0 0 0 0 0 trace := by
  induction terms with
  | nil => rfl
  | cons term tail ih =>
      change fixedSliceSparseTermEval term x5 x4 x3 x2 x1 trace +
          fixedSliceSparseEval tail x5 x4 x3 x2 x1 trace =
        fixedSliceSparseTermEval term 0 0 0 0 0 trace +
          fixedSliceSparseEval tail 0 0 0 0 0 trace
      obtain ⟨hx5, hx4, hx3, hx2, hx1⟩ :=
        hterms term (by simp)
      have htail : fixedSliceSparseTraceOnly tail := by
        intro item hitem
        exact hterms item (by simp [hitem])
      rw [ih htail]
      simp [fixedSliceSparseTermEval, hx5, hx4, hx3, hx2, hx1]

@[simp] private theorem fixedSliceSparseEval_nil
    (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval [] x5 x4 x3 x2 x1 trace = 0 := rfl

private theorem fixedSliceSparseEval_cons (term : FixedSliceSparseTerm)
    (terms : FixedSliceSparsePolynomial) (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval (term :: terms) x5 x4 x3 x2 x1 trace =
      fixedSliceSparseTermEval term x5 x4 x3 x2 x1 trace +
        fixedSliceSparseEval terms x5 x4 x3 x2 x1 trace := rfl

private theorem fixedSliceSparseTermEval_mul (a b : FixedSliceSparseTerm)
    (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseTermEval (fixedSliceSparseTermMul a b)
        x5 x4 x3 x2 x1 trace =
      fixedSliceSparseTermEval a x5 x4 x3 x2 x1 trace *
        fixedSliceSparseTermEval b x5 x4 x3 x2 x1 trace := by
  simp only [fixedSliceSparseTermEval, fixedSliceSparseTermMul,
    fixedSliceSparseExponentMul, fixedSliceAlphaEval_mul, pow_add]
  ring

private theorem fixedSliceSparseEval_insert (term : FixedSliceSparseTerm)
    (terms : FixedSliceSparsePolynomial) (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval (fixedSliceSparseInsert term terms)
        x5 x4 x3 x2 x1 trace =
      fixedSliceSparseTermEval term x5 x4 x3 x2 x1 trace +
        fixedSliceSparseEval terms x5 x4 x3 x2 x1 trace := by
  induction terms with
  | nil =>
      by_cases hzero : term.coefficient = fixedSliceAlphaZero
      · simp [fixedSliceSparseInsert, fixedSliceSparseTermEval, hzero]
      · simp [fixedSliceSparseInsert, fixedSliceSparseEval_cons, hzero]
  | cons head tail ih =>
      by_cases hexponent : term.exponent = head.exponent
      · by_cases hzero :
          fixedSliceAlphaAdd term.coefficient head.coefficient =
            fixedSliceAlphaZero
        · have hcast :
              fixedSliceAlphaEval term.coefficient +
                  fixedSliceAlphaEval head.coefficient = 0 := by
            rw [← fixedSliceAlphaEval_add, hzero,
              fixedSliceAlphaEval_zero]
          rw [fixedSliceSparseInsert, ite_eq_left hexponent, ite_eq_left hzero,
            fixedSliceSparseEval_cons]
          simp only [fixedSliceSparseTermEval]
          rw [hexponent]
          linear_combination
            -(x5 ^ head.exponent.x5 * x4 ^ head.exponent.x4 *
              x3 ^ head.exponent.x3 * x2 ^ head.exponent.x2 *
              x1 ^ head.exponent.x1 * trace ^ head.exponent.trace) * hcast
        · rw [fixedSliceSparseInsert, ite_eq_left hexponent, ite_eq_right hzero,
            fixedSliceSparseEval_cons, fixedSliceSparseEval_cons]
          simp only [fixedSliceSparseTermEval]
          rw [fixedSliceAlphaEval_add]
          rw [hexponent]
          ring
      · by_cases hlt :
          fixedSliceSparseExponentLT term.exponent head.exponent
        · rw [fixedSliceSparseInsert, ite_eq_right hexponent, ite_eq_left hlt,
            fixedSliceSparseEval_cons, fixedSliceSparseEval_cons]
        · rw [fixedSliceSparseInsert, ite_eq_right hexponent, ite_eq_right hlt,
            fixedSliceSparseEval_cons, fixedSliceSparseEval_cons, ih]
          ring

private theorem fixedSliceSparseEval_normalizeSorted
    (terms : FixedSliceSparsePolynomial) (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval (fixedSliceSparseNormalizeSorted terms)
        x5 x4 x3 x2 x1 trace =
      fixedSliceSparseEval terms x5 x4 x3 x2 x1 trace := by
  induction terms with
  | nil => rfl
  | cons term tail ih =>
      rw [fixedSliceSparseNormalizeSorted,
        fixedSliceSparseEval_insert, ih]
      rfl

private theorem fixedSliceSparseEval_mergeSort
    (terms : FixedSliceSparsePolynomial) (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval
        (terms.mergeSort fun a b =>
          fixedSliceSparseExponentLE a.exponent b.exponent)
        x5 x4 x3 x2 x1 trace =
      fixedSliceSparseEval terms x5 x4 x3 x2 x1 trace := by
  exact ((List.mergeSort_perm terms fun a b =>
    fixedSliceSparseExponentLE a.exponent b.exponent).map fun term =>
      fixedSliceSparseTermEval term x5 x4 x3 x2 x1 trace).sum_eq

theorem fixedSliceSparseEval_normalize
    (terms : FixedSliceSparsePolynomial) (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval (fixedSliceSparseNormalize terms)
        x5 x4 x3 x2 x1 trace =
      fixedSliceSparseEval terms x5 x4 x3 x2 x1 trace := by
  rw [fixedSliceSparseNormalize, fixedSliceSparseEval_normalizeSorted,
    fixedSliceSparseEval_mergeSort]

private theorem fixedSliceSparseEval_append
    (a b : FixedSliceSparsePolynomial) (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval (a ++ b) x5 x4 x3 x2 x1 trace =
      fixedSliceSparseEval a x5 x4 x3 x2 x1 trace +
        fixedSliceSparseEval b x5 x4 x3 x2 x1 trace := by
  simp [fixedSliceSparseEval, List.map_append, List.sum_append]

theorem fixedSliceSparseEval_add
    (a b : FixedSliceSparsePolynomial) (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval (fixedSliceSparseAdd a b)
        x5 x4 x3 x2 x1 trace =
      fixedSliceSparseEval a x5 x4 x3 x2 x1 trace +
        fixedSliceSparseEval b x5 x4 x3 x2 x1 trace := by
  rw [fixedSliceSparseAdd, fixedSliceSparseEval_normalize,
    fixedSliceSparseEval_append]

private theorem fixedSliceSparseEval_map_mul (term : FixedSliceSparseTerm)
    (terms : FixedSliceSparsePolynomial) (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval (terms.map (fixedSliceSparseTermMul term))
        x5 x4 x3 x2 x1 trace =
      fixedSliceSparseTermEval term x5 x4 x3 x2 x1 trace *
        fixedSliceSparseEval terms x5 x4 x3 x2 x1 trace := by
  induction terms with
  | nil => simp
  | cons head tail ih =>
      rw [List.map_cons, fixedSliceSparseEval_cons,
        fixedSliceSparseEval_cons, fixedSliceSparseTermEval_mul, ih]
      ring

private theorem fixedSliceSparseEval_flatMap_mul
    (a b : FixedSliceSparsePolynomial) (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval
        (a.flatMap fun termA => b.map (fixedSliceSparseTermMul termA))
        x5 x4 x3 x2 x1 trace =
      fixedSliceSparseEval a x5 x4 x3 x2 x1 trace *
        fixedSliceSparseEval b x5 x4 x3 x2 x1 trace := by
  induction a with
  | nil => simp
  | cons head tail ih =>
      rw [List.flatMap_cons, fixedSliceSparseEval_append,
        fixedSliceSparseEval_map_mul, ih, fixedSliceSparseEval_cons]
      ring

theorem fixedSliceSparseEval_mul
    (a b : FixedSliceSparsePolynomial) (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval (fixedSliceSparseMul a b)
        x5 x4 x3 x2 x1 trace =
      fixedSliceSparseEval a x5 x4 x3 x2 x1 trace *
        fixedSliceSparseEval b x5 x4 x3 x2 x1 trace := by
  rw [fixedSliceSparseMul, fixedSliceSparseEval_normalize,
    fixedSliceSparseEval_flatMap_mul]

theorem fixedSliceSparseEval_scale
    (n : ℤ) (polynomial : FixedSliceSparsePolynomial)
    (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval (fixedSliceSparseScale n polynomial)
        x5 x4 x3 x2 x1 trace =
      (n : ℂ) * fixedSliceSparseEval polynomial x5 x4 x3 x2 x1 trace := by
  induction polynomial with
  | nil => simp [fixedSliceSparseScale]
  | cons term tail ih =>
      rw [fixedSliceSparseScale, List.map_cons,
        fixedSliceSparseEval_cons, fixedSliceSparseEval_cons]
      change fixedSliceSparseTermEval
          ⟨fixedSliceAlphaScale n term.coefficient, term.exponent⟩
            x5 x4 x3 x2 x1 trace +
          fixedSliceSparseEval (fixedSliceSparseScale n tail)
            x5 x4 x3 x2 x1 trace = _
      rw [ih]
      simp only [fixedSliceSparseTermEval, fixedSliceAlphaEval_scale]
      ring

theorem fixedSliceSparseEval_sumProducts
    (terms : List (FixedSliceSparsePolynomial ×
      FixedSliceSparsePolynomial)) (x5 x4 x3 x2 x1 trace : ℂ) :
    fixedSliceSparseEval (fixedSliceSparseSumProducts terms)
        x5 x4 x3 x2 x1 trace =
      (terms.map fun pair =>
        fixedSliceSparseEval pair.1 x5 x4 x3 x2 x1 trace *
          fixedSliceSparseEval pair.2 x5 x4 x3 x2 x1 trace).sum := by
  induction terms with
  | nil => rfl
  | cons pair tail ih =>
      rw [fixedSliceSparseSumProducts, fixedSliceSparseEval_add,
        fixedSliceSparseEval_mul, ih]
      rfl

theorem fixedSliceSparseEval_sumProducts_eq_zero
    (terms : List (FixedSliceSparsePolynomial ×
      FixedSliceSparsePolynomial)) (x5 x4 x3 x2 x1 trace : ℂ)
    (hzero : ∀ pair ∈ terms,
      fixedSliceSparseEval pair.2 x5 x4 x3 x2 x1 trace = 0) :
    fixedSliceSparseEval (fixedSliceSparseSumProducts terms)
        x5 x4 x3 x2 x1 trace = 0 := by
  rw [fixedSliceSparseEval_sumProducts]
  apply List.sum_eq_zero
  intro value hvalue
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hvalue
  rw [hzero pair hpair, mul_zero]

theorem fixedSliceSparseLinearCombination_eval_eq_zero
    (row generators : List FixedSliceSparsePolynomial)
    (x5 x4 x3 x2 x1 trace : ℂ)
    (hzero : ∀ generator ∈ generators,
      fixedSliceSparseEval generator x5 x4 x3 x2 x1 trace = 0) :
    fixedSliceSparseEval
        (fixedSliceSparseSumProducts (List.zip row generators))
        x5 x4 x3 x2 x1 trace = 0 := by
  apply fixedSliceSparseEval_sumProducts_eq_zero
  intro pair hpair
  exact hzero pair.2 (List.of_mem_zip hpair).2

/-- Kernel-checked sparse identities propagate simultaneous vanishing from
the source system to the target system. -/
theorem fixedSliceSparseSystemIdentity.vanish
    {targets : List FixedSliceSparsePolynomial}
    {multipliers : List (List FixedSliceSparsePolynomial)}
    {generators : List FixedSliceSparsePolynomial}
    (hidentity : fixedSliceSparseSystemIdentity
      targets multipliers generators)
    (x5 x4 x3 x2 x1 trace : ℂ)
    (hzero : ∀ generator ∈ generators,
      fixedSliceSparseEval generator x5 x4 x3 x2 x1 trace = 0) :
    ∀ target ∈ targets,
      fixedSliceSparseEval target x5 x4 x3 x2 x1 trace = 0 := by
  intro target htarget
  have hmember : fixedSliceSparseNormalize target ∈
      targets.map fixedSliceSparseNormalize :=
    List.mem_map.mpr ⟨target, htarget, rfl⟩
  rw [hidentity] at hmember
  obtain ⟨combination, hcombination, heq⟩ := List.mem_map.mp hmember
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp hcombination
  have heval := congrArg
    (fun polynomial =>
      fixedSliceSparseEval polynomial x5 x4 x3 x2 x1 trace) heq
  rw [fixedSliceSparseEval_normalize,
    fixedSliceSparseEval_normalize] at heval
  rw [← heval]
  exact fixedSliceSparseLinearCombination_eval_eq_zero
    row generators x5 x4 x3 x2 x1 trace hzero

def fixedSliceSparseScaledSystemIdentity
    (targets : List (ℤ × FixedSliceSparsePolynomial))
    (multipliers : List (List FixedSliceSparsePolynomial))
    (generators : List FixedSliceSparsePolynomial) : Prop :=
  fixedSliceSparseSystemIdentity
    (targets.map fun target =>
      fixedSliceSparseScale target.1 target.2)
    multipliers generators

/-- A checked identity with a nonzero integer scale proves that every
unscaled target vanishes. -/
theorem fixedSliceSparseScaledSystemIdentity.vanish
    {targets : List (ℤ × FixedSliceSparsePolynomial)}
    {multipliers : List (List FixedSliceSparsePolynomial)}
    {generators : List FixedSliceSparsePolynomial}
    (hidentity : fixedSliceSparseScaledSystemIdentity
      targets multipliers generators)
    (x5 x4 x3 x2 x1 trace : ℂ)
    (hscale : ∀ target ∈ targets, target.1 ≠ 0)
    (hzero : ∀ generator ∈ generators,
      fixedSliceSparseEval generator x5 x4 x3 x2 x1 trace = 0) :
    ∀ target ∈ targets,
      fixedSliceSparseEval target.2 x5 x4 x3 x2 x1 trace = 0 := by
  have hscaled := fixedSliceSparseSystemIdentity.vanish hidentity
    x5 x4 x3 x2 x1 trace hzero
  intro target htarget
  have hz := hscaled (fixedSliceSparseScale target.1 target.2)
    (List.mem_map.mpr ⟨target, htarget, rfl⟩)
  rw [fixedSliceSparseEval_scale] at hz
  exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast hscale target htarget)

theorem fixedSliceSparseScaledSystemIdentity.vanish_targets
    {targets : List (ℤ × FixedSliceSparsePolynomial)}
    {targetPolynomials : List FixedSliceSparsePolynomial}
    {multipliers : List (List FixedSliceSparsePolynomial)}
    {generators : List FixedSliceSparsePolynomial}
    (hidentity : fixedSliceSparseScaledSystemIdentity
      targets multipliers generators)
    (hprojection : targets.map Prod.snd = targetPolynomials)
    (x5 x4 x3 x2 x1 trace : ℂ)
    (hscale : ∀ target ∈ targets, target.1 ≠ 0)
    (hzero : ∀ generator ∈ generators,
      fixedSliceSparseEval generator x5 x4 x3 x2 x1 trace = 0) :
    ∀ target ∈ targetPolynomials,
      fixedSliceSparseEval target x5 x4 x3 x2 x1 trace = 0 := by
  have hpairs := fixedSliceSparseScaledSystemIdentity.vanish hidentity
    x5 x4 x3 x2 x1 trace hscale hzero
  intro target htarget
  rw [← hprojection] at htarget
  obtain ⟨pair, hpair, heq⟩ := List.mem_map.mp htarget
  rw [← heq]
  exact hpairs pair hpair

end Biunimodular.F11
