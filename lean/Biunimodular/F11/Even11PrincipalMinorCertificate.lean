/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11PrincipalMinorBridge
import Mathlib.Algebra.Ring.MinimalAxioms

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 800000

namespace Biunimodular.F11

/-!
# Exact certificate for all order-11 even Fourier principal minors

The native computation in this file takes place in the five-coefficient
model of `ℤ[α]`, where `α` satisfies `alpha11Minpoly`.  The multiplication
formula is proved sound by evaluation at the concrete cyclotomic generator.
The resulting 63 determinant rows are then identified with the stored exact
certificate and transported to the concrete complex Fourier matrix.
-/

/-- A degree-below-five coefficient representative in the order-11 real
cyclotomic ring. -/
structure Alpha11Coeff where
  coeff : Fin 5 → ℤ
  deriving DecidableEq

namespace Alpha11Coeff

@[ext] theorem ext {a b : Alpha11Coeff} (h : a.coeff = b.coeff) : a = b := by
  cases a
  cases b
  simp_all

/-- Evaluation of a reduced coefficient row at the concrete generator. -/
noncomputable def eval (a : Alpha11Coeff) : ℂ :=
  a.coeff 0 + a.coeff 1 * even11Alpha + a.coeff 2 * even11Alpha ^ 2 +
    a.coeff 3 * even11Alpha ^ 3 + a.coeff 4 * even11Alpha ^ 4

instance : Zero Alpha11Coeff := ⟨⟨![0, 0, 0, 0, 0]⟩⟩
instance : One Alpha11Coeff := ⟨⟨![1, 0, 0, 0, 0]⟩⟩
instance : Add Alpha11Coeff :=
  ⟨fun a b => ⟨fun k => a.coeff k + b.coeff k⟩⟩
instance : Neg Alpha11Coeff := ⟨fun a => ⟨fun k => -a.coeff k⟩⟩

/-- Multiplication reduced by
`α⁵ + α⁴ - 4α³ - 3α² + 3α + 1`. -/
def mul (a b : Alpha11Coeff) : Alpha11Coeff := ⟨![
  a.coeff 0 * b.coeff 0 - a.coeff 1 * b.coeff 4 - a.coeff 2 * b.coeff 3 +
    a.coeff 2 * b.coeff 4 - a.coeff 3 * b.coeff 2 + a.coeff 3 * b.coeff 3 -
    5 * a.coeff 3 * b.coeff 4 - a.coeff 4 * b.coeff 1 +
    a.coeff 4 * b.coeff 2 - 5 * a.coeff 4 * b.coeff 3 +
    6 * a.coeff 4 * b.coeff 4,
  a.coeff 0 * b.coeff 1 + a.coeff 1 * b.coeff 0 -
    3 * a.coeff 1 * b.coeff 4 - 3 * a.coeff 2 * b.coeff 3 +
    2 * a.coeff 2 * b.coeff 4 - 3 * a.coeff 3 * b.coeff 2 +
    2 * a.coeff 3 * b.coeff 3 - 14 * a.coeff 3 * b.coeff 4 -
    3 * a.coeff 4 * b.coeff 1 + 2 * a.coeff 4 * b.coeff 2 -
    14 * a.coeff 4 * b.coeff 3 + 13 * a.coeff 4 * b.coeff 4,
  a.coeff 0 * b.coeff 2 + a.coeff 1 * b.coeff 1 +
    3 * a.coeff 1 * b.coeff 4 + a.coeff 2 * b.coeff 0 +
    3 * a.coeff 2 * b.coeff 3 - 6 * a.coeff 2 * b.coeff 4 +
    3 * a.coeff 3 * b.coeff 2 - 6 * a.coeff 3 * b.coeff 3 +
    17 * a.coeff 3 * b.coeff 4 + 3 * a.coeff 4 * b.coeff 1 -
    6 * a.coeff 4 * b.coeff 2 + 17 * a.coeff 4 * b.coeff 3 -
    32 * a.coeff 4 * b.coeff 4,
  a.coeff 0 * b.coeff 3 + a.coeff 1 * b.coeff 2 +
    4 * a.coeff 1 * b.coeff 4 + a.coeff 2 * b.coeff 1 +
    4 * a.coeff 2 * b.coeff 3 - a.coeff 2 * b.coeff 4 +
    a.coeff 3 * b.coeff 0 + 4 * a.coeff 3 * b.coeff 2 -
    a.coeff 3 * b.coeff 3 + 14 * a.coeff 3 * b.coeff 4 +
    4 * a.coeff 4 * b.coeff 1 - a.coeff 4 * b.coeff 2 +
    14 * a.coeff 4 * b.coeff 3 - 7 * a.coeff 4 * b.coeff 4,
  a.coeff 0 * b.coeff 4 + a.coeff 1 * b.coeff 3 - a.coeff 1 * b.coeff 4 +
    a.coeff 2 * b.coeff 2 - a.coeff 2 * b.coeff 3 +
    5 * a.coeff 2 * b.coeff 4 + a.coeff 3 * b.coeff 1 -
    a.coeff 3 * b.coeff 2 + 5 * a.coeff 3 * b.coeff 3 -
    6 * a.coeff 3 * b.coeff 4 + a.coeff 4 * b.coeff 0 -
    a.coeff 4 * b.coeff 1 + 5 * a.coeff 4 * b.coeff 2 -
    6 * a.coeff 4 * b.coeff 3 + 20 * a.coeff 4 * b.coeff 4
]⟩

instance : Mul Alpha11Coeff := ⟨mul⟩

@[simp] theorem zero_coeff (k : Fin 5) :
    (0 : Alpha11Coeff).coeff k = 0 := by
  fin_cases k <;> rfl

@[simp] theorem one_coeff (k : Fin 5) :
    (1 : Alpha11Coeff).coeff k = if k = 0 then 1 else 0 := by
  fin_cases k <;> rfl

@[simp] theorem add_coeff (a b : Alpha11Coeff) (k : Fin 5) :
    (a + b).coeff k = a.coeff k + b.coeff k := rfl

@[simp] theorem neg_coeff (a : Alpha11Coeff) (k : Fin 5) :
    (-a).coeff k = -a.coeff k := rfl

@[simp] theorem eval_zero : eval 0 = 0 := by simp [eval]
@[simp] theorem eval_one : eval 1 = 1 := by simp [eval]

@[simp] theorem eval_add (a b : Alpha11Coeff) :
    eval (a + b) = eval a + eval b := by
  simp [eval]
  ring

@[simp] theorem eval_neg (a : Alpha11Coeff) : eval (-a) = -eval a := by
  simp [eval]
  ring

/-- Degree-below-five representatives are uniquely determined by evaluation
at the concrete generator. -/
theorem eval_injective : Function.Injective eval := by
  intro a b hab
  by_contra hne
  have hcoeff : a.coeff - b.coeff ≠ 0 := by
    intro h
    apply hne
    apply Alpha11Coeff.ext
    funext k
    have hk := congrFun h k
    simp at hk
    omega
  have hpoly := alpha11_eval_ne_zero_of_natDegree_lt_five
    (minorCoeffPolynomial_ne_zero hcoeff)
    (minorCoeffPolynomial_natDegree_lt (a.coeff - b.coeff))
  apply hpoly
  rw [show minorCoeffPolynomial (a.coeff - b.coeff) =
      minorCoeffPolynomial a.coeff - minorCoeffPolynomial b.coeff by
    simp [minorCoeffPolynomial]]
  simp only [Polynomial.eval₂_sub]
  have heval (c : Alpha11Coeff) :
      (minorCoeffPolynomial c.coeff).eval₂
          (Int.castRingHom ℂ) even11Alpha = eval c := by
    rw [minorCoeffPolynomial, Polynomial.ofFn_eq_sum_monomial]
    change Polynomial.eval₂RingHom (Int.castRingHom ℂ) even11Alpha
      (∑ i : Fin 5, Polynomial.monomial i.1 (c.coeff i)) = eval c
    rw [map_sum]
    simp_rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
    simp [eval, Fin.sum_univ_succ]
    ring
  rw [heval a, heval b, hab, sub_self]

/-- The explicit reduced multiplication has the intended complex value. -/
@[simp] theorem eval_mul (a b : Alpha11Coeff) :
    eval (a * b) = eval a * eval b := by
  have hr := alpha11Minpoly_even11Alpha
  simp [alpha11Minpoly, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow] at hr
  change eval (mul a b) = eval a * eval b
  simp [mul, eval]
  ring_nf at hr ⊢
  let c5 : ℂ :=
    a.coeff 1 * b.coeff 4 + a.coeff 2 * b.coeff 3 +
      a.coeff 3 * b.coeff 2 + a.coeff 4 * b.coeff 1
  let c6 : ℂ :=
    a.coeff 2 * b.coeff 4 + a.coeff 3 * b.coeff 3 +
      a.coeff 4 * b.coeff 2
  let c7 : ℂ := a.coeff 3 * b.coeff 4 + a.coeff 4 * b.coeff 3
  let c8 : ℂ := a.coeff 4 * b.coeff 4
  linear_combination
    -(c5 - c6 + 5*c7 - 6*c8 +
      (c6 - c7 + 5*c8) * even11Alpha +
      (c7 - c8) * even11Alpha^2 + c8 * even11Alpha^3) * hr

instance : CommRing Alpha11Coeff :=
  CommRing.ofMinimalAxioms
    (by intro a b c; apply eval_injective; simp; ring)
    (by intro a; apply eval_injective; simp)
    (by intro a; apply eval_injective; simp)
    (by intro a b c; apply eval_injective; simp; ring)
    (by intro a b; apply eval_injective; simp [mul_comm])
    (by intro a; apply eval_injective; simp)
    (by intro a b c; apply eval_injective; simp [mul_add])

noncomputable def evalRingHom : Alpha11Coeff →+* ℂ where
  toFun := eval
  map_zero' := eval_zero
  map_one' := eval_one
  map_add' := eval_add
  map_mul' := eval_mul

theorem eval_coeffPolynomial (c : MinorCoeff) :
    (minorCoeffPolynomial c).eval₂ (Int.castRingHom ℂ) even11Alpha =
      eval ⟨c⟩ := by
  rw [minorCoeffPolynomial, Polynomial.ofFn_eq_sum_monomial]
  change Polynomial.eval₂RingHom (Int.castRingHom ℂ) even11Alpha
    (∑ i : Fin 5, Polynomial.monomial i.1 (c i)) = eval ⟨c⟩
  rw [map_sum]
  simp_rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
  simp [eval, Fin.sum_univ_succ]
  ring

/-- Reduced coefficient representatives of the six symmetric root-of-unity
power sums. -/
def cosCoeff : Fin 6 → Alpha11Coeff
  | 0 => ⟨fun k => match k.1 with | 0 => 2 | _ => 0⟩
  | 1 => ⟨fun k => match k.1 with | 1 => 1 | _ => 0⟩
  | 2 => ⟨fun k => match k.1 with | 0 => -2 | 2 => 1 | _ => 0⟩
  | 3 => ⟨fun k => match k.1 with | 1 => -3 | 3 => 1 | _ => 0⟩
  | 4 => ⟨fun k => match k.1 with | 0 => 2 | 2 => -4 | 4 => 1 | _ => 0⟩
  | 5 => ⟨fun k => match k.1 with
      | 0 => -1 | 1 => 2 | 2 => 3 | 3 => -1 | _ => -1⟩

/-- Reduced coefficient matrix of the unnormalised even Fourier operator. -/
def matrixEntry (i j : Fin 6) : Alpha11Coeff :=
  if j = 0 then 1 else cosCoeff (even11FoldExponent (i.1 * j.1))

theorem eval_cosCoeff (r : Fin 6) :
    eval (cosCoeff r) =
      (even11CosRep r).eval₂ (Int.castRingHom ℂ) even11Alpha := by
  fin_cases r <;>
    simp [cosCoeff, even11CosRep, eval,
      Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow] <;>
    ring

theorem eval_matrixEntry (i j : Fin 6) :
    eval (matrixEntry i j) = even11FourierPolynomialEvalMatrix i j := by
  by_cases hj : j = 0
  · simp [matrixEntry, even11FourierPolynomialEvalMatrix,
      even11FourierPolyEntry, hj]
  · simp [matrixEntry, even11FourierPolynomialEvalMatrix,
      even11FourierPolyEntry, hj, eval_cosCoeff]

/-- The coordinate support encoded by a six-bit mask. -/
def maskSupport (mask : Nat) : Finset (Fin 6) :=
  Finset.univ.filter fun i => mask.testBit i.1

/-- Computable Leibniz determinant in the reduced coefficient ring. -/
def principalDet (S : Finset (Fin 6)) : Alpha11Coeff :=
  ∑ σ : Equiv.Perm S,
    (Equiv.Perm.sign σ : Alpha11Coeff) * ∏ i : S, matrixEntry (σ i) i

def coefficientMatrix : Matrix (Fin 6) (Fin 6) Alpha11Coeff :=
  matrixEntry

theorem principalDet_eq_det (S : Finset (Fin 6)) :
    principalDet S = Matrix.det (coefficientMatrix.submatrix
      (fun i : S => (i : Fin 6)) (fun j : S => (j : Fin 6))) := by
  rw [Matrix.det_apply']
  rfl

/-- The computable reduced determinant evaluates to the concrete polynomial
matrix determinant. -/
theorem eval_principalDet (S : Finset (Fin 6)) :
    eval (principalDet S) =
      Matrix.det (even11FourierPolynomialEvalMatrix.submatrix
        (fun i : S => (i : Fin 6)) (fun j : S => (j : Fin 6))) := by
  rw [principalDet_eq_det]
  change evalRingHom (Matrix.det _) = _
  rw [evalRingHom.map_det]
  apply congrArg Matrix.det
  ext i j
  exact eval_matrixEntry i j

/-- Native verification of the 63 stored reduced determinant rows. -/
theorem all_principalDet :
    ∀ p ∈ List.zip even11PrincipalMinorMasks even11PrincipalMinorRemainders,
      (principalDet (maskSupport p.1)).coeff = p.2 := by
  native_decide

/-- The mask table covers every nonempty support in six coordinates. -/
theorem all_nonempty_supports_covered :
    ∀ S : Finset (Fin 6), S.Nonempty →
      ∃ p ∈ List.zip even11PrincipalMinorMasks even11PrincipalMinorRemainders,
        maskSupport p.1 = S := by
  native_decide

/-- The stored table proves all polynomial-evaluation principal minors
nonzero. -/
theorem polynomialPrincipalMinorsNonzero :
    Even11PolynomialPrincipalMinorsNonzero := by
  intro S hS
  rcases all_nonempty_supports_covered S hS with ⟨p, hp, hsupport⟩
  have hc : p.2 ∈ even11PrincipalMinorRemainders :=
    (List.of_mem_zip hp).2
  have hrow := even11PrincipalMinorRemainders_eval_nonzero p.2 hc
  rw [eval_coeffPolynomial] at hrow
  have hcoeff := all_principalDet p hp
  have hdet : principalDet (maskSupport p.1) = ⟨p.2⟩ := by
    exact Alpha11Coeff.ext hcoeff
  rw [← hdet, hsupport, eval_principalDet] at hrow
  exact hrow

theorem polynomial_eq_of_eval_eq_of_natDegree_lt_five
    {p q : Polynomial ℤ} (hp : p.natDegree < 5) (hq : q.natDegree < 5)
    (heval : p.eval₂ (Int.castRingHom ℂ) even11Alpha =
      q.eval₂ (Int.castRingHom ℂ) even11Alpha) :
    p = q := by
  by_contra hne
  have hsub : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hdeg : (p - q).natDegree < 5 :=
    (Polynomial.natDegree_sub_le p q).trans_lt (max_lt hp hq)
  exact alpha11_eval_ne_zero_of_natDegree_lt_five hsub hdeg
    (by simp [Polynomial.eval₂_sub, heval])

/-- The native table implements the exact remainder-certificate interface
from the bridge module. -/
theorem remainderCertificate : Even11PrincipalMinorRemainderCertificate := by
  intro S hS
  rcases all_nonempty_supports_covered S hS with ⟨p, hp, hsupport⟩
  refine ⟨p.2, (List.of_mem_zip hp).2, ?_⟩
  have hcoeff := all_principalDet p hp
  have hdet : principalDet (maskSupport p.1) = ⟨p.2⟩ :=
    Alpha11Coeff.ext hcoeff
  have heval :
      (even11PrincipalMinorPolynomial S).eval₂
          (Int.castRingHom ℂ) even11Alpha =
        (minorCoeffPolynomial p.2).eval₂
          (Int.castRingHom ℂ) even11Alpha := by
    rw [even11PrincipalMinorPolynomial_eval, ← eval_principalDet,
      ← hsupport, hdet, ← eval_coeffPolynomial]
  have hminDegree : alpha11Minpoly.natDegree = 5 := by
    simp only [alpha11Minpoly]
    compute_degree
    all_goals norm_num
  have hminNeOne : alpha11Minpoly ≠ 1 := by
    intro h
    have := congrArg Polynomial.natDegree h
    simp [hminDegree] at this
  apply polynomial_eq_of_eval_eq_of_natDegree_lt_five
  · have hmod := Polynomial.natDegree_modByMonic_lt
      (even11PrincipalMinorPolynomial S) alpha11Minpoly_monic hminNeOne
    rwa [hminDegree] at hmod
  · exact minorCoeffPolynomial_natDegree_lt p.2
  · rw [Polynomial.eval₂_modByMonic_eq_self_of_root
      alpha11Minpoly_even11Alpha]
    exact heval

end Alpha11Coeff

/-- Unconditional exact verification of all 63 nonempty principal minors of
the concrete order-11 even Fourier matrix. -/
theorem even11_principalMinorsNonzero : PrincipalMinorsNonzero even11Fourier :=
  even11_principalMinorsNonzero_iff_polynomial.mpr
    Alpha11Coeff.polynomialPrincipalMinorsNonzero

/-- Unconditional coordinatewise support uncertainty for the concrete
six-coordinate Fourier operator. -/
theorem even11_noDisjointFourierSupport_certified :
    NoDisjointFourierSupport even11Fourier :=
  even11_noDisjointFourierSupport_of_principalMinors
    even11_principalMinorsNonzero

/-- The same unconditional support uncertainty for the normalized Fourier
involution. -/
theorem even11_normalized_noDisjointFourierSupport_certified :
    NoDisjointFourierSupport even11FourierNormalized := by
  have hsR : Real.sqrt 11 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hs : (Real.sqrt 11 : ℂ) ≠ 0 := by exact_mod_cast hsR
  exact (noDisjointFourierSupport_smul_iff (inv_ne_zero hs)).2
    even11_noDisjointFourierSupport_certified

/-- Unconditional exclusion of the projective boundary of the concrete
order-11 fixed slice. -/
theorem even11_fixedSlice_common_ne_zero_certified
    {h : Even6 ℂ} (hnz : h ≠ 0) (hh : FixedSliceEq even11Fourier h) :
    fourierCoordProduct even11Fourier h 0 ≠ 0 :=
  even11_fixedSlice_common_ne_zero_of_principalMinors
    even11_principalMinorsNonzero hnz hh

/-- Unconditional no-boundary theorem for the normalized Fourier involution
used by the quotient invariant. -/
theorem even11_normalized_fixedSlice_common_ne_zero_certified
    {h : Even6 ℂ} (hnz : h ≠ 0)
    (hh : FixedSliceEq even11FourierNormalized h) :
    fourierCoordProduct even11FourierNormalized h 0 ≠ 0 :=
  fixedSlice_common_ne_zero_of_uncertainty
    even11_normalized_noDisjointFourierSupport_certified hnz hh

/-- The exact principal-minor certificate makes the homogeneous quotient
denominator nonzero on every nonzero normalized fixed-slice point. -/
theorem even11_normalized_fixedSliceQDen_ne_zero_certified
    {h : Even6 ℂ} (hnz : h ≠ 0)
    (hh : FixedSliceEq even11FourierNormalized h) :
    fixedSliceQDen even11FourierNormalized h ≠ 0 :=
  fixedSliceQDen_ne_zero_of_common_ne_zero
    (even11_normalized_fixedSlice_common_ne_zero_certified hnz hh)

/-- Consequently the normalized fixed-slice quotient equation has exactly its
canonical affine value, with no boundary exception. -/
theorem even11_normalized_fixedSliceUEquation_iff
    {h : Even6 ℂ} (hnz : h ≠ 0)
    (hh : FixedSliceEq even11FourierNormalized h) {u : ℂ} :
    fixedSliceUEquation even11FourierNormalized h u ↔
      u = fixedSliceUValue even11FourierNormalized h :=
  fixedSliceUEquation_iff_eq_value
    (even11_normalized_fixedSliceQDen_ne_zero_certified hnz hh)

end Biunimodular.F11
