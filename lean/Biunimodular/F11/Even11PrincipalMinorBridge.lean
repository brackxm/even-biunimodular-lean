/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FourierLift
import Biunimodular.F11.Even11FourierPolynomialModel
import Biunimodular.F11.Even11PrincipalMinorReduction
import Biunimodular.F11.FiniteFieldIrreducibilityCriterion
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option maxRecDepth 200000

namespace Biunimodular.F11

open ZMod Polynomial

noncomputable section

/-!
# Principal-minor bridge for the concrete order-11 Fourier operator

This file connects the abstract determinant reduction to the concrete
six-coordinate DFT.  It exposes the exact character entry of the matrix and
the no-boundary endpoint obtained once its 63 nonempty principal minors have
been verified.
-/

/-- Exact character formula for every entry of the concrete six-coordinate
Fourier matrix.  The zeroth column contains one copy of the zero orbit; every
other column contains the two representatives `j` and `-j`. -/
theorem even11Fourier_matrix_entry (i j : Fin 6) :
    even6LinearMatrix even11Fourier i j =
      if j = 0 then 1 else
        stdAddChar (-((j.1 : ZMod 11) * (i.1 : ZMod 11))) +
          stdAddChar ((j.1 : ZMod 11) * (i.1 : ZMod 11)) := by
  rw [even6LinearMatrix, even11Fourier_apply, ZMod.dft_apply]
  change (∑ x : Fin 11,
    stdAddChar (-((x.1 : ZMod 11) * (i.1 : ZMod 11))) *
      Pi.single (M := fun _ : Fin 6 => ℂ) j 1
        (even11Coordinate (x.1 : ZMod 11))) = _
  fin_cases j <;>
    simp [even11Coordinate, Pi.single_apply, Fin.sum_univ_succ,
      ZMod.val_natCast]
  all_goals (congr 2; native_decide +revert)

/-- The primitive eleventh root used by mathlib's standard additive
character. -/
def even11Zeta : ℂ := stdAddChar (1 : ZMod 11)

/-- The real-cyclotomic generator `ζ + ζ⁻¹` used by the polynomial matrix. -/
def even11Alpha : ℂ := even11Zeta + even11Zeta⁻¹

theorem even11Zeta_pow_eleven : even11Zeta ^ 11 = 1 := by
  calc
    even11Zeta ^ 11 = stdAddChar (11 • (1 : ZMod 11)) := by
      simpa [even11Zeta] using
        (AddChar.map_nsmul_eq_pow (stdAddChar (N := 11)) 11
          (1 : ZMod 11)).symm
    _ = stdAddChar (0 : ZMod 11) := by congr 1
    _ = 1 := AddChar.map_zero_eq_one _

theorem even11Zeta_ne_zero : even11Zeta ≠ 0 := by
  intro hz
  simpa [hz] using even11Zeta_pow_eleven

theorem even11Zeta_ne_one : even11Zeta ≠ 1 := by
  intro hz
  have hchar : stdAddChar (1 : ZMod 11) = stdAddChar (0 : ZMod 11) := by
    simpa [even11Zeta] using hz
  have h10 : (1 : ZMod 11) = 0 := ZMod.injective_stdAddChar hchar
  have hne : (1 : ZMod 11) ≠ 0 := by native_decide
  exact hne h10

theorem even11_stdAddChar_nat (n : Nat) :
    stdAddChar (n : ZMod 11) = even11Zeta ^ n := by
  simpa [even11Zeta] using
    AddChar.map_nsmul_eq_pow (stdAddChar (N := 11)) n (1 : ZMod 11)

theorem even11_stdAddChar_mul (i j : Fin 6) :
    stdAddChar ((i.1 : ZMod 11) * (j.1 : ZMod 11)) =
      even11Zeta ^ (i.1 * j.1) := by
  rw [← Nat.cast_mul, even11_stdAddChar_nat]

private theorem pow_complement_eleven {a : ℂ} (ha : a ^ 11 = 1)
    (r : Nat) (hr : r ≤ 11) :
    a ^ (11 - r) = a⁻¹ ^ r := by
  rw [inv_pow]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_add, Nat.sub_add_cancel hr, ha]

theorem even11Zeta_pow_complement (r : Nat) (hr : r ≤ 11) :
    even11Zeta ^ (11 - r) = even11Zeta⁻¹ ^ r :=
  pow_complement_eleven even11Zeta_pow_eleven r hr

/-- Folding an exponent into `0, ..., 5` preserves the symmetric root-of-unity
power sum represented by `even11CosRep`. -/
theorem even11Fold_power_sum (n : Nat) :
    even11Zeta ^ (even11FoldExponent n).1 +
        even11Zeta⁻¹ ^ (even11FoldExponent n).1 =
      even11Zeta ^ n + even11Zeta⁻¹ ^ n := by
  have hinvPow : even11Zeta⁻¹ ^ 11 = 1 := by
    rw [inv_pow, even11Zeta_pow_eleven, inv_one]
  have hzmod : even11Zeta ^ (n % 11) = even11Zeta ^ n :=
    pow_eq_pow_of_modEq (Nat.mod_modEq n 11) even11Zeta_pow_eleven
  have hinvmod : even11Zeta⁻¹ ^ (n % 11) = even11Zeta⁻¹ ^ n :=
    pow_eq_pow_of_modEq (Nat.mod_modEq n 11) hinvPow
  rw [← hzmod, ← hinvmod]
  by_cases h : n % 11 ≤ 5
  · simp [even11FoldExponent, h]
  · have hr : n % 11 ≤ 11 := (Nat.mod_lt n (by omega)).le
    simp only [even11FoldExponent, h, ↓reduceDIte, Fin.val_mk]
    rw [even11Zeta_pow_complement (n % 11) hr]
    have hinvComp : even11Zeta⁻¹ ^ (11 - n % 11) =
        even11Zeta ^ (n % 11) := by
      simpa only [inv_inv] using
        pow_complement_eleven hinvPow (n % 11) hr
    rw [hinvComp, add_comm]

/-- The six stored Chebyshev representatives have their intended values at
the concrete eleventh-root generator. -/
theorem even11CosRep_eval (r : Fin 6) :
    (even11CosRep r).eval₂ (Int.castRingHom ℂ) even11Alpha =
      even11Zeta ^ r.1 + even11Zeta⁻¹ ^ r.1 := by
  have hz := even11Zeta_ne_zero
  have hz11 := even11Zeta_pow_eleven
  have hsum : ∑ i ∈ Finset.range 11, even11Zeta ^ i = 0 := by
    rw [geom_sum_eq even11Zeta_ne_one, hz11, sub_self, zero_div]
  norm_num [Finset.sum_range_succ] at hsum
  fin_cases r <;>
    simp [even11CosRep, even11Alpha, Polynomial.eval₂_add,
      Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow] <;>
    field_simp <;>
    ring_nf at hz11 hsum ⊢
  linear_combination (-even11Zeta) * hsum + hz11

/-- The declared degree-five polynomial vanishes at the concrete generator
`ζ + ζ⁻¹`. -/
theorem alpha11Minpoly_even11Alpha :
    alpha11Minpoly.eval₂ (Int.castRingHom ℂ) even11Alpha = 0 := by
  have hz := even11Zeta_ne_zero
  have hz11 := even11Zeta_pow_eleven
  have hsum : ∑ i ∈ Finset.range 11, even11Zeta ^ i = 0 := by
    rw [geom_sum_eq even11Zeta_ne_one, hz11, sub_self, zero_div]
  norm_num [Finset.sum_range_succ] at hsum
  simp [alpha11Minpoly, even11Alpha, Polynomial.eval₂_add,
    Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  field_simp
  ring_nf at hz11 hsum ⊢
  linear_combination
    -(1 + even11Zeta + even11Zeta ^ 2 + even11Zeta ^ 3 +
      even11Zeta ^ 4) * hz11 + even11Zeta ^ 5 * hsum

/-- Reduction of the degree-five generator polynomial modulo two. -/
noncomputable def alpha11Minpoly2 : (ZMod 2)[X] :=
  X^5 + X^4 + X^2 + X + 1

/-- Exact Frobenius certificate for irreducibility modulo two. -/
theorem alpha11Minpoly2_irreducible : Irreducible alpha11Minpoly2 := by
  let low : (ZMod 2)[X] := X^4 + X^2 + X + 1
  have hform : alpha11Minpoly2 = X^5 + low := by
    simp only [alpha11Minpoly2, low]
    ring
  have hlow : low.degree < 5 := by
    simp only [low]
    compute_degree
    all_goals norm_num
  have hm : alpha11Minpoly2.Monic := by
    rw [hform]
    exact monic_X_pow_add hlow
  have hdeg : alpha11Minpoly2.natDegree = 5 := by
    rw [hform, natDegree_add_eq_left_of_degree_lt]
    · simp
    · simpa using hlow
  let q : (ZMod 2)[X] :=
    X^27 + X^26 + X^25 + X^22 + X^21 + X^19 + X^18 +
      X^17 + X^16 + X^15 + X^13 + X^9 + X^6 + X^4 + X^2 + X
  have hfull : alpha11Minpoly2 ∣ X ^ 2 ^ 5 - X := by
    refine ⟨q, ?_⟩
    simp only [alpha11Minpoly2, q]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have hc1 : IsCoprime alpha11Minpoly2 (X ^ 2 - X) := by
    refine ⟨1, X^3 + 1, ?_⟩
    simp only [alpha11Minpoly2]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  apply irreducible_of_frobenius_certificate
      (p := 2) (n := 5) (f := alpha11Minpoly2)
  · exact hm
  · exact hdeg
  · norm_num
  · exact hfull
  · intro d hd hdpos hdlt
    interval_cases d
    · exact hc1
    · norm_num at hd
    · norm_num at hd
    · norm_num at hd

theorem alpha11Minpoly_monic : alpha11Minpoly.Monic := by
  let low : ℤ[X] := X^4 - 4*X^3 - 3*X^2 + 3*X + 1
  have hlow : low.degree < 5 := by
    simp only [low]
    compute_degree
    all_goals norm_num
  rw [show alpha11Minpoly = X^5 + low by
    simp only [alpha11Minpoly, low]; ring]
  exact monic_X_pow_add hlow

theorem alpha11Minpoly_mod2 :
    alpha11Minpoly.map (Int.castRingHom (ZMod 2)) =
      alpha11Minpoly2 := by
  simp [alpha11Minpoly, alpha11Minpoly2]
  reduce_mod_char

/-- The declared polynomial is irreducible over the integers. -/
theorem alpha11Minpoly_irreducible : Irreducible alpha11Minpoly := by
  apply alpha11Minpoly_monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 2))
  rw [alpha11Minpoly_mod2]
  exact alpha11Minpoly2_irreducible

theorem alpha11Minpoly_irreducible_over_Q :
    Irreducible (alpha11Minpoly.map (Int.castRingHom ℚ)) := by
  exact (alpha11Minpoly_monic.irreducible_iff_irreducible_map_fraction_map).1
    alpha11Minpoly_irreducible

theorem alpha11Minpoly_mapQ_aeval :
    Polynomial.aeval even11Alpha
      (alpha11Minpoly.map (Int.castRingHom ℚ)) = 0 := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  have hhom : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) =
      Int.castRingHom ℂ := by
    ext z
    simp
  rw [hhom]
  exact alpha11Minpoly_even11Alpha

/-- The declared degree-five polynomial is the minimal polynomial of the
concrete generator over the rationals. -/
theorem alpha11Minpoly_mapQ_eq_minpoly :
    alpha11Minpoly.map (Int.castRingHom ℚ) = minpoly ℚ even11Alpha := by
  apply minpoly.eq_of_irreducible_of_monic
    alpha11Minpoly_irreducible_over_Q alpha11Minpoly_mapQ_aeval
  exact alpha11Minpoly_monic.map (Int.castRingHom ℚ)

/-- A nonzero integer polynomial of degree below five cannot vanish at the
concrete generator.  This is the algebraic justification for reading a
nonzero reduced coefficient row as a nonzero complex determinant. -/
theorem alpha11_eval_ne_zero_of_natDegree_lt_five
    {q : ℤ[X]} (hq : q ≠ 0) (hdeg : q.natDegree < 5) :
    q.eval₂ (Int.castRingHom ℂ) even11Alpha ≠ 0 := by
  intro hqeval
  let qQ := q.map (Int.castRingHom ℚ)
  have hqQ0 : qQ ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff
      (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))).mpr hq
  have hqQeval : Polynomial.aeval even11Alpha qQ = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hhom : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) =
        Int.castRingHom ℂ := by
      ext z
      simp
    rw [hhom]
    exact hqeval
  have hdvd : minpoly ℚ even11Alpha ∣ qQ :=
    minpoly.dvd ℚ even11Alpha hqQeval
  have hle : (minpoly ℚ even11Alpha).natDegree ≤ qQ.natDegree :=
    natDegree_le_of_dvd hdvd hqQ0
  rw [← alpha11Minpoly_mapQ_eq_minpoly] at hle
  have hmapdeg : qQ.natDegree = q.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ)) q
  have halphadeg :
      (alpha11Minpoly.map (Int.castRingHom ℚ)).natDegree = 5 := by
    rw [Polynomial.natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))]
    simp only [alpha11Minpoly]
    compute_degree
    all_goals norm_num
  rw [halphadeg, hmapdeg] at hle
  omega

/-- Interpret a stored five-coefficient certificate row as its degree-below-five
integer polynomial. -/
noncomputable def minorCoeffPolynomial (c : MinorCoeff) : ℤ[X] :=
  Polynomial.ofFn 5 c

@[simp] theorem minorCoeffPolynomial_coeff (c : MinorCoeff) (k : Fin 5) :
    (minorCoeffPolynomial c).coeff k.1 = c k := by
  simp [minorCoeffPolynomial]

theorem minorCoeffPolynomial_ne_zero {c : MinorCoeff} (hc : c ≠ 0) :
    minorCoeffPolynomial c ≠ 0 := by
  intro hp
  apply hc
  apply Polynomial.injective_ofFn 5
  simpa [minorCoeffPolynomial] using hp

theorem minorCoeffPolynomial_natDegree_lt (c : MinorCoeff) :
    (minorCoeffPolynomial c).natDegree < 5 := by
  simpa [minorCoeffPolynomial] using
    (Polynomial.ofFn_natDegree_lt (R := ℤ) (n := 5) (by norm_num) c)

/-- Every stored reduced principal-minor row has a nonzero value at the
concrete real-cyclotomic generator. -/
theorem even11PrincipalMinorRemainders_eval_nonzero :
    ∀ c ∈ even11PrincipalMinorRemainders,
      (minorCoeffPolynomial c).eval₂
        (Int.castRingHom ℂ) even11Alpha ≠ 0 := by
  intro c hc
  apply alpha11_eval_ne_zero_of_natDegree_lt_five
  · exact minorCoeffPolynomial_ne_zero
      (even11PrincipalMinorRemainders_all_nonzero c hc)
  · exact minorCoeffPolynomial_natDegree_lt c

/-- Evaluation at the concrete generator identifies every polynomial matrix
entry with the corresponding entry of the transported DFT. -/
theorem even11FourierPolyEntry_eval (i j : Fin 6) :
    (even11FourierPolyEntry i j).eval₂ (Int.castRingHom ℂ) even11Alpha =
      even6LinearMatrix even11Fourier i j := by
  rw [even11Fourier_matrix_entry]
  by_cases hj : j = 0
  · simp [hj, even11FourierPolyEntry]
  simp only [hj, ↓reduceIte, even11FourierPolyEntry]
  rw [even11CosRep_eval]
  rw [AddChar.map_neg_eq_inv, even11_stdAddChar_mul]
  rw [← inv_pow]
  simpa [add_comm, Nat.mul_comm] using even11Fold_power_sum (i.1 * j.1)

/-- The exact integer-polynomial matrix before evaluation at the concrete
cyclotomic generator. -/
def even11FourierPolynomialMatrix : Matrix (Fin 6) (Fin 6) ℤ[X] :=
  even11FourierPolyEntry

/-- The principal determinant polynomial associated with a coordinate
support. -/
def even11PrincipalMinorPolynomial (S : Finset (Fin 6)) : ℤ[X] :=
  Matrix.det (even11FourierPolynomialMatrix.submatrix
    (fun i : S => (i : Fin 6)) (fun j : S => (j : Fin 6)))

/-- Polynomial-evaluation formulation of the 63 nonempty principal-minor
obligations. -/
def even11FourierPolynomialEvalMatrix : Matrix (Fin 6) (Fin 6) ℂ :=
  fun i j => (even11FourierPolyEntry i j).eval₂
    (Int.castRingHom ℂ) even11Alpha

theorem even11FourierPolynomialEvalMatrix_eq :
    even11FourierPolynomialEvalMatrix = even6LinearMatrix even11Fourier := by
  ext i j
  exact even11FourierPolyEntry_eval i j

/-- Evaluation commutes with taking each polynomial principal determinant. -/
theorem even11PrincipalMinorPolynomial_eval (S : Finset (Fin 6)) :
    (even11PrincipalMinorPolynomial S).eval₂
        (Int.castRingHom ℂ) even11Alpha =
      Matrix.det (even11FourierPolynomialEvalMatrix.submatrix
        (fun i : S => (i : Fin 6)) (fun j : S => (j : Fin 6))) := by
  let e : ℤ[X] →+* ℂ :=
    Polynomial.eval₂RingHom (Int.castRingHom ℂ) even11Alpha
  change e (Matrix.det _) = Matrix.det _
  rw [e.map_det]
  rfl

def Even11PolynomialPrincipalMinorsNonzero : Prop :=
  ∀ S : Finset (Fin 6), S.Nonempty →
    Matrix.det (even11FourierPolynomialEvalMatrix.submatrix
      (fun i : S => (i : Fin 6)) (fun j : S => (j : Fin 6))) ≠ 0

/-- Finite certificate interface: for each nonempty
support, the corresponding determinant reduced modulo the degree-five
minimal polynomial is one of the stored coefficient rows. -/
def Even11PrincipalMinorRemainderCertificate : Prop :=
  ∀ S : Finset (Fin 6), S.Nonempty →
    ∃ c ∈ even11PrincipalMinorRemainders,
      even11PrincipalMinorPolynomial S %ₘ alpha11Minpoly =
        minorCoeffPolynomial c

/-- Once the finite determinant/remainder correspondence is checked, all 63
complex principal minors are nonzero. -/
theorem even11_polynomialPrincipalMinorsNonzero_of_remainderCertificate
    (hcert : Even11PrincipalMinorRemainderCertificate) :
    Even11PolynomialPrincipalMinorsNonzero := by
  intro S hS
  rcases hcert S hS with ⟨c, hc, heq⟩
  have hrow := even11PrincipalMinorRemainders_eval_nonzero c hc
  rw [← heq,
    Polynomial.eval₂_modByMonic_eq_self_of_root
      alpha11Minpoly_even11Alpha,
    even11PrincipalMinorPolynomial_eval] at hrow
  exact hrow

/-- The polynomial and concrete-DFT formulations of principal-minor
nonvanishing coincide entry by entry. -/
theorem even11_principalMinorsNonzero_iff_polynomial :
    PrincipalMinorsNonzero even11Fourier ↔
      Even11PolynomialPrincipalMinorsNonzero := by
  rw [Even11PolynomialPrincipalMinorsNonzero,
    even11FourierPolynomialEvalMatrix_eq]
  rfl

/-- The exact 63-principal-minor obligation is sufficient for concrete
order-11 support uncertainty. -/
theorem even11_noDisjointFourierSupport_of_principalMinors
    (hminor : PrincipalMinorsNonzero even11Fourier) :
    NoDisjointFourierSupport even11Fourier :=
  noDisjointFourierSupport_of_principalMinorsNonzero hminor

/-- Polynomial version of the same exact support-uncertainty endpoint. -/
theorem even11_noDisjointFourierSupport_of_polynomialPrincipalMinors
    (hminor : Even11PolynomialPrincipalMinorsNonzero) :
    NoDisjointFourierSupport even11Fourier :=
  even11_noDisjointFourierSupport_of_principalMinors
    (even11_principalMinorsNonzero_iff_polynomial.mpr hminor)

/-- Exact coefficient-remainder certificate endpoint for concrete order-11
support uncertainty. -/
theorem even11_noDisjointFourierSupport_of_remainderCertificate
    (hcert : Even11PrincipalMinorRemainderCertificate) :
    NoDisjointFourierSupport even11Fourier :=
  even11_noDisjointFourierSupport_of_polynomialPrincipalMinors
    (even11_polynomialPrincipalMinorsNonzero_of_remainderCertificate hcert)

/-- Concrete no-boundary endpoint stated directly in terms of the 63
principal minors of the order-11 matrix. -/
theorem even11_fixedSlice_common_ne_zero_of_principalMinors
    (hminor : PrincipalMinorsNonzero even11Fourier)
    {h : Even6 ℂ} (hnz : h ≠ 0) (hh : FixedSliceEq even11Fourier h) :
    fourierCoordProduct even11Fourier h 0 ≠ 0 :=
  fixedSlice_common_ne_zero_of_principalMinorsNonzero hminor hnz hh

/-- Concrete no-boundary endpoint from the polynomial principal-minor
formulation used by the exact coefficient certificate. -/
theorem even11_fixedSlice_common_ne_zero_of_polynomialPrincipalMinors
    (hminor : Even11PolynomialPrincipalMinorsNonzero)
    {h : Even6 ℂ} (hnz : h ≠ 0) (hh : FixedSliceEq even11Fourier h) :
    fourierCoordProduct even11Fourier h 0 ≠ 0 :=
  even11_fixedSlice_common_ne_zero_of_principalMinors
    (even11_principalMinorsNonzero_iff_polynomial.mpr hminor) hnz hh

/-- No-boundary fixed-slice endpoint stated directly from the finite
coefficient-remainder certificate. -/
theorem even11_fixedSlice_common_ne_zero_of_remainderCertificate
    (hcert : Even11PrincipalMinorRemainderCertificate)
    {h : Even6 ℂ} (hnz : h ≠ 0) (hh : FixedSliceEq even11Fourier h) :
    fourierCoordProduct even11Fourier h 0 ≠ 0 :=
  even11_fixedSlice_common_ne_zero_of_polynomialPrincipalMinors
    (even11_polynomialPrincipalMinorsNonzero_of_remainderCertificate hcert)
    hnz hh

end

end Biunimodular.F11
