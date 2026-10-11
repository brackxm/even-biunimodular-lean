/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.P150RootCoverAssembly11
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# Exact isolation of the circle-admissible P150 roots

For each gap between the forty stored root boxes, map the gap `(a,b)` to the
positive half-line by `y = (a + b t)/(1+t)`.  The cleared transformed factor
has coefficients of one strict sign, so it cannot vanish for `t ≥ 0`.
This proves that every root with `0 ≤ y < 1` lies in a listed box without a
large Sturm-chain replay.
-/

def p150FactorCoefficientsQ11 : KFactor → List ℚ
  | .g5 => p150G5Coeffs11.map (fun c => (c : ℚ))
  | .f30 => p150F30Coeffs11.map (fun c => (c : ℚ))
  | .f40 => p150F40Coeffs11.map (fun c => (c : ℚ))

def p150FactorPolynomialQ11 (factor : KFactor) : ℚ[X] :=
  polynomialOfCoefficientsQ11 (p150FactorCoefficientsQ11 factor)

def p150FactorPolynomialR11 (factor : KFactor) : ℝ[X] :=
  (p150FactorPolynomialQ11 factor).map (algebraMap ℚ ℝ)

def p150FactorRootIndices11 (factor : KFactor) : List (Fin 40) :=
  (List.finRange 40).filter fun q =>
    (squaredKRootIntervals40[q.1]!).factor = factor

def p150FactorGapsAux11 (prev : ℚ) : List (Fin 40) → List RationalInterval
  | [] => [⟨prev, 1⟩]
  | q :: qs =>
      ⟨prev, (squaredKRootIntervals40[q.1]!).box.lo⟩ ::
        p150FactorGapsAux11
          (squaredKRootIntervals40[q.1]!).box.hi qs

def p150FactorGaps11 (factor : KFactor) : List RationalInterval :=
  p150FactorGapsAux11 0 (p150FactorRootIndices11 factor)

/-- Cleared coefficient list of
`(1+t)^(n) p((a+b*t)/(1+t))`, constructed recursively in Horner form. -/
def coefficientMobiusQ11 : List ℚ → ℚ → ℚ → List ℚ
  | [], _, _ => []
  | c :: cs, a, b =>
      coefficientAddQ11
        (coefficientScaleQ11 c (coefficientPowQ11 [1, 1] cs.length))
        (coefficientMulQ11 [a, b] (coefficientMobiusQ11 cs a b))

def HasStrictUniformSignQ11 (cs : List ℚ) : Prop :=
  cs ≠ [] ∧
    (cs.Forall (fun c => 0 < c) ∨ cs.Forall (fun c => c < 0))

instance (cs : List ℚ) : Decidable (HasStrictUniformSignQ11 cs) :=
  by
    unfold HasStrictUniformSignQ11
    infer_instance

/-- Ascending coefficient list for the formal derivative.  The recursive
formula mirrors `(c + X*p)' = p + X*p'`; keeping it executable lets the
forty local monotonicity checks be discharged by `native_decide`. -/
def coefficientDerivativeQ11 : List ℚ → List ℚ
  | [] => []
  | _ :: cs => coefficientAddQ11 cs (0 :: coefficientDerivativeQ11 cs)

theorem polynomialOfCoefficientsQ11_derivative (cs : List ℚ) :
    polynomialOfCoefficientsQ11 (coefficientDerivativeQ11 cs) =
      (polynomialOfCoefficientsQ11 cs).derivative := by
  induction cs with
  | nil => simp [coefficientDerivativeQ11]
  | cons c cs ih =>
    rw [coefficientDerivativeQ11, polynomialOfCoefficientsQ11_add]
    simp only [polynomialOfCoefficientsQ11_cons]
    rw [ih]
    simp [Polynomial.derivative_add, Polynomial.derivative_mul]

def p150FactorDerivativeCoefficientsQ11 (factor : KFactor) : List ℚ :=
  coefficientDerivativeQ11 (p150FactorCoefficientsQ11 factor)

/-- On every stored root interval the derivative of the tagged factor has
one strict sign.  This is a compact exact replay: after the same Mobius
change of variables used for the complementary gaps, every coefficient is
strictly positive or every coefficient is strictly negative. -/
theorem p150_factor_interval_derivative_uniform_sign11 :
    ∀ q : Fin 40,
      let I := squaredKRootIntervals40[q.1]!
      HasStrictUniformSignQ11
        (coefficientMobiusQ11
          (p150FactorDerivativeCoefficientsQ11 I.factor)
          I.box.lo I.box.hi) := by
  native_decide

theorem p150FactorRootIndices11_lengths :
    (p150FactorRootIndices11 .g5).length = 5 ∧
    (p150FactorRootIndices11 .f30).length = 15 ∧
    (p150FactorRootIndices11 .f40).length = 20 := by
  native_decide

theorem p150FactorRootIndices11_tags :
    ∀ (factor : KFactor) (q : Fin 40),
      q ∈ p150FactorRootIndices11 factor →
      (squaredKRootIntervals40[q.1]!).factor = factor := by
  intro factor
  cases factor <;> native_decide

/-- The core finite root-isolation computation: every complementary gap has
a cleared Möbius transform whose nonzero coefficients all have the same
strict sign. -/
theorem p150_factor_gap_uniform_sign11 :
    ∀ (factor : KFactor) (gap : RationalInterval),
      gap ∈ p150FactorGaps11 factor →
      HasStrictUniformSignQ11
        (coefficientMobiusQ11 (p150FactorCoefficientsQ11 factor)
          gap.lo gap.hi) := by
  intro factor
  cases factor <;> intro gap hgap
  all_goals
    apply (List.forall_iff_forall_mem.mp (by native_decide)) gap hgap

theorem p150_factor_eval_one_ne_zero11 :
    ∀ factor : KFactor,
      (p150FactorPolynomialQ11 factor).eval 1 ≠ 0 := by
  intro factor
  cases factor <;>
    norm_num [p150FactorPolynomialQ11, p150FactorCoefficientsQ11,
      polynomialOfCoefficientsQ11, p150G5Coeffs11,
      p150F30Coeffs11, p150F40Coeffs11]

theorem polynomialOfCoefficientsQ11_mobius (c : ℚ) (cs : List ℚ)
    (a b : ℚ) :
    polynomialOfCoefficientsQ11 (coefficientMobiusQ11 (c :: cs) a b) =
      C c * (1 + X) ^ cs.length +
        (C a + C b * X) *
          polynomialOfCoefficientsQ11 (coefficientMobiusQ11 cs a b) := by
  simp [coefficientMobiusQ11, polynomialOfCoefficientsQ11_add,
    polynomialOfCoefficientsQ11_scale, polynomialOfCoefficientsQ11_mul,
    polynomialOfCoefficientsQ11_pow]

/-- Semantic correctness of the cleared Möbius transform. -/
theorem polynomialOfCoefficientsQ11_mobius_eval
    (c : ℚ) (cs : List ℚ) (a b : ℚ) (y t : ℝ)
    (hrel : (1 + t) * y = (a : ℝ) + (b : ℝ) * t) :
    ((polynomialOfCoefficientsQ11
      (coefficientMobiusQ11 (c :: cs) a b)).map
        (algebraMap ℚ ℝ)).eval t =
      (1 + t) ^ cs.length *
        ((polynomialOfCoefficientsQ11 (c :: cs)).map
          (algebraMap ℚ ℝ)).eval y := by
  induction cs generalizing c with
  | nil =>
    simp [coefficientMobiusQ11, coefficientAddQ11,
      coefficientScaleQ11, coefficientMulQ11, coefficientPowQ11,
      polynomialOfCoefficientsQ11]
  | cons d ds ih =>
    rw [polynomialOfCoefficientsQ11_mobius]
    simp only [Polynomial.map_add, Polynomial.eval_add,
      Polynomial.map_mul, Polynomial.eval_mul, Polynomial.map_C,
      Polynomial.eval_C, Polynomial.map_pow, Polynomial.eval_pow,
      Polynomial.map_one, Polynomial.eval_one, Polynomial.map_X,
      Polynomial.eval_X]
    rw [ih d]
    simp only [polynomialOfCoefficientsQ11_cons, Polynomial.map_add,
      Polynomial.eval_add, Polynomial.map_mul, Polynomial.eval_mul,
      Polynomial.map_C, Polynomial.eval_C, Polynomial.map_X,
      Polynomial.eval_X, List.length_cons, pow_succ]
    have ha : (algebraMap ℚ ℝ) a = (a : ℝ) := by norm_num
    have hb : (algebraMap ℚ ℝ) b = (b : ℝ) := by norm_num
    rw [ha, hb]
    rw [← hrel]
    ring

theorem polynomialOfCoefficientsQ11_eval_nonneg
    (cs : List ℚ) (t : ℝ) (ht : 0 ≤ t)
    (hcs : cs.Forall (fun c => 0 ≤ c)) :
    0 ≤ ((polynomialOfCoefficientsQ11 cs).map
      (algebraMap ℚ ℝ)).eval t := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc_tail : 0 ≤ c ∧ cs.Forall (fun c => 0 ≤ c) :=
      (List.forall_cons (fun c : ℚ => 0 ≤ c) c cs).mp hcs
    have hc : 0 ≤ c := hc_tail.1
    have htail : cs.Forall (fun c => 0 ≤ c) := hc_tail.2
    rw [polynomialOfCoefficientsQ11_cons, Polynomial.map_add,
      Polynomial.eval_add, Polynomial.map_mul, Polynomial.eval_mul]
    simp only [Polynomial.map_C, Polynomial.eval_C, Polynomial.map_X,
      Polynomial.eval_X]
    apply add_nonneg
    · change 0 ≤ (c : ℝ)
      exact Rat.cast_nonneg.mpr hc
    · exact mul_nonneg ht (ih htail)

theorem polynomialOfCoefficientsQ11_eval_nonpos
    (cs : List ℚ) (t : ℝ) (ht : 0 ≤ t)
    (hcs : cs.Forall (fun c => c ≤ 0)) :
    ((polynomialOfCoefficientsQ11 cs).map
      (algebraMap ℚ ℝ)).eval t ≤ 0 := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc_tail : c ≤ 0 ∧ cs.Forall (fun c => c ≤ 0) :=
      (List.forall_cons (fun c : ℚ => c ≤ 0) c cs).mp hcs
    have hc : c ≤ 0 := hc_tail.1
    have htail : cs.Forall (fun c => c ≤ 0) := hc_tail.2
    rw [polynomialOfCoefficientsQ11_cons, Polynomial.map_add,
      Polynomial.eval_add, Polynomial.map_mul, Polynomial.eval_mul]
    simp only [Polynomial.map_C, Polynomial.eval_C, Polynomial.map_X,
      Polynomial.eval_X]
    apply add_nonpos
    · change (c : ℝ) ≤ 0
      exact Rat.cast_nonpos.mpr hc
    · exact mul_nonpos_of_nonneg_of_nonpos ht (ih htail)

theorem polynomialOfCoefficientsQ11_eval_ne_zero_of_uniform_sign
    (cs : List ℚ) (t : ℝ) (ht : 0 ≤ t)
    (hsign : HasStrictUniformSignQ11 cs) :
    ((polynomialOfCoefficientsQ11 cs).map
      (algebraMap ℚ ℝ)).eval t ≠ 0 := by
  cases cs with
  | nil => exact False.elim (hsign.1 rfl)
  | cons c cs =>
    rcases hsign.2 with hpos | hneg
    · have hc_tail : 0 < c ∧ cs.Forall (fun x => 0 < x) :=
        (List.forall_cons (fun x : ℚ => 0 < x) c cs).mp hpos
      have hc : 0 < c := hc_tail.1
      have htail : cs.Forall (fun x => 0 ≤ x) :=
        hc_tail.2.imp fun _ hx => hx.le
      rw [polynomialOfCoefficientsQ11_cons, Polynomial.map_add,
        Polynomial.eval_add, Polynomial.map_mul, Polynomial.eval_mul]
      simp only [Polynomial.map_C, Polynomial.eval_C, Polynomial.map_X,
        Polynomial.eval_X]
      apply ne_of_gt
      apply add_pos_of_pos_of_nonneg
      · change 0 < (c : ℝ)
        exact Rat.cast_pos.mpr hc
      · exact mul_nonneg ht
          (polynomialOfCoefficientsQ11_eval_nonneg cs t ht htail)
    · have hc_tail : c < 0 ∧ cs.Forall (fun x => x < 0) :=
        (List.forall_cons (fun x : ℚ => x < 0) c cs).mp hneg
      have hc : c < 0 := hc_tail.1
      have htail : cs.Forall (fun x => x ≤ 0) :=
        hc_tail.2.imp fun _ hx => hx.le
      rw [polynomialOfCoefficientsQ11_cons, Polynomial.map_add,
        Polynomial.eval_add, Polynomial.map_mul, Polynomial.eval_mul]
      simp only [Polynomial.map_C, Polynomial.eval_C, Polynomial.map_X,
        Polynomial.eval_X]
      apply ne_of_lt
      apply add_neg_of_neg_of_nonpos
      · change (c : ℝ) < 0
        exact_mod_cast hc
      · exact mul_nonpos_of_nonneg_of_nonpos ht
          (polynomialOfCoefficientsQ11_eval_nonpos cs t ht htail)

/-- The tagged factor derivative cannot vanish in the half-open stored root
interval.  The upper endpoint is omitted only because the Mobius parameter
uses `(hi-y)` as denominator; Rolle points arising below are automatically
strictly below it. -/
theorem p150FactorPolynomialR11_derivative_ne_zero_in_interval
    (q : Fin 40) (y : ℝ)
    (hlo : ((squaredKRootIntervals40[q.1]!).box.lo : ℝ) ≤ y)
    (hhi : y < ((squaredKRootIntervals40[q.1]!).box.hi : ℝ)) :
    (p150FactorPolynomialR11
      (squaredKRootIntervals40[q.1]!).factor).derivative.eval y ≠ 0 := by
  let I := squaredKRootIntervals40[q.1]!
  change (p150FactorPolynomialR11 I.factor).derivative.eval y ≠ 0
  let t : ℝ := (y - (I.box.lo : ℝ)) / ((I.box.hi : ℝ) - y)
  have hden : 0 < (I.box.hi : ℝ) - y := sub_pos.mpr hhi
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) hden.le
  have hrel : (1 + t) * y =
      (I.box.lo : ℝ) + (I.box.hi : ℝ) * t := by
    dsimp [t]
    field_simp [ne_of_gt hden]
    ring
  have hs := p150_factor_interval_derivative_uniform_sign11 q
  change HasStrictUniformSignQ11
    (coefficientMobiusQ11
      (p150FactorDerivativeCoefficientsQ11 I.factor)
      I.box.lo I.box.hi) at hs
  have hne := polynomialOfCoefficientsQ11_eval_ne_zero_of_uniform_sign
    (coefficientMobiusQ11
      (p150FactorDerivativeCoefficientsQ11 I.factor)
      I.box.lo I.box.hi) t ht hs
  cases hcs : p150FactorDerivativeCoefficientsQ11 I.factor with
  | nil =>
      exact False.elim (hs.1 (by simp [hcs, coefficientMobiusQ11]))
  | cons c cs =>
      have heq := polynomialOfCoefficientsQ11_mobius_eval
        c cs I.box.lo I.box.hi y t hrel
      rw [← hcs] at heq
      have hpow : (1 + t) ^ cs.length ≠ (0 : ℝ) := by
        positivity
      intro hzero
      have hderivativeQ :
          (((polynomialOfCoefficientsQ11
            (p150FactorDerivativeCoefficientsQ11 I.factor)).map
              (algebraMap ℚ ℝ)).eval y) = 0 := by
        rw [p150FactorDerivativeCoefficientsQ11,
          polynomialOfCoefficientsQ11_derivative]
        simpa [p150FactorPolynomialR11, p150FactorPolynomialQ11,
          Polynomial.derivative_map] using hzero
      rw [hderivativeQ, mul_zero] at heq
      exact hne heq

/-- Each of the forty rational boxes contains at most one root of its tagged
factor.  This is the semantic consequence of the exact derivative-sign
certificate above. -/
theorem p150FactorPolynomialR11_root_unique_in_interval
    (q : Fin 40) (x y : ℝ)
    (hxlo : ((squaredKRootIntervals40[q.1]!).box.lo : ℝ) ≤ x)
    (hxhi : x ≤ ((squaredKRootIntervals40[q.1]!).box.hi : ℝ))
    (hylo : ((squaredKRootIntervals40[q.1]!).box.lo : ℝ) ≤ y)
    (hyhi : y ≤ ((squaredKRootIntervals40[q.1]!).box.hi : ℝ))
    (hxroot : (p150FactorPolynomialR11
      (squaredKRootIntervals40[q.1]!).factor).IsRoot x)
    (hyroot : (p150FactorPolynomialR11
      (squaredKRootIntervals40[q.1]!).factor).IsRoot y) :
    x = y := by
  let p := p150FactorPolynomialR11
    (squaredKRootIntervals40[q.1]!).factor
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have heval : p.eval x = p.eval y := by
      rw [Polynomial.IsRoot] at hxroot hyroot
      rw [hxroot, hyroot]
    obtain ⟨z, hz, hzero⟩ :=
      exists_deriv_eq_zero hlt p.continuousOn heval
    rw [p.deriv] at hzero
    exact p150FactorPolynomialR11_derivative_ne_zero_in_interval q z
      (hxlo.trans hz.1.le) (hz.2.trans_le hyhi) hzero
  · have heval : p.eval y = p.eval x := by
      rw [Polynomial.IsRoot] at hxroot hyroot
      rw [hxroot, hyroot]
    obtain ⟨z, hz, hzero⟩ :=
      exists_deriv_eq_zero hgt p.continuousOn heval
    rw [p.deriv] at hzero
    exact p150FactorPolynomialR11_derivative_ne_zero_in_interval q z
      (hylo.trans hz.1.le) (hz.2.trans_le hxhi) hzero

private theorem factor_interval_or_gap_aux11
    (qs : List (Fin 40)) (prev : ℚ) (y : ℝ)
    (hprev : (prev : ℝ) ≤ y) (hy1 : y ≤ 1) :
    (∃ q ∈ qs,
      (squaredKRootIntervals40[q.1]!).box.lo ≤ y ∧
      y ≤ (squaredKRootIntervals40[q.1]!).box.hi) ∨
    y = 1 ∨
    ∃ gap ∈ p150FactorGapsAux11 prev qs,
      (gap.lo : ℝ) ≤ y ∧ y < (gap.hi : ℝ) := by
  induction qs generalizing prev with
  | nil =>
    by_cases hy : y = 1
    · exact Or.inr (Or.inl hy)
    · refine Or.inr (Or.inr ⟨⟨prev, 1⟩, ?_, hprev, ?_⟩)
      · simp [p150FactorGapsAux11]
      · have hlt : y < (1 : ℝ) := lt_of_le_of_ne hy1 hy
        simpa using hlt
  | cons q qs ih =>
    let I := squaredKRootIntervals40[q.1]!
    by_cases hlo : y < (I.box.lo : ℝ)
    · refine Or.inr (Or.inr ⟨⟨prev, I.box.lo⟩, ?_, hprev, hlo⟩)
      simp [p150FactorGapsAux11, I]
    · have hylo : (I.box.lo : ℝ) ≤ y := le_of_not_gt hlo
      by_cases hhi : y ≤ (I.box.hi : ℝ)
      · exact Or.inl ⟨q, by simp, hylo, hhi⟩
      · have hhiy : (I.box.hi : ℝ) ≤ y := (lt_of_not_ge hhi).le
        rcases ih I.box.hi hhiy with hroot | hone | hgap
        · exact Or.inl <| by
            rcases hroot with ⟨r, hr, hry⟩
            exact ⟨r, by simp [hr], hry⟩
        · exact Or.inr (Or.inl hone)
        · exact Or.inr (Or.inr <| by
            rcases hgap with ⟨gap, hgap, hgy⟩
            refine ⟨gap, ?_, hgy⟩
            rw [p150FactorGapsAux11]
            right
            exact hgap)

theorem p150_factor_interval_or_gap11
    (factor : KFactor) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (∃ q ∈ p150FactorRootIndices11 factor,
      (squaredKRootIntervals40[q.1]!).box.lo ≤ y ∧
      y ≤ (squaredKRootIntervals40[q.1]!).box.hi) ∨
    y = 1 ∨
    ∃ gap ∈ p150FactorGaps11 factor,
      (gap.lo : ℝ) ≤ y ∧ y < (gap.hi : ℝ) := by
  exact factor_interval_or_gap_aux11
    (p150FactorRootIndices11 factor) 0 y (by simpa) hy1

theorem p150FactorPolynomialR11_not_isRoot_in_gap
    (factor : KFactor) (gap : RationalInterval)
    (hgap : gap ∈ p150FactorGaps11 factor)
    (y : ℝ) (hlo : (gap.lo : ℝ) ≤ y) (hhi : y < (gap.hi : ℝ)) :
    ¬(p150FactorPolynomialR11 factor).IsRoot y := by
  let t : ℝ := (y - (gap.lo : ℝ)) / ((gap.hi : ℝ) - y)
  have hden : 0 < (gap.hi : ℝ) - y := sub_pos.mpr hhi
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) hden.le
  have hrel : (1 + t) * y =
      (gap.lo : ℝ) + (gap.hi : ℝ) * t := by
    dsimp [t]
    field_simp [ne_of_gt hden]
    ring
  have hs := p150_factor_gap_uniform_sign11 factor gap hgap
  have hne := polynomialOfCoefficientsQ11_eval_ne_zero_of_uniform_sign
    (coefficientMobiusQ11 (p150FactorCoefficientsQ11 factor)
      gap.lo gap.hi) t ht hs
  intro hyroot
  rw [Polynomial.IsRoot] at hyroot
  have heq := polynomialOfCoefficientsQ11_mobius_eval
    (c := (p150FactorCoefficientsQ11 factor)[0]!)
    (cs := (p150FactorCoefficientsQ11 factor).tail)
    gap.lo gap.hi y t hrel
  have hlist : (p150FactorCoefficientsQ11 factor)[0]! ::
      (p150FactorCoefficientsQ11 factor).tail =
        p150FactorCoefficientsQ11 factor := by
    cases factor <;> native_decide
  rw [hlist] at heq
  change ((polynomialOfCoefficientsQ11
      (p150FactorCoefficientsQ11 factor)).map
        (algebraMap ℚ ℝ)).eval y = 0 at hyroot
  rw [hyroot, mul_zero] at heq
  exact hne heq

/-- The three rational factors are exactly the casts of the integer
polynomials used to define `p150K11`. -/
theorem p150FactorPolynomialQ11_eq_map_integer :
    p150FactorPolynomialQ11 .g5 =
        p150G5Y11.map (Int.castRingHom ℚ) ∧
    p150FactorPolynomialQ11 .f30 =
        p150F30Y11.map (Int.castRingHom ℚ) ∧
    p150FactorPolynomialQ11 .f40 =
        p150F40Y11.map (Int.castRingHom ℚ) := by
  constructor
  · simpa [p150FactorPolynomialQ11, p150FactorCoefficientsQ11,
      p150G5Y11] using
        (polynomialOfCoefficientsZ_map_Q11 p150G5Coeffs11).symm
  constructor
  · simpa [p150FactorPolynomialQ11, p150FactorCoefficientsQ11,
      p150F30Y11] using
        (polynomialOfCoefficientsZ_map_Q11 p150F30Coeffs11).symm
  · simpa [p150FactorPolynomialQ11, p150FactorCoefficientsQ11,
      p150F40Y11] using
        (polynomialOfCoefficientsZ_map_Q11 p150F40Coeffs11).symm

/-- Evaluation of P150 splits into the three squared-coordinate factors. -/
theorem p150KR11_eval_factorization (k : ℝ) :
    p150KR11.eval k =
      (p150FactorPolynomialR11 .g5).eval (k ^ 2) *
      (p150FactorPolynomialR11 .f30).eval (k ^ 2) *
      (p150FactorPolynomialR11 .f40).eval (k ^ 2) := by
  rw [p150KR11, p150KQ11, p150K11, Polynomial.map_comp,
    Polynomial.map_comp, Polynomial.eval_comp]
  simp only [Polynomial.map_pow, Polynomial.map_X, Polynomial.eval_pow,
    Polynomial.eval_X]
  simp only [p150SquaredY11, Polynomial.map_mul, Polynomial.eval_mul]
  rw [← p150FactorPolynomialQ11_eq_map_integer.1,
    ← p150FactorPolynomialQ11_eq_map_integer.2.1,
    ← p150FactorPolynomialQ11_eq_map_integer.2.2]
  rfl

theorem p150FactorPolynomialR11_eval_one_ne_zero
    (factor : KFactor) :
    (p150FactorPolynomialR11 factor).eval 1 ≠ 0 := by
  have hq := p150_factor_eval_one_ne_zero11 factor
  have hr : (((p150FactorPolynomialQ11 factor).eval (1 : ℚ) : ℚ) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr hq
  simpa [p150FactorPolynomialR11, Polynomial.aeval_def] using hr

/-- Every root of one factor in the squared circle range belongs to one of
that factor's listed boxes. -/
theorem p150FactorPolynomialR11_root_in_interval
    (factor : KFactor) (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hyroot : (p150FactorPolynomialR11 factor).IsRoot y) :
    ∃ q ∈ p150FactorRootIndices11 factor,
      (squaredKRootIntervals40[q.1]!).box.lo ≤ y ∧
      y ≤ (squaredKRootIntervals40[q.1]!).box.hi := by
  rcases p150_factor_interval_or_gap11 factor y hy0 hy1 with
    hinterval | hone | hgap
  · exact hinterval
  · subst y
    exact False.elim
      (p150FactorPolynomialR11_eval_one_ne_zero factor hyroot)
  · rcases hgap with ⟨gap, hgap, hlo, hhi⟩
    exact False.elim
      (p150FactorPolynomialR11_not_isRoot_in_gap factor gap hgap y hlo hhi
        hyroot)

/-- The exact, kernel-checked root isolation certificate consumed by the
P150 coordinate-cover assembly. -/
theorem p150SquaredRootIsolationCertificate11 :
    P150SquaredRootIsolationCertificate11 where
  cover k hk hp := by
    have hy0 : 0 ≤ k ^ 2 := sq_nonneg k
    have hy1 : k ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one k).mpr hk
    rw [Polynomial.IsRoot, p150KR11_eval_factorization] at hp
    have coverFactor : ∀ factor : KFactor,
        (p150FactorPolynomialR11 factor).eval (k ^ 2) = 0 →
        ∃ q : Fin 40,
          squaredKInInterval11 k (squaredKRootIntervals40[q.1]!) := by
      intro factor hfactor
      have hroot : (p150FactorPolynomialR11 factor).IsRoot (k ^ 2) := by
        simpa [Polynomial.IsRoot] using hfactor
      obtain ⟨q, _, hbounds⟩ :=
        p150FactorPolynomialR11_root_in_interval factor (k ^ 2)
          hy0 hy1 hroot
      exact ⟨q, by simpa [squaredKInInterval11] using hbounds⟩
    rcases mul_eq_zero.mp hp with hgf | h40
    · rcases mul_eq_zero.mp hgf with h5 | h30
      · exact coverFactor .g5 h5
      · exact coverFactor .f30 h30
    · exact coverFactor .f40 h40

/-- After root isolation, the hypothesis for the coordinate cover
is the exact H252 phase-elimination replay. -/
theorem p150KRootCoverCertificate11_of_elimination
    (E : H252PhaseEliminationCertificate11) :
    P150KRootCoverCertificate11 :=
  p150KRootCoverCertificate11_of_exact_layers E
    p150SquaredRootIsolationCertificate11
    squaredKIntervalPhaseCenterCertificate11

end

end Biunimodular.F11
