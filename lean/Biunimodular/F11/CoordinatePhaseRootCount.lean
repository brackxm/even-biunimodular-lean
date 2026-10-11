/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateSquaredRootCount

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial
noncomputable section

def coordinatePhaseFactorQ11 (f : KFactor) : ℚ[X] :=
  (p150FactorPolynomialQ11 f).comp (X ^ 2)

def coordinatePhaseFactorR11 (f : KFactor) : ℝ[X] :=
  (coordinatePhaseFactorQ11 f).map (algebraMap ℚ ℝ)

theorem coordinatePhaseFactorR11_eval (f : KFactor) (k : ℝ) :
    (coordinatePhaseFactorR11 f).eval k = (p150FactorPolynomialR11 f).eval (k ^ 2) := by
  simp [coordinatePhaseFactorR11, coordinatePhaseFactorQ11, p150FactorPolynomialR11,
    Polynomial.map_comp, Polynomial.eval_comp]

abbrev CoordinatePhaseUnitRoot11 (f : KFactor) :=
  {k : ℝ // -1 < k ∧ k < 1 ∧ (coordinatePhaseFactorR11 f).IsRoot k}

theorem coordinatePhaseUnitRoot11_square (f : KFactor) (k : CoordinatePhaseUnitRoot11 f) :
    0 < k.val ^ 2 ∧ k.val ^ 2 < 1 ∧ (p150FactorPolynomialR11 f).IsRoot (k.val ^ 2) := by
  have hr := k.property.2.2
  rw [Polynomial.IsRoot, coordinatePhaseFactorR11_eval] at hr
  have hsq : k.val ^ 2 < 1 := by nlinarith [k.property.1, k.property.2.1]
  obtain ⟨i, _, hi⟩ := p150FactorPolynomialR11_root_in_interval f (k.val ^ 2)
    (sq_nonneg _) hsq.le hr
  have h0 : (0 : ℝ) < (squaredKRootIntervals40[i.val]!).box.lo := by
    exact_mod_cast (coordinateRootEndpointCertificate11 i).1
  exact ⟨h0.trans_le hi.1, hsq, hr⟩

def coordinatePhaseRootSignSquare11 (f : KFactor) (k : CoordinatePhaseUnitRoot11 f) :
    Bool × CoordinateSquaredUnitRoot11 f :=
  (decide (0 < k.val), ⟨k.val ^ 2, coordinatePhaseUnitRoot11_square f k⟩)

def coordinatePhaseRootFromSignSquare11 (f : KFactor)
    (p : Bool × CoordinateSquaredUnitRoot11 f) : CoordinatePhaseUnitRoot11 f := by
  let k := Real.sqrt p.2.val
  have hk0 : 0 < k := Real.sqrt_pos.mpr p.2.property.1
  have hksq : k ^ 2 = p.2.val := Real.sq_sqrt p.2.property.1.le
  have hk1 : k < 1 := by nlinarith [p.2.property.2.1]
  refine ⟨if p.1 then k else -k, ?_, ?_, ?_⟩
  · cases p.1 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  · cases p.1 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  · rw [Polynomial.IsRoot, coordinatePhaseFactorR11_eval]
    cases p.1 <;> simpa only [Bool.false_eq_true, ↓reduceIte, neg_sq, hksq, Polynomial.IsRoot]
      using p.2.property.2.2

def coordinatePhaseRootSignSquareEquiv11 (f : KFactor) :
    CoordinatePhaseUnitRoot11 f ≃ Bool × CoordinateSquaredUnitRoot11 f where
  toFun := coordinatePhaseRootSignSquare11 f
  invFun := coordinatePhaseRootFromSignSquare11 f
  left_inv k := by
    apply Subtype.ext
    change (if decide (0 < k.val) then Real.sqrt (k.val ^ 2) else -Real.sqrt (k.val ^ 2)) = k.val
    have hne : k.val ≠ 0 := by
      intro h
      have hp := (coordinatePhaseUnitRoot11_square f k).1
      simp [h] at hp
    by_cases hp : 0 < k.val
    · simp [hp, Real.sqrt_sq hp.le]
    · have hn : k.val < 0 := lt_of_le_of_ne (le_of_not_gt hp) hne
      simp [hp, Real.sqrt_sq_eq_abs, abs_of_neg hn]
  right_inv p := by
    rcases p with ⟨b, y⟩
    have hk : 0 < Real.sqrt y.val := Real.sqrt_pos.mpr y.property.1
    have hs : (Real.sqrt y.val) ^ 2 = y.val := Real.sq_sqrt y.property.1.le
    apply Prod.ext
    · cases b <;> simp [coordinatePhaseRootSignSquare11, coordinatePhaseRootFromSignSquare11,
        hk, show ¬0 < -Real.sqrt y.val by linarith]
    · apply Subtype.ext
      cases b <;> simp [coordinatePhaseRootSignSquare11, coordinatePhaseRootFromSignSquare11, hs]

theorem coordinatePhaseUnitRoot11_card (f : KFactor) :
    Nat.card (CoordinatePhaseUnitRoot11 f) =
      (match f with | .g5 => 10 | .f30 => 30 | .f40 => 40) := by
  rw [Nat.card_congr (coordinatePhaseRootSignSquareEquiv11 f), Nat.card_prod,
    coordinateSquaredUnitRoot11_card]
  cases f <;> norm_num

end
end Biunimodular.F11
