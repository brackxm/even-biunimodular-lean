/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.CoordinateRootEndpointCertificate
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial
noncomputable section

theorem coordinateFactorRootInInterval11 (i : Fin 40) :
    ∃ y : ℝ,
      (squaredKRootIntervals40[i.val]!).box.lo ≤ y ∧
      y ≤ (squaredKRootIntervals40[i.val]!).box.hi ∧
      (p150FactorPolynomialR11 (squaredKRootIntervals40[i.val]!).factor).IsRoot y := by
  let I := squaredKRootIntervals40[i.val]!
  let p := p150FactorPolynomialR11 I.factor
  have h := coordinateRootEndpointCertificate11 i
  have hab : (I.box.lo : ℝ) ≤ I.box.hi := by exact_mod_cast h.2.1.le
  have hprod : p.eval (I.box.lo : ℝ) * p.eval (I.box.hi : ℝ) < 0 := by
    change ((polynomialOfCoefficientsQ11 _).map _).eval _ *
      ((polynomialOfCoefficientsQ11 _).map _).eval _ < 0
    rw [coordinateHornerEvalQ11_real, coordinateHornerEvalQ11_real, ← Rat.cast_mul]
    exact_mod_cast h.2.2.2
  have hcont : ContinuousOn (fun y : ℝ => p.eval y)
      (Set.Icc (I.box.lo : ℝ) I.box.hi) := p.continuous.continuousOn
  have hex : (0 : ℝ) ∈ p.eval '' Set.Icc (I.box.lo : ℝ) I.box.hi := by
    rcases mul_neg_iff.mp hprod with hp | hp
    · exact intermediate_value_Icc' hab hcont ⟨hp.2.le, hp.1.le⟩
    · exact intermediate_value_Icc hab hcont ⟨hp.1.le, hp.2.le⟩
  obtain ⟨y, hy, hz⟩ := hex
  exact ⟨y, hy.1, hy.2, hz⟩

abbrev CoordinateSquaredUnitRoot11 (f : KFactor) :=
  {y : ℝ // 0 < y ∧ y < 1 ∧ (p150FactorPolynomialR11 f).IsRoot y}

def coordinateSquaredRootOfInterval11 (f : KFactor)
    (i : CoordinateFactorIntervalIndex11 f) : CoordinateSquaredUnitRoot11 f := by
  let y := Classical.choose (coordinateFactorRootInInterval11 i.val)
  have hy := Classical.choose_spec (coordinateFactorRootInInterval11 i.val)
  have hb := coordinateRootEndpointCertificate11 i.val
  have htag := p150FactorRootIndices11_tags f i.val i.property
  refine ⟨y, ?_, ?_, ?_⟩
  · have h0 : (0 : ℝ) < (squaredKRootIntervals40[i.val.val]!).box.lo := by
      exact_mod_cast hb.1
    exact h0.trans_le hy.1
  · have h1 : ((squaredKRootIntervals40[i.val.val]!).box.hi : ℝ) < 1 := by
      exact_mod_cast hb.2.2.1
    exact hy.2.1.trans_lt h1
  · exact (congrArg (fun p : ℝ[X] => p.IsRoot y)
      (congrArg p150FactorPolynomialR11 htag)).mp hy.2.2

theorem coordinateSquaredRootOfInterval11_in_interval (f : KFactor)
    (i : CoordinateFactorIntervalIndex11 f) :
    (squaredKRootIntervals40[i.val.val]!).box.lo ≤ (coordinateSquaredRootOfInterval11 f i).val ∧
      (coordinateSquaredRootOfInterval11 f i).val ≤ (squaredKRootIntervals40[i.val.val]!).box.hi := by
  exact ⟨(Classical.choose_spec (coordinateFactorRootInInterval11 i.val)).1,
    (Classical.choose_spec (coordinateFactorRootInInterval11 i.val)).2.1⟩

theorem coordinateSquaredRootOfInterval11_bijective (f : KFactor) :
    Function.Bijective (coordinateSquaredRootOfInterval11 f) := by
  constructor
  · intro i j hij
    by_contra hne
    have hi := coordinateSquaredRootOfInterval11_in_interval f i
    have hj := coordinateSquaredRootOfInterval11_in_interval f j
    have he := congrArg Subtype.val hij
    rcases coordinateFactorIntervals11_separated f i j hne with h | h
    · have hR : ((squaredKRootIntervals40[i.val.val]!).box.hi : ℝ) <
          (squaredKRootIntervals40[j.val.val]!).box.lo := by exact_mod_cast h
      linarith
    · have hR : ((squaredKRootIntervals40[j.val.val]!).box.hi : ℝ) <
          (squaredKRootIntervals40[i.val.val]!).box.lo := by exact_mod_cast h
      linarith
  · intro y
    obtain ⟨i, hi, hy⟩ := p150FactorPolynomialR11_root_in_interval f y.val
      y.property.1.le y.property.2.1.le y.property.2.2
    let j : CoordinateFactorIntervalIndex11 f := ⟨i, hi⟩
    refine ⟨j, Subtype.ext ?_⟩
    have hj := coordinateSquaredRootOfInterval11_in_interval f j
    have htag := p150FactorRootIndices11_tags f i hi
    apply p150FactorPolynomialR11_root_unique_in_interval i _ _ hj.1 hj.2 hy.1 hy.2
    · rw [htag]
      exact (coordinateSquaredRootOfInterval11 f j).property.2.2
    · rw [htag]
      exact y.property.2.2

theorem coordinateSquaredUnitRoot11_card (f : KFactor) :
    Nat.card (CoordinateSquaredUnitRoot11 f) =
      (match f with | .g5 => 5 | .f30 => 15 | .f40 => 20) := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (coordinateSquaredRootOfInterval11_bijective f)),
    Nat.card_eq_fintype_card]
  exact coordinateFactorIntervalIndex11_card f

end
end Biunimodular.F11
