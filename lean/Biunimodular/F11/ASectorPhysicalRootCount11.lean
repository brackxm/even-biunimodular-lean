/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPhysicalRootCoverage11

set_option autoImplicit false

namespace Biunimodular.F11

/-- Indices of the fifteen exact isolating intervals for physical F30 roots. -/
abbrev F30PhysicalRootIntervalIndex11 :=
  {i : Fin 40 // i ∈ p150FactorRootIndices11 .f30}

theorem f30PhysicalRootIntervalIndex11_card :
    Fintype.card F30PhysicalRootIntervalIndex11 = 15 := by
  native_decide

/-- Distinct tagged F30 intervals have disjoint rational closures. -/
theorem f30PhysicalRootIntervals11_separated :
    ∀ i j : F30PhysicalRootIntervalIndex11, i ≠ j →
      (squaredKRootIntervals40[i.1.1]!).box.hi <
        (squaredKRootIntervals40[j.1.1]!).box.lo ∨
      (squaredKRootIntervals40[j.1.1]!).box.hi <
        (squaredKRootIntervals40[i.1.1]!).box.lo := by
  native_decide

/-- Real roots of F30 in the squared unit-circle range. -/
abbrev F30PhysicalRoot11 :=
  {y : ℝ // 0 ≤ y ∧ y ≤ 1 ∧
    (p150FactorPolynomialR11 .f30).IsRoot y}

noncomputable def f30PhysicalRootOfInterval11
    (i : F30PhysicalRootIntervalIndex11) : F30PhysicalRoot11 := by
  let s := Classical.choose (everyF30RootInterval_physically_realized11 i.1 i.2)
  have hs := Classical.choose_spec
    (everyF30RootInterval_physically_realized11 i.1 i.2)
  have hcircle := s.2.1.2.2.2.2
  refine ⟨s.1.k ^ 2, sq_nonneg _, ?_, hs.2.2⟩
  nlinarith [sq_nonneg s.1.j]

theorem f30PhysicalRootOfInterval11_in_interval
    (i : F30PhysicalRootIntervalIndex11) :
    ((squaredKRootIntervals40[i.1.1]!).box.lo : ℝ) ≤
        (f30PhysicalRootOfInterval11 i).1 ∧
      (f30PhysicalRootOfInterval11 i).1 ≤
        ((squaredKRootIntervals40[i.1.1]!).box.hi : ℝ) := by
  have hs := Classical.choose_spec
    (everyF30RootInterval_physically_realized11 i.1 i.2)
  exact hs.2.1

theorem f30PhysicalRootOfInterval11_injective :
    Function.Injective f30PhysicalRootOfInterval11 := by
  intro i j hij
  by_contra hne
  have hi := f30PhysicalRootOfInterval11_in_interval i
  have hj := f30PhysicalRootOfInterval11_in_interval j
  have heq := congrArg Subtype.val hij
  rcases f30PhysicalRootIntervals11_separated i j hne with hsep | hsep
  · have hsepR : ((squaredKRootIntervals40[i.1.1]!).box.hi : ℝ) <
        ((squaredKRootIntervals40[j.1.1]!).box.lo : ℝ) := by
      exact_mod_cast hsep
    linarith
  · have hsepR : ((squaredKRootIntervals40[j.1.1]!).box.hi : ℝ) <
        ((squaredKRootIntervals40[i.1.1]!).box.lo : ℝ) := by
      exact_mod_cast hsep
    linarith

theorem f30PhysicalRootOfInterval11_surjective :
    Function.Surjective f30PhysicalRootOfInterval11 := by
  intro y
  obtain ⟨i, hi, hybox⟩ := p150FactorPolynomialR11_root_in_interval
    .f30 y.1 y.2.1 y.2.2.1 y.2.2.2
  let index : F30PhysicalRootIntervalIndex11 := ⟨i, hi⟩
  refine ⟨index, ?_⟩
  apply Subtype.ext
  have hbox := f30PhysicalRootOfInterval11_in_interval index
  have htag := p150FactorRootIndices11_tags .f30 i hi
  apply p150FactorPolynomialR11_root_unique_in_interval i
    (f30PhysicalRootOfInterval11 index).1 y.1
      hbox.1 hbox.2 hybox.1 hybox.2
  · rw [htag]
    exact (f30PhysicalRootOfInterval11 index).2.2.2
  · rw [htag]
    exact y.2.2.2

/-- The fifteen exact intervals enumerate all physical F30 roots. -/
noncomputable def f30PhysicalRootIntervalEquiv11 :
    F30PhysicalRootIntervalIndex11 ≃ F30PhysicalRoot11 :=
  Equiv.ofBijective f30PhysicalRootOfInterval11
    ⟨f30PhysicalRootOfInterval11_injective,
      f30PhysicalRootOfInterval11_surjective⟩

theorem f30PhysicalRoot11_natCard : Nat.card F30PhysicalRoot11 = 15 := by
  rw [← Nat.card_congr f30PhysicalRootIntervalEquiv11]
  simpa only [Nat.card_eq_fintype_card] using
    f30PhysicalRootIntervalIndex11_card

/-- Real G30 roots in the scaled physical range. -/
abbrev G30PhysicalRoot11 :=
  {x : ℝ // 0 ≤ x ∧ x ≤ 4 ∧
    (aSectorG30.map (Int.castRingHom ℝ)).IsRoot x}

noncomputable def g30PhysicalRootEquivF30PhysicalRoot11 :
    G30PhysicalRoot11 ≃ F30PhysicalRoot11 where
  toFun x := ⟨x.1 / 4, by
    refine ⟨div_nonneg x.2.1 (by norm_num), by linarith [x.2.2.1], ?_⟩
    rw [Polynomial.IsRoot, p150F30_factor_eval_eq_G30_scaled]
    simpa only [show 4 * (x.1 / 4) = x.1 by ring] using x.2.2.2.eq_zero⟩
  invFun y := ⟨4 * y.1, by
    refine ⟨mul_nonneg (by norm_num) y.2.1, by linarith [y.2.2.1], ?_⟩
    have h := y.2.2.2.eq_zero
    rw [p150F30_factor_eval_eq_G30_scaled] at h
    exact h⟩
  left_inv x := by apply Subtype.ext; dsimp; ring
  right_inv y := by apply Subtype.ext; dsimp; ring

/-- Exactly fifteen of the thirty G30 conjugates lie in the physical range. -/
theorem g30PhysicalRoot11_natCard : Nat.card G30PhysicalRoot11 = 15 := by
  rw [Nat.card_congr g30PhysicalRootEquivF30PhysicalRoot11]
  exact f30PhysicalRoot11_natCard

end Biunimodular.F11
