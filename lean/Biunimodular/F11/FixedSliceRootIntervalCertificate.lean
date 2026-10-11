/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceQuotientPolynomial
import Mathlib.Algebra.Polynomial.RuleOfSigns

/-!
# Exact unit-interval root counts for the F11 quotient polynomial

This file proves directly that the sextic `A` factor has exactly three roots
and the octic `B` factor exactly four roots in `(0, 1)`.  The upper bounds use
Descartes' rule of signs after the Mobius substitution `x = t / (1 + t)`;
the lower bounds use rational sign-changing intervals and the intermediate
value theorem.  These results identify the eight split roots of the full
degree-sixteen quotient spectrum without the degree-150 eliminant.
-/

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial Set

noncomputable section

def invariantAR : ℝ[X] :=
  (invariantA.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ)
def invariantBR : ℝ[X] :=
  (invariantB.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℝ)

def invariantAUnitTransformR : ℝ[X] :=
  -70031983*X^6 + 625452688*X^5 + 2224643008*X^4 +
    2211312320*X^3 + 601352192*X^2 - 80109568*X + 692224

def invariantBUnitTransformR : ℝ[X] :=
  128754409*X^8 - 1362096008*X^7 - 5548408400*X^6 -
    5556041728*X^5 + 898648320*X^4 + 3533832192*X^3 +
    815820800*X^2 - 313229312*X + 7929856

theorem invariantAUnitTransformR_signVariations :
    invariantAUnitTransformR.signVariations = 3 := by
  have hcoeff : invariantAUnitTransformR.coeffList =
      [-70031983, 625452688, 2224643008, 2211312320, 601352192,
        -80109568, 692224] := by
    have hdegree : invariantAUnitTransformR.degree = 6 := by
      norm_num [invariantAUnitTransformR]
      compute_degree <;> norm_num
    rw [coeffList, hdegree]
    change [invariantAUnitTransformR.coeff 6,
      invariantAUnitTransformR.coeff 5,
      invariantAUnitTransformR.coeff 4,
      invariantAUnitTransformR.coeff 3,
      invariantAUnitTransformR.coeff 2,
      invariantAUnitTransformR.coeff 1,
      invariantAUnitTransformR.coeff 0] = _
    norm_num [invariantAUnitTransformR]
    norm_num [coeff_X]
  rw [signVariations, hcoeff]
  norm_num [List.signVariations, List.destutter]

theorem invariantBUnitTransformR_signVariations :
    invariantBUnitTransformR.signVariations = 4 := by
  have hcoeff : invariantBUnitTransformR.coeffList =
      [128754409, -1362096008, -5548408400, -5556041728, 898648320,
        3533832192, 815820800, -313229312, 7929856] := by
    have hdegree : invariantBUnitTransformR.degree = 8 := by
      norm_num [invariantBUnitTransformR]
      compute_degree <;> norm_num
    rw [coeffList, hdegree]
    change [invariantBUnitTransformR.coeff 8,
      invariantBUnitTransformR.coeff 7,
      invariantBUnitTransformR.coeff 6,
      invariantBUnitTransformR.coeff 5,
      invariantBUnitTransformR.coeff 4,
      invariantBUnitTransformR.coeff 3,
      invariantBUnitTransformR.coeff 2,
      invariantBUnitTransformR.coeff 1,
      invariantBUnitTransformR.coeff 0] = _
    norm_num [invariantBUnitTransformR]
    norm_num [coeff_X]
  rw [signVariations, hcoeff]
  norm_num [List.signVariations, List.destutter]

theorem invariantAUnitTransformR_eval (x : ℝ) (hx : x ≠ 1) :
    invariantAUnitTransformR.eval (x / (1 - x)) =
      invariantAR.eval x / (1 - x)^6 := by
  norm_num [invariantAUnitTransformR, invariantAR, invariantA]
  field_simp [sub_ne_zero.mpr hx]
  ring

theorem invariantBUnitTransformR_eval (x : ℝ) (hx : x ≠ 1) :
    invariantBUnitTransformR.eval (x / (1 - x)) =
      invariantBR.eval x / (1 - x)^8 := by
  norm_num [invariantBUnitTransformR, invariantBR, invariantB]
  field_simp [sub_ne_zero.mpr hx]
  ring

abbrev AUnitRoot := {x : invariantAR.rootSet ℝ // 0 < (x : ℝ) ∧ (x : ℝ) < 1}
abbrev BUnitRoot := {x : invariantBR.rootSet ℝ // 0 < (x : ℝ) ∧ (x : ℝ) < 1}
abbrev PositiveRoot (p : ℝ[X]) := {x : p.rootSet ℝ // 0 < (x : ℝ)}

theorem positiveRoot_card_le_signVariations (p : ℝ[X]) :
    Fintype.card (PositiveRoot p) ≤ p.signVariations := by
  classical
  let rootsPos : Finset ℝ := p.roots.toFinset.filter fun x => 0 < x
  let f : PositiveRoot p → ↑rootsPos := fun x =>
    ⟨(x.1 : ℝ), by
      rw [show rootsPos = p.roots.toFinset.filter fun x => 0 < x by rfl,
        Finset.mem_filter]
      exact ⟨by simpa [rootSet_def, aroots_def] using x.1.property, x.2⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val h
  calc
    Fintype.card (PositiveRoot p) ≤ Fintype.card ↑rootsPos :=
      Fintype.card_le_of_injective f hf
    _ =
        (p.roots.toFinset.filter fun x => 0 < x).card := by
      rw [Fintype.card_coe]
    _ =
        (p.roots.filter fun x => 0 < x).toFinset.card := by
      rw [Multiset.toFinset_filter]
    _ ≤ (p.roots.filter fun x => 0 < x).card :=
      Multiset.toFinset_card_le _
    _ = p.roots.countP (fun x => 0 < x) := by
      exact (Multiset.countP_eq_card_filter _ _).symm
    _ ≤ p.signVariations := roots_countP_pos_le_signVariations p

noncomputable def aUnitRootToPositiveRoot :
    AUnitRoot → PositiveRoot invariantAUnitTransformR := fun x =>
  ⟨⟨(x : ℝ) / (1 - (x : ℝ)), by
      rw [mem_rootSet]
      refine ⟨?_, ?_⟩
      · intro h
        have heval := congrArg (fun p : ℝ[X] => p.eval 0) h
        norm_num [invariantAUnitTransformR] at heval
      change invariantAUnitTransformR.eval ((x : ℝ) / (1 - (x : ℝ))) = 0
      rw [invariantAUnitTransformR_eval _ x.2.2.ne]
      have hxroot := (mem_rootSet.mp x.1.property).2
      change invariantAR.eval (x : ℝ) = 0 at hxroot
      rw [hxroot]
      simp⟩,
    div_pos x.2.1 (sub_pos.mpr x.2.2)⟩

noncomputable def bUnitRootToPositiveRoot :
    BUnitRoot → PositiveRoot invariantBUnitTransformR := fun x =>
  ⟨⟨(x : ℝ) / (1 - (x : ℝ)), by
      rw [mem_rootSet]
      refine ⟨?_, ?_⟩
      · intro h
        have heval := congrArg (fun p : ℝ[X] => p.eval 0) h
        norm_num [invariantBUnitTransformR] at heval
      change invariantBUnitTransformR.eval ((x : ℝ) / (1 - (x : ℝ))) = 0
      rw [invariantBUnitTransformR_eval _ x.2.2.ne]
      have hxroot := (mem_rootSet.mp x.1.property).2
      change invariantBR.eval (x : ℝ) = 0 at hxroot
      rw [hxroot]
      simp⟩,
    div_pos x.2.1 (sub_pos.mpr x.2.2)⟩

theorem unitMobius_injective {x y : ℝ} (hx : x < 1) (hy : y < 1)
    (h : x / (1 - x) = y / (1 - y)) : x = y := by
  have hcross := (div_eq_div_iff (sub_ne_zero.mpr hx.ne')
    (sub_ne_zero.mpr hy.ne')).mp h
  linear_combination hcross

theorem aUnitRootToPositiveRoot_injective :
    Function.Injective aUnitRootToPositiveRoot := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact unitMobius_injective x.2.2 y.2.2 (congrArg Subtype.val (congrArg Subtype.val h))

theorem bUnitRootToPositiveRoot_injective :
    Function.Injective bUnitRootToPositiveRoot := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact unitMobius_injective x.2.2 y.2.2 (congrArg Subtype.val (congrArg Subtype.val h))

theorem AUnitRoot_card_le : Fintype.card AUnitRoot ≤ 3 := by
  calc
    Fintype.card AUnitRoot ≤ Fintype.card (PositiveRoot invariantAUnitTransformR) :=
      Fintype.card_le_of_injective _ aUnitRootToPositiveRoot_injective
    _ ≤ invariantAUnitTransformR.signVariations :=
      positiveRoot_card_le_signVariations _
    _ = 3 := invariantAUnitTransformR_signVariations

theorem BUnitRoot_card_le : Fintype.card BUnitRoot ≤ 4 := by
  calc
    Fintype.card BUnitRoot ≤ Fintype.card (PositiveRoot invariantBUnitTransformR) :=
      Fintype.card_le_of_injective _ bUnitRootToPositiveRoot_injective
    _ ≤ invariantBUnitTransformR.signVariations :=
      positiveRoot_card_le_signVariations _
    _ = 4 := invariantBUnitTransformR_signVariations

lemma exists_root_between {p : ℝ[X]} {a b : ℝ}
    (hab : a < b) (ha : 0 < p.eval a) (hb : p.eval b < 0) :
    ∃ x : ℝ, a < x ∧ x < b ∧ p.eval x = 0 := by
  have hz : (0 : ℝ) ∈ Icc (p.eval b) (p.eval a) := ⟨hb.le, ha.le⟩
  obtain ⟨x, hx, hpx⟩ :=
    (intermediate_value_Icc' hab.le p.continuous.continuousOn hz)
  refine ⟨x, ?_, ?_, hpx⟩
  · exact hx.1.lt_of_ne (by rintro rfl; simp at hpx; linarith)
  · exact hx.2.lt_of_ne (by rintro rfl; simp at hpx; linarith)

lemma exists_root_between' {p : ℝ[X]} {a b : ℝ}
    (hab : a < b) (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ x : ℝ, a < x ∧ x < b ∧ p.eval x = 0 := by
  obtain ⟨x, hax, hxb, hx⟩ := exists_root_between (p := -p) hab (by simpa) (by simpa)
  exact ⟨x, hax, hxb, by simpa using hx⟩

theorem invariantAR_root_0 :
    ∃ x : ℝ, 0 < x ∧ x < 1/50 ∧ invariantAR.eval x = 0 := by
  apply exists_root_between (by norm_num)
  · norm_num [invariantAR, invariantA]
  · norm_num [invariantAR, invariantA]

theorem invariantAR_root_1 :
    ∃ x : ℝ, 1/20 < x ∧ x < 1/10 ∧ invariantAR.eval x = 0 := by
  apply exists_root_between' (by norm_num)
  · norm_num [invariantAR, invariantA]
  · norm_num [invariantAR, invariantA]

theorem invariantAR_root_2 :
    ∃ x : ℝ, 9/10 < x ∧ x < 19/20 ∧ invariantAR.eval x = 0 := by
  apply exists_root_between (by norm_num)
  · norm_num [invariantAR, invariantA]
  · norm_num [invariantAR, invariantA]

theorem invariantBR_root_0 :
    ∃ x : ℝ, 1/50 < x ∧ x < 1/25 ∧ invariantBR.eval x = 0 := by
  apply exists_root_between (by norm_num)
  · norm_num [invariantBR, invariantB]
  · norm_num [invariantBR, invariantB]

theorem invariantBR_root_1 :
    ∃ x : ℝ, 3/20 < x ∧ x < 4/25 ∧ invariantBR.eval x = 0 := by
  apply exists_root_between' (by norm_num)
  · norm_num [invariantBR, invariantB]
  · norm_num [invariantBR, invariantB]

theorem invariantBR_root_2 :
    ∃ x : ℝ, 2/5 < x ∧ x < 41/100 ∧ invariantBR.eval x = 0 := by
  apply exists_root_between (by norm_num)
  · norm_num [invariantBR, invariantB]
  · norm_num [invariantBR, invariantB]

theorem invariantBR_root_3 :
    ∃ x : ℝ, 93/100 < x ∧ x < 47/50 ∧ invariantBR.eval x = 0 := by
  apply exists_root_between' (by norm_num)
  · norm_num [invariantBR, invariantB]
  · norm_num [invariantBR, invariantB]

private theorem invariantAR_ne_zero : invariantAR ≠ 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 0) h
  norm_num [invariantAR, invariantA] at heval

private theorem invariantBR_ne_zero : invariantBR ≠ 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 0) h
  norm_num [invariantBR, invariantB] at heval

noncomputable def aUnitRoot0 : AUnitRoot := by
  let x := Classical.choose invariantAR_root_0
  have hx := Classical.choose_spec invariantAR_root_0
  exact ⟨⟨x, by
    rw [mem_rootSet]
    exact ⟨invariantAR_ne_zero, hx.2.2⟩⟩,
    hx.1, lt_trans hx.2.1 (by norm_num)⟩

theorem aUnitRoot0_bounds :
    (0 : ℝ) < aUnitRoot0 ∧ (aUnitRoot0 : ℝ) < 1/50 := by
  exact ⟨(Classical.choose_spec invariantAR_root_0).1,
    (Classical.choose_spec invariantAR_root_0).2.1⟩

noncomputable def aUnitRoot1 : AUnitRoot := by
  let x := Classical.choose invariantAR_root_1
  have hx := Classical.choose_spec invariantAR_root_1
  exact ⟨⟨x, by
    rw [mem_rootSet]
    exact ⟨invariantAR_ne_zero, hx.2.2⟩⟩,
    lt_trans (by norm_num) hx.1, lt_trans hx.2.1 (by norm_num)⟩

theorem aUnitRoot1_bounds :
    (1/20 : ℝ) < aUnitRoot1 ∧ (aUnitRoot1 : ℝ) < 1/10 := by
  exact ⟨(Classical.choose_spec invariantAR_root_1).1,
    (Classical.choose_spec invariantAR_root_1).2.1⟩

noncomputable def aUnitRoot2 : AUnitRoot := by
  let x := Classical.choose invariantAR_root_2
  have hx := Classical.choose_spec invariantAR_root_2
  exact ⟨⟨x, by
    rw [mem_rootSet]
    exact ⟨invariantAR_ne_zero, hx.2.2⟩⟩,
    lt_trans (by norm_num) hx.1, lt_trans hx.2.1 (by norm_num)⟩

theorem aUnitRoot2_bounds :
    (9/10 : ℝ) < aUnitRoot2 ∧ (aUnitRoot2 : ℝ) < 19/20 := by
  exact ⟨(Classical.choose_spec invariantAR_root_2).1,
    (Classical.choose_spec invariantAR_root_2).2.1⟩

noncomputable def bUnitRoot0 : BUnitRoot := by
  let x := Classical.choose invariantBR_root_0
  have hx := Classical.choose_spec invariantBR_root_0
  exact ⟨⟨x, by
    rw [mem_rootSet]
    exact ⟨invariantBR_ne_zero, hx.2.2⟩⟩,
    lt_trans (by norm_num) hx.1, lt_trans hx.2.1 (by norm_num)⟩

theorem bUnitRoot0_bounds :
    (1/50 : ℝ) < bUnitRoot0 ∧ (bUnitRoot0 : ℝ) < 1/25 := by
  exact ⟨(Classical.choose_spec invariantBR_root_0).1,
    (Classical.choose_spec invariantBR_root_0).2.1⟩

noncomputable def bUnitRoot1 : BUnitRoot := by
  let x := Classical.choose invariantBR_root_1
  have hx := Classical.choose_spec invariantBR_root_1
  exact ⟨⟨x, by
    rw [mem_rootSet]
    exact ⟨invariantBR_ne_zero, hx.2.2⟩⟩,
    lt_trans (by norm_num) hx.1, lt_trans hx.2.1 (by norm_num)⟩

theorem bUnitRoot1_bounds :
    (3/20 : ℝ) < bUnitRoot1 ∧ (bUnitRoot1 : ℝ) < 4/25 := by
  exact ⟨(Classical.choose_spec invariantBR_root_1).1,
    (Classical.choose_spec invariantBR_root_1).2.1⟩

noncomputable def bUnitRoot2 : BUnitRoot := by
  let x := Classical.choose invariantBR_root_2
  have hx := Classical.choose_spec invariantBR_root_2
  exact ⟨⟨x, by
    rw [mem_rootSet]
    exact ⟨invariantBR_ne_zero, hx.2.2⟩⟩,
    lt_trans (by norm_num) hx.1, lt_trans hx.2.1 (by norm_num)⟩

theorem bUnitRoot2_bounds :
    (2/5 : ℝ) < bUnitRoot2 ∧ (bUnitRoot2 : ℝ) < 41/100 := by
  exact ⟨(Classical.choose_spec invariantBR_root_2).1,
    (Classical.choose_spec invariantBR_root_2).2.1⟩

noncomputable def bUnitRoot3 : BUnitRoot := by
  let x := Classical.choose invariantBR_root_3
  have hx := Classical.choose_spec invariantBR_root_3
  exact ⟨⟨x, by
    rw [mem_rootSet]
    exact ⟨invariantBR_ne_zero, hx.2.2⟩⟩,
    lt_trans (by norm_num) hx.1, lt_trans hx.2.1 (by norm_num)⟩

theorem bUnitRoot3_bounds :
    (93/100 : ℝ) < bUnitRoot3 ∧ (bUnitRoot3 : ℝ) < 47/50 := by
  exact ⟨(Classical.choose_spec invariantBR_root_3).1,
    (Classical.choose_spec invariantBR_root_3).2.1⟩

private theorem unitRoot_ne_of_lt {p : ℝ[X]}
    {x y : {z : p.rootSet ℝ // 0 < (z : ℝ) ∧ (z : ℝ) < 1}}
    (h : (x : ℝ) < (y : ℝ)) : x ≠ y := by
  intro hxy
  have hv : (x : ℝ) = (y : ℝ) := congrArg
    (fun z : {z : p.rootSet ℝ // 0 < (z : ℝ) ∧ (z : ℝ) < 1} =>
      (z.1.1 : ℝ)) hxy
  exact h.ne hv

theorem AUnitRoot_card_ge : 3 ≤ Fintype.card AUnitRoot := by
  have h01 : (aUnitRoot0 : ℝ) < aUnitRoot1 := by
    linarith [aUnitRoot0_bounds, aUnitRoot1_bounds]
  have h12 : (aUnitRoot1 : ℝ) < aUnitRoot2 := by
    linarith [aUnitRoot1_bounds, aUnitRoot2_bounds]
  have h02 : (aUnitRoot0 : ℝ) < aUnitRoot2 := h01.trans h12
  let s : Finset AUnitRoot := {aUnitRoot0, aUnitRoot1, aUnitRoot2}
  have hs : s.card = 3 := by
    simp [s, unitRoot_ne_of_lt h01, unitRoot_ne_of_lt h02,
      unitRoot_ne_of_lt h12]
  rw [← hs]
  exact Finset.card_le_univ s

theorem BUnitRoot_card_ge : 4 ≤ Fintype.card BUnitRoot := by
  have h01 : (bUnitRoot0 : ℝ) < bUnitRoot1 := by
    linarith [bUnitRoot0_bounds, bUnitRoot1_bounds]
  have h12 : (bUnitRoot1 : ℝ) < bUnitRoot2 := by
    linarith [bUnitRoot1_bounds, bUnitRoot2_bounds]
  have h23 : (bUnitRoot2 : ℝ) < bUnitRoot3 := by
    linarith [bUnitRoot2_bounds, bUnitRoot3_bounds]
  have h02 := h01.trans h12
  have h03 := h02.trans h23
  have h13 := h12.trans h23
  let s : Finset BUnitRoot := {bUnitRoot0, bUnitRoot1, bUnitRoot2, bUnitRoot3}
  have hs : s.card = 4 := by
    simp [s, unitRoot_ne_of_lt h01, unitRoot_ne_of_lt h02,
      unitRoot_ne_of_lt h03, unitRoot_ne_of_lt h12,
      unitRoot_ne_of_lt h13, unitRoot_ne_of_lt h23]
  rw [← hs]
  exact Finset.card_le_univ s

theorem AUnitRoot_card : Fintype.card AUnitRoot = 3 :=
  Nat.le_antisymm AUnitRoot_card_le AUnitRoot_card_ge

theorem BUnitRoot_card : Fintype.card BUnitRoot = 4 :=
  Nat.le_antisymm BUnitRoot_card_le BUnitRoot_card_ge

abbrev AComplexUnitRoot :=
  {z : FixedSliceAQuotientRoot //
    z.1.im = 0 ∧ 0 < z.1.re ∧ z.1.re < 1}

abbrev BComplexUnitRoot :=
  {z : FixedSliceBQuotientRoot //
    z.1.im = 0 ∧ 0 < z.1.re ∧ z.1.re < 1}

noncomputable def realToComplexQAlgHom : ℝ →ₐ[ℚ] ℂ where
  toFun := Complex.ofReal
  map_one' := by simp
  map_mul' := by simp
  map_zero' := by simp
  map_add' := by simp
  commutes' q := by norm_num

noncomputable def aUnitRootComplexEquiv : AUnitRoot ≃ AComplexUnitRoot where
  toFun x := ⟨⟨(x : ℝ), by
    apply rootSet_mapsTo realToComplexQAlgHom
    simpa [invariantAR] using x.1.property⟩,
    by simp, by simpa using x.2.1, by simpa using x.2.2⟩
  invFun z := ⟨⟨z.1.1.re, by
    rw [mem_rootSet]
    refine ⟨invariantAR_ne_zero, ?_⟩
    have hzroot : ((invariantA.map (Int.castRingHom ℚ)).map
        (algebraMap ℚ ℂ)).IsRoot z.1.1 := by
      simpa [IsRoot] using (mem_rootSet.mp z.1.property).2
    have hz : z.1.1 = (z.1.1.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using z.2.1
    rw [hz] at hzroot
    have hmap : invariantAR.map Complex.ofRealHom =
        (invariantA.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) := by
      norm_num [invariantAR, invariantA]
    rw [← hmap] at hzroot
    exact hzroot.of_map Complex.ofReal_injective⟩,
    z.2.2.1, z.2.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Complex.ext (by simp) (by simpa using z.2.1)).symm

noncomputable def bUnitRootComplexEquiv : BUnitRoot ≃ BComplexUnitRoot where
  toFun x := ⟨⟨(x : ℝ), by
    apply rootSet_mapsTo realToComplexQAlgHom
    simpa [invariantBR] using x.1.property⟩,
    by simp, by simpa using x.2.1, by simpa using x.2.2⟩
  invFun z := ⟨⟨z.1.1.re, by
    rw [mem_rootSet]
    refine ⟨invariantBR_ne_zero, ?_⟩
    have hzroot : ((invariantB.map (Int.castRingHom ℚ)).map
        (algebraMap ℚ ℂ)).IsRoot z.1.1 := by
      simpa [IsRoot] using (mem_rootSet.mp z.1.property).2
    have hz : z.1.1 = (z.1.1.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using z.2.1
    rw [hz] at hzroot
    have hmap : invariantBR.map Complex.ofRealHom =
        (invariantB.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) := by
      norm_num [invariantBR, invariantB]
    rw [← hmap] at hzroot
    exact hzroot.of_map Complex.ofReal_injective⟩,
    z.2.2.1, z.2.2.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Complex.ext (by simp) (by simpa using z.2.1)).symm

theorem AComplexUnitRoot_card : Fintype.card AComplexUnitRoot = 3 := by
  rw [Fintype.card_congr aUnitRootComplexEquiv.symm]
  exact AUnitRoot_card

theorem BComplexUnitRoot_card : Fintype.card BComplexUnitRoot = 4 := by
  rw [Fintype.card_congr bUnitRootComplexEquiv.symm]
  exact BUnitRoot_card

def FixedSliceQuotientSectorRoot.IsAdmissible :
    FixedSliceQuotientSectorRoot → Prop
  | .gaussian => True
  | .constant => False
  | .A root => root.1.im = 0 ∧ 0 < root.1.re ∧ root.1.re < 1
  | .B root => root.1.im = 0 ∧ 0 < root.1.re ∧ root.1.re < 1

instance (s : FixedSliceQuotientSectorRoot) : Decidable s.IsAdmissible := by
  cases s <;> simp only [FixedSliceQuotientSectorRoot.IsAdmissible] <;>
    infer_instance

abbrev FixedSliceAdmissibleSectorRoot :=
  {s : FixedSliceQuotientSectorRoot // s.IsAdmissible}

noncomputable def fixedSliceAdmissibleSectorRootEquiv :
    FixedSliceAdmissibleSectorRoot ≃ Unit ⊕ (AComplexUnitRoot ⊕ BComplexUnitRoot) where
  toFun s := by
    rcases s with ⟨s, hs⟩
    cases s with
    | gaussian => exact Sum.inl ()
    | constant => exact False.elim hs
    | A root => exact Sum.inr (Sum.inl ⟨root, hs⟩)
    | B root => exact Sum.inr (Sum.inr ⟨root, hs⟩)
  invFun s := by
    rcases s with (_ | a | b)
    · exact ⟨.gaussian, trivial⟩
    · exact ⟨.A a.1, a.2⟩
    · exact ⟨.B b.1, b.2⟩
  left_inv s := by
    rcases s with ⟨s, hs⟩
    cases s with
    | gaussian => rfl
    | constant => exact False.elim hs
    | A root => rfl
    | B root => rfl
  right_inv s := by
    rcases s with (_ | a | b) <;> rfl

theorem fixedSliceAdmissibleSectorRoot_card :
    Fintype.card FixedSliceAdmissibleSectorRoot = 8 := by
  rw [Fintype.card_congr fixedSliceAdmissibleSectorRootEquiv,
    Fintype.card_sum, Fintype.card_sum, AComplexUnitRoot_card,
    BComplexUnitRoot_card]
  norm_num

private theorem fixedSliceAQuotientRoot_ne_zero
    (root : FixedSliceAQuotientRoot) : (root : ℂ) ≠ 0 := by
  intro hzero
  have hroot := (mem_rootSet.mp root.property).2
  rw [hzero] at hroot
  norm_num [aeval_def, invariantA] at hroot

private theorem fixedSliceBQuotientRoot_ne_zero
    (root : FixedSliceBQuotientRoot) : (root : ℂ) ≠ 0 := by
  intro hzero
  have hroot := (mem_rootSet.mp root.property).2
  rw [hzero] at hroot
  norm_num [aeval_def, invariantB] at hroot

theorem fixedSliceQuotientSectorRoot_admissible_iff
    (s : FixedSliceQuotientSectorRoot) :
    s.IsAdmissible ↔
      (fixedSliceQuotientSectorRootValue s : ℂ).im = 0 ∧
      0 ≤ (fixedSliceQuotientSectorRootValue s : ℂ).re ∧
      (fixedSliceQuotientSectorRootValue s : ℂ).re < 1 := by
  cases s with
  | gaussian => norm_num [FixedSliceQuotientSectorRoot.IsAdmissible,
      fixedSliceQuotientSectorRootValue]
  | constant => norm_num [FixedSliceQuotientSectorRoot.IsAdmissible,
      fixedSliceQuotientSectorRootValue]
  | A root =>
      simp only [FixedSliceQuotientSectorRoot.IsAdmissible,
        fixedSliceQuotientSectorRootValue]
      constructor
      · rintro ⟨him, hpos, hlt⟩
        exact ⟨him, hpos.le, hlt⟩
      · rintro ⟨him, hnonneg, hlt⟩
        refine ⟨him, hnonneg.lt_of_ne ?_, hlt⟩
        intro hre
        apply fixedSliceAQuotientRoot_ne_zero root
        apply Complex.ext
        · simpa using hre.symm
        · simpa using him
  | B root =>
      simp only [FixedSliceQuotientSectorRoot.IsAdmissible,
        fixedSliceQuotientSectorRootValue]
      constructor
      · rintro ⟨him, hpos, hlt⟩
        exact ⟨him, hpos.le, hlt⟩
      · rintro ⟨him, hnonneg, hlt⟩
        refine ⟨him, hnonneg.lt_of_ne ?_, hlt⟩
        intro hre
        apply fixedSliceBQuotientRoot_ne_zero root
        apply Complex.ext
        · simpa using hre.symm
        · simpa using him

/-- A quotient-polynomial root is split precisely when its factor-tagged value
is real and lies in the physical interval `0 ≤ u < 1`. -/
noncomputable def fixedSliceQuotientRootSplit
    (r : FixedSliceQuotientRoot) : Prop :=
  (fixedSliceQuotientSectorRootEquiv.symm r).IsAdmissible

theorem fixedSliceQuotientRootSplit_iff (r : FixedSliceQuotientRoot) :
    fixedSliceQuotientRootSplit r ↔
      (r : ℂ).im = 0 ∧ 0 ≤ (r : ℂ).re ∧ (r : ℂ).re < 1 := by
  unfold fixedSliceQuotientRootSplit
  rw [fixedSliceQuotientSectorRoot_admissible_iff]
  have h := fixedSliceQuotientSectorRootEquiv.apply_symm_apply r
  change fixedSliceQuotientSectorRootValue
    (fixedSliceQuotientSectorRootEquiv.symm r) = r at h
  rw [h]

instance (r : FixedSliceQuotientRoot) :
    Decidable (fixedSliceQuotientRootSplit r) := by
  unfold fixedSliceQuotientRootSplit
  infer_instance

abbrev SplitQuotientRoot :=
  {r : FixedSliceQuotientRoot // fixedSliceQuotientRootSplit r}

noncomputable def splitQuotientRootSectorEquiv :
    SplitQuotientRoot ≃ FixedSliceAdmissibleSectorRoot where
  toFun r := ⟨fixedSliceQuotientSectorRootEquiv.symm r.1, r.2⟩
  invFun s := ⟨fixedSliceQuotientSectorRootEquiv s.1, by
    simpa [fixedSliceQuotientRootSplit] using s.2⟩
  left_inv r := by
    apply Subtype.ext
    simp
  right_inv s := by
    apply Subtype.ext
    simp

theorem splitQuotientRoot_card :
    Fintype.card SplitQuotientRoot = 8 := by
  rw [Fintype.card_congr splitQuotientRootSectorEquiv]
  exact fixedSliceAdmissibleSectorRoot_card

/-- The unique Gaussian point in the admissible quotient spectrum. -/
noncomputable def gaussianSplitQuotientRoot : SplitQuotientRoot :=
  ⟨fixedSliceQuotientSectorRootEquiv .gaussian, by
    simp [fixedSliceQuotientRootSplit,
      FixedSliceQuotientSectorRoot.IsAdmissible]⟩

theorem gaussianSplitQuotientRoot_value :
    ((gaussianSplitQuotientRoot : SplitQuotientRoot) : ℂ) = 0 := by
  rfl

theorem splitQuotientRoot_eq_gaussian_iff (r : SplitQuotientRoot) :
    r = gaussianSplitQuotientRoot ↔ (r : ℂ) = 0 := by
  constructor
  · rintro rfl
    exact gaussianSplitQuotientRoot_value
  · intro hzero
    apply Subtype.ext
    apply Subtype.ext
    exact hzero.trans gaussianSplitQuotientRoot_value.symm

/-- Non-Gaussian admissible roots are the complement of `u = 0`. -/
abbrev NonGaussianSplitQuotientRoot :=
  {r : SplitQuotientRoot // r ≠ gaussianSplitQuotientRoot}

theorem nonGaussianSplitQuotientRoot_card :
    Fintype.card NonGaussianSplitQuotientRoot = 7 := by
  classical
  rw [Fintype.card_subtype_compl
    (fun r : SplitQuotientRoot => r = gaussianSplitQuotientRoot),
    splitQuotientRoot_card,
    Fintype.card_subtype_eq gaussianSplitQuotientRoot]

end
end Biunimodular.F11
