/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.DegreeEight875FiniteCertificates
import Mathlib.GroupTheory.GroupAction.Jordan

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Biunimodular.F11

theorem s8_eight_point_transitive :
    ∀ x y : Fin 8, ∃ n ∈ Finset.range 8, (s8CanonicalEight ^ n) x = y := by
  native_decide

private theorem s8_seven_point_transitive :
    ∀ b : Equiv.Perm (Fin 8),
      b.support.card = 7 → b ^ 7 = 1 → b 7 = 7 →
      ∀ x y : Fin 8, x ≠ 7 → y ≠ 7 →
        ∃ n ∈ Finset.range 7, (b ^ n) x = y := by
  native_decide

private theorem s8_seven_fixed_pow (b : Equiv.Perm (Fin 8))
    (hb : b 7 = 7) (n : ℕ) : (b ^ n) 7 = 7 := by
  induction n with
  | zero => simp
  | succ n ih => simpa [pow_succ, Equiv.Perm.mul_apply, hb] using ih

private theorem s8_pair_primitive (H : Subgroup (Equiv.Perm (Fin 8)))
    (ha : s8CanonicalEight ∈ H) (b : Equiv.Perm (Fin 8))
    (hb : b ∈ H) (hb7 : b.support.card = 7)
    (hborder : b ^ 7 = 1) (hbfix : b 7 = 7) :
    MulAction.IsPreprimitive H (Fin 8) := by
  apply MulAction.isPreprimitive_of_is_two_pretransitive
  rw [MulAction.is_two_pretransitive_iff]
  intro x y u v hxy huv
  obtain ⟨i, -, hi⟩ := s8_eight_point_transitive x 7
  obtain ⟨j, -, hj⟩ := s8_eight_point_transitive u 7
  have hiy : (s8CanonicalEight ^ i) y ≠ 7 := by
    intro heq
    exact hxy ((s8CanonicalEight ^ i).injective (hi.trans heq.symm))
  have hjv : (s8CanonicalEight ^ j) v ≠ 7 := by
    intro heq
    exact huv ((s8CanonicalEight ^ j).injective (hj.trans heq.symm))
  obtain ⟨n, -, hn⟩ :=
    s8_seven_point_transitive b hb7 hborder hbfix _ _ hiy hjv
  refine ⟨⟨(s8CanonicalEight ^ j)⁻¹ * b ^ n * s8CanonicalEight ^ i,
    H.mul_mem (H.mul_mem (H.inv_mem (H.pow_mem ha _)) (H.pow_mem hb _))
      (H.pow_mem ha _)⟩, ?_, ?_⟩
  · simp [Equiv.Perm.mul_apply, hi, s8_seven_fixed_pow b hbfix]
    rw [← hj]
    simp
  · simp [Equiv.Perm.mul_apply, hn]

private theorem s8_word_mem (H : Subgroup (Equiv.Perm (Fin 8)))
    (a b : Equiv.Perm (Fin 8)) (ha : a ∈ H) (hb : b ∈ H)
    (w : S8Word) : s8EvalWord a b w ∈ H := by
  have hletter : ∀ n, s8WordLetter a b n ∈ H := by
    intro n
    cases n with
    | zero => exact ha
    | succ n =>
      cases n with
      | zero => exact H.inv_mem ha
      | succ n =>
        cases n with
        | zero => exact hb
        | succ n => exact H.inv_mem hb
  have hfold : ∀ (p : Equiv.Perm (Fin 8)) (hp : p ∈ H),
      (w.foldl (fun q n => q * s8WordLetter a b n) p) ∈ H := by
    induction w with
    | nil => intro p hp; simpa using hp
    | cons n w ih =>
      intro p hp
      simpa only [List.foldl_cons] using ih _ (H.mul_mem hp (hletter n))
  exact hfold 1 H.one_mem

private theorem s8_eight_not_even :
    s8CanonicalEight ∉ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  native_decide

/-- The generation statement after the 8-cycle has been put in canonical
coordinates and the fixed point of the 7-cycle has been moved to 7. -/
theorem s8_normalized_generation (b c : Equiv.Perm (Fin 8))
    (hb7 : b.support.card = 7) (hborder : b ^ 7 = 1) (hbfix : b 7 = 7)
    (hc5 : c.support.card = 5) (hcorder : c ^ 5 = 1) :
    Subgroup.closure ({s8CanonicalEight, b, c} : Set (Equiv.Perm (Fin 8))) = ⊤ := by
  let H := Subgroup.closure ({s8CanonicalEight, b, c} : Set (Equiv.Perm (Fin 8)))
  have ha : s8CanonicalEight ∈ H := Subgroup.subset_closure (by simp)
  have hb : b ∈ H := Subgroup.subset_closure (by simp)
  have hc : c ∈ H := Subgroup.subset_closure (by simp)
  have hprim : MulAction.IsPreprimitive H (Fin 8) :=
    s8_pair_primitive H ha b hb hb7 hborder hbfix
  rcases s8_swap_word_or_exception b hb7 hborder hbfix with hexc | ⟨w, hw, hswap⟩
  · obtain ⟨w, hw, hthree⟩ :=
      s8_exceptional_commutator_word b hexc c hc5 hcorder
    have hword : s8EvalWord s8CanonicalEight b w ∈ H :=
      s8_word_mem H _ _ ha hb w
    have hcomm : c * s8EvalWord s8CanonicalEight b w * c⁻¹ *
        (s8EvalWord s8CanonicalEight b w)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem hc hword) (H.inv_mem hc)) (H.inv_mem hword)
    have hA : alternatingGroup (Fin 8) ≤ H :=
      Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem
        hprim (card_support_eq_three_iff.mp hthree) hcomm
    have hdiv : H.index ∣ 2 := by
      simpa using Subgroup.index_dvd_of_le hA
    have hle : H.index ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    have hne : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hcase : H.index = 1 ∨ H.index = 2 := by omega
    rcases hcase with htop | htwo
    · exact Subgroup.index_eq_one.mp htop
    · have hEq : H = alternatingGroup (Fin 8) :=
        Equiv.Perm.eq_alternatingGroup_of_index_eq_two htwo
      exact (s8_eight_not_even (hEq ▸ ha)).elim
  · have hword : s8EvalWord s8CanonicalEight b w ∈ H :=
      s8_word_mem H _ _ ha hb w
    exact Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem
      hprim _ (Equiv.Perm.card_support_eq_two.mp hswap) hword

end Biunimodular.F11
