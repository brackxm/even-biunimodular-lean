/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.PhaseGramIntrinsic11

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

theorem phaseSolution11_exists_nonreal (s : PhaseSolution11) :
    ∃ i : Fin 6, (phaseGramValues11 s.val i).im ≠ 0 := by
  by_contra! h
  have hb : s.val.b = 0 := h 1
  have hd : s.val.d = 0 := h 2
  have hh : s.val.h = 0 := h 3
  have hf : s.val.f = 0 := h 4
  have hk : s.val.k = 0 := h 5
  apply phaseConjugationGenerator11_no_fixed s.val s.property
  rw [phaseConjugationGenerator11_smul]
  cases hx : s.val
  simp_all [phaseConjugate11]

/-- A nonreal phase gives a nonsingular two-by-two principal Gram minor. -/
theorem phaseGramMatrix11_rank_two (s : PhaseSolution11) :
    (phaseGramMatrix11 s.val).rank = 2 := by
  obtain ⟨i, hi⟩ := phaseSolution11_exists_nonreal s
  let r : Fin 2 → Fin 6 := ![0, i]
  let M := (phaseGramMatrix11 s.val).submatrix r r
  have hc := phaseGramMatrix11_diagonal s.val s.property.1 i
  have hdet : M.det = 4 * (phaseGramValues11 s.val i).im ^ 2 := by
    simp only [M, Matrix.det_fin_two, Matrix.submatrix_apply, r, Matrix.cons_val_zero,
      Matrix.cons_val_one, phaseGramMatrix11_apply, phaseGramValues11_zero,
      Complex.one_re, Complex.one_im, one_mul, mul_one, zero_mul, mul_zero, add_zero]
    rw [phaseGramMatrix11_apply] at hc
    nlinarith
  have hne : M.det ≠ 0 := by rw [hdet]; positivity
  have hr := Matrix.rank_of_det_ne_zero hne
  have hle := Matrix.rank_submatrix_le (phaseGramMatrix11 s.val) r r
  have hup := phaseGramMatrix11_rank_le_two s.val
  change M.rank ≤ _ at hle
  norm_num at hr
  omega

theorem phaseGramIntrinsic11_rank_two (K : PhaseGramIntrinsicLocus11) : K.val.rank = 2 := by
  obtain ⟨s, hs⟩ := phaseGramIntrinsic11_reconstruction K.val K.property
  rw [← hs]
  exact phaseGramMatrix11_rank_two s

/-- Every physical Gram matrix is symmetric and positive semidefinite, has
constant diagonal two and exact rank two, and satisfies the five linear
phase relations. -/
theorem phaseGramLocus11_geometry (K : PhaseGramLocus11) :
    K.1.IsSymm ∧ K.1.PosSemidef ∧
      (∀ i, K.1 i i = 2) ∧ K.1.rank = 2 ∧
      PhaseGramLinearRelations11 K.1 :=
  let h := phaseGramLocus11_properties K
  ⟨h.1, h.2.1, h.2.2.1,
    phaseGramIntrinsic11_rank_two (phaseGramLocus11IntrinsicEquiv K), h.2.2.2.2⟩

/-- The intrinsic locus agrees with the exact rank-two formulation. -/
theorem phaseGramIntrinsicSet11_eq_exact_rank :
    phaseGramIntrinsicSet11 =
      {K | K.PosSemidef ∧ K.rank = 2 ∧ (∀ i, K i i = 2) ∧ PhaseGramLinearRelations11 K} := by
  ext K
  constructor
  · intro h
    exact ⟨h.1, phaseGramIntrinsic11_rank_two ⟨K, h⟩, h.2.2⟩
  · rintro ⟨hp, hr, hd, hl⟩
    exact ⟨hp, hr.le, hd, hl⟩

end
end Biunimodular.F11
