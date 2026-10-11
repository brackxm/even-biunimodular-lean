/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false

namespace Biunimodular.F11

open Matrix
open scoped InnerProductSpace MatrixOrder

noncomputable section

/-- Every real inner product space of dimension at most two admits complex
coordinates preserving its real inner product. -/
theorem real_inner_coordinates_of_finrank_le_two
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E ≤ 2) :
    ∃ z : E → ℂ, ∀ x y,
      inner ℝ x y = (z x).re * (z y).re + (z x).im * (z y).im := by
  have hcases : Module.finrank ℝ E = 0 ∨ Module.finrank ℝ E = 1 ∨
      Module.finrank ℝ E = 2 := by omega
  rcases hcases with h | h | h
  · let b := (stdOrthonormalBasis ℝ E).reindex (finCongr h)
    refine ⟨fun _ ↦ 0, ?_⟩
    intro x y
    rw [← b.repr.inner_map_map x y, PiLp.inner_apply]
    simp
  · let b := (stdOrthonormalBasis ℝ E).reindex (finCongr h)
    refine ⟨fun x ↦ ((b.repr x 0 : ℝ) : ℂ), ?_⟩
    intro x y
    rw [← b.repr.inner_map_map x y, PiLp.inner_apply]
    simp [mul_comm]
  · let b := (stdOrthonormalBasis ℝ E).reindex (finCongr h)
    refine ⟨fun x ↦ ⟨b.repr x 0, b.repr x 1⟩, ?_⟩
    intro x y
    rw [← b.repr.inner_map_map x y, PiLp.inner_apply]
    simp [Fin.sum_univ_two, mul_comm]

/-- A real positive semidefinite matrix of rank at most two is the real
Gram matrix of complex numbers. This is an existence theorem for arbitrary
matrices, independent of the phase parametrization. -/
theorem real_psd_rank_le_two_gram
    {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℝ) (hK : K.PosSemidef) (hr : K.rank ≤ 2) :
    ∃ z : n → ℂ, ∀ i j,
      K i j = (z i).re * (z j).re + (z i).im * (z j).im := by
  classical
  obtain ⟨A, hA⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hK.nonneg
  have hfactor : K = Aᴴ * A := hA
  let L := A.toEuclideanLin
  have hdim : Module.finrank ℝ L.range ≤ 2 := by
    have heq := A.rank_eq_finrank_range_toLin
      (EuclideanSpace.basisFun n ℝ).toBasis
      (EuclideanSpace.basisFun n ℝ).toBasis
    change A.rank = Module.finrank ℝ L.range at heq
    rw [← heq, ← Matrix.rank_conjTranspose_mul_self A, ← hfactor]
    exact hr
  obtain ⟨z, hz⟩ := real_inner_coordinates_of_finrank_le_two L.range hdim
  let v (i : n) : L.range :=
    ⟨L (EuclideanSpace.single i 1), LinearMap.mem_range_self L _⟩
  refine ⟨fun i ↦ z (v i), ?_⟩
  intro i j
  rw [← hz]
  change K i j = inner ℝ (L (EuclideanSpace.single i 1))
    (L (EuclideanSpace.single j 1))
  have hv (i : n) : L (EuclideanSpace.single i 1) =
      WithLp.toLp 2 (A.transpose i) := by
    simp [L, Matrix.toLpLin_apply, EuclideanSpace.single, Matrix.mulVec_single]
    rfl
  rw [hv, hv, inner_matrix_col_col, hfactor]

/-- With diagonal two, the Gram vectors can be normalized to unit complex
phases with their distinguished zeroth phase equal to one. -/
theorem real_psd_rank_le_two_normalized_gram
    {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℝ) (o : n) (hK : K.PosSemidef)
    (hr : K.rank ≤ 2) (hd : ∀ i, K i i = 2) :
    ∃ y : n → ℂ, y o = 1 ∧
      (∀ i, (y i).re ^ 2 + (y i).im ^ 2 = 1) ∧
      ∀ i j, K i j = 2 * ((y i).re * (y j).re + (y i).im * (y j).im) := by
  obtain ⟨z, hz⟩ := real_psd_rank_le_two_gram K hK hr
  have ho : (z o).re ^ 2 + (z o).im ^ 2 = 2 := by
    simpa [pow_two] using (hz o o).symm.trans (hd o)
  let y (i : n) : ℂ :=
    ⟨((z i).re * (z o).re + (z i).im * (z o).im) / 2,
      ((z i).im * (z o).re - (z i).re * (z o).im) / 2⟩
  have hg (i j : n) : K i j =
      2 * ((y i).re * (y j).re + (y i).im * (y j).im) := by
    rw [hz]
    dsimp [y]
    calc
      _ = ((z i).re * (z j).re + (z i).im * (z j).im) *
          ((z o).re ^ 2 + (z o).im ^ 2) / 2 := by rw [ho]; ring
      _ = _ := by ring
  refine ⟨y, ?_, ?_, hg⟩
  · apply Complex.ext <;> dsimp [y]
    · nlinarith [ho]
    · ring
  · intro i
    have h := (hg i i).symm.trans (hd i)
    nlinarith

end

end Biunimodular.F11
