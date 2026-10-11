/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Biunimodular.F11.PhaseInvariant11

set_option autoImplicit false

namespace Biunimodular.F11

open scoped BigOperators
open scoped ComplexConjugate

noncomputable section

/-!
# The rank-two Gram model for physical p = 11 phases

The zeroth phase is fixed to `1`.  The other five phases are indexed in
multiplicative order `(κ, λ, ν, μ, ξ)`.  The matrix below is twice the real
Gram matrix of the resulting six unit vectors in `ℝ²`.
-/

/-- Embed a multiplicative phase index among the last five Gram vertices. -/
def phaseGramVertex11 (a : Fin 5) : Fin 6 :=
  ⟨a.val + 1, Nat.succ_lt_succ a.isLt⟩

/-- The six complex phase values, with the normalized value `1` first and the
five nonzero values in multiplicative order. -/
def phaseGramValues11 (x : PhaseCoords11) : Fin 6 → ℂ :=
  ![1, phaseC x.a x.b, phaseC x.c x.d, phaseC x.g x.h,
    phaseC x.e x.f, phaseC x.j x.k]

@[simp] theorem phaseGramValues11_zero (x : PhaseCoords11) :
    phaseGramValues11 x 0 = 1 := rfl

@[simp] theorem phaseGramValues11_vertex (x : PhaseCoords11) (a : Fin 5) :
    phaseGramValues11 x (phaseGramVertex11 a) =
      phaseMultiplicativeValues11 x a := by
  fin_cases a <;> rfl

/-- The real two-vector underlying a phase value. -/
def phaseGramVector11 (x : PhaseCoords11) (i : Fin 6) : Fin 2 → ℝ :=
  ![(phaseGramValues11 x i).re, (phaseGramValues11 x i).im]

/-- The `6 × 2` coordinate matrix of the six real phase vectors. -/
def phaseGramCoordinateMatrix11 (x : PhaseCoords11) :
    Matrix (Fin 6) (Fin 2) ℝ :=
  fun i k ↦ phaseGramVector11 x i k

/-- Twice the ordinary real Gram matrix of the normalized phase vectors. -/
def phaseGramMatrix11 (x : PhaseCoords11) : Matrix (Fin 6) (Fin 6) ℝ :=
  ((2 : ℝ) • phaseGramCoordinateMatrix11 x) *
    (phaseGramCoordinateMatrix11 x).transpose

theorem phaseGramMatrix11_apply (x : PhaseCoords11) (i j : Fin 6) :
    phaseGramMatrix11 x i j =
      2 * ((phaseGramValues11 x i).re * (phaseGramValues11 x j).re +
        (phaseGramValues11 x i).im * (phaseGramValues11 x j).im) := by
  simp [phaseGramMatrix11, phaseGramCoordinateMatrix11,
    phaseGramVector11, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- The concrete matrix really is twice a Euclidean Gram matrix. -/
theorem phaseGramMatrix11_eq_gram (x : PhaseCoords11) :
    phaseGramMatrix11 x =
      (2 : ℝ) • Matrix.gram ℝ
        (fun i ↦ WithLp.toLp 2 (phaseGramVector11 x i)) := by
  ext i j
  simp only [phaseGramMatrix11, Matrix.mul_apply, Matrix.smul_apply,
    phaseGramCoordinateMatrix11, Matrix.gram_apply, smul_eq_mul]
  change (∑ k : Fin 2,
      (2 : ℝ) * phaseGramVector11 x i k * phaseGramVector11 x j k) =
    (2 : ℝ) * inner ℝ
      (WithLp.toLp 2 (phaseGramVector11 x i))
      (WithLp.toLp 2 (phaseGramVector11 x j))
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_two]
  ring

/-- Every physical Gram matrix is positive semidefinite. -/
theorem phaseGramMatrix11_posSemidef (x : PhaseCoords11) :
    (phaseGramMatrix11 x).PosSemidef := by
  rw [phaseGramMatrix11_eq_gram]
  exact (Matrix.posSemidef_gram ℝ _).smul (by norm_num)

/-- Every physical Gram matrix has rank at most two. -/
theorem phaseGramMatrix11_rank_le_two (x : PhaseCoords11) :
    (phaseGramMatrix11 x).rank ≤ 2 := by
  exact (Matrix.rank_mul_le_left
      ((2 : ℝ) • phaseGramCoordinateMatrix11 x)
      (phaseGramCoordinateMatrix11 x).transpose).trans
    (Matrix.rank_le_width ((2 : ℝ) • phaseGramCoordinateMatrix11 x))

/-- The physical Gram matrix is symmetric. -/
theorem phaseGramMatrix11_isSymm (x : PhaseCoords11) :
    (phaseGramMatrix11 x).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rw [phaseGramMatrix11_apply, phaseGramMatrix11_apply]
  ring

/-- Unit-modulus phase coordinates give the constant diagonal `2`. -/
theorem phaseGramMatrix11_diagonal
    (x : PhaseCoords11) (hc : x.CircleEquations) (i : Fin 6) :
    phaseGramMatrix11 x i i = 2 := by
  rcases hc with ⟨hab, hcd, hef, hgh, hjk⟩
  fin_cases i <;>
    simp [phaseGramMatrix11_apply, phaseGramValues11, phaseC] <;>
    nlinarith

/-- Simultaneous complex conjugation does not change the real Gram matrix. -/
theorem phaseGramMatrix11_conjugate (x : PhaseCoords11) :
    phaseGramMatrix11 (phaseConjugate11 x) = phaseGramMatrix11 x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phaseGramMatrix11_apply, phaseGramValues11,
      phaseConjugate11, phaseC]

/-- Cyclic addition on the five nonzero Gram vertices. -/
def phaseGramShift11 (n : ℕ) (a : Fin 5) : Fin 5 :=
  ⟨(a.val + n) % 5, Nat.mod_lt _ (by norm_num)⟩

/-- Relabel all nonzero Gram vertices by a dilation in `ZMod 5`, while
fixing the normalized zeroth vertex. -/
def phaseGramRelabelIndex11 (r : ZMod 5) : Fin 6 → Fin 6 :=
  ![0,
    phaseGramVertex11 (phaseRotateIndex11 r 0),
    phaseGramVertex11 (phaseRotateIndex11 r 1),
    phaseGramVertex11 (phaseRotateIndex11 r 2),
    phaseGramVertex11 (phaseRotateIndex11 r 3),
    phaseGramVertex11 (phaseRotateIndex11 r 4)]

@[simp] theorem phaseGramRelabelIndex11_zero (i : Fin 6) :
    phaseGramRelabelIndex11 0 i = i := by
  fin_cases i <;> native_decide

theorem phaseGramRelabelIndex11_add (r s : ZMod 5) (i : Fin 6) :
    phaseGramRelabelIndex11 (r + s) i =
      phaseGramRelabelIndex11 s (phaseGramRelabelIndex11 r i) := by
  native_decide +revert

@[simp] theorem phaseGramRelabelIndex11_vertex
    (r : ZMod 5) (a : Fin 5) :
    phaseGramRelabelIndex11 r (phaseGramVertex11 a) =
      phaseGramVertex11 (phaseRotateIndex11 r a) := by
  fin_cases a <;> rfl

/-- Cyclic relabelling of a Gram matrix. -/
def phaseGramRelabelMatrix11 (r : ZMod 5)
    (K : Matrix (Fin 6) (Fin 6) ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  fun i j ↦ K (phaseGramRelabelIndex11 r i)
    (phaseGramRelabelIndex11 r j)

@[simp] theorem phaseGramRelabelMatrix11_zero
    (K : Matrix (Fin 6) (Fin 6) ℝ) :
    phaseGramRelabelMatrix11 0 K = K := by
  ext i j
  simp [phaseGramRelabelMatrix11]

theorem phaseGramRelabelMatrix11_add (r s : ZMod 5)
    (K : Matrix (Fin 6) (Fin 6) ℝ) :
    phaseGramRelabelMatrix11 (r + s) K =
      phaseGramRelabelMatrix11 r (phaseGramRelabelMatrix11 s K) := by
  ext i j
  simp only [phaseGramRelabelMatrix11, phaseGramRelabelIndex11_add]

theorem phaseMultiplicativeValues11_smul
    (g : EvenSymmetry11) (x : PhaseCoords11) :
    phaseMultiplicativeValues11 (g • x) =
      phaseValueAction11.smul g (phaseMultiplicativeValues11 x) := by
  change phaseMultiplicativeValues11
      (phaseMultiplicativeValues11.symm
        (phaseValueAction11.smul g (phaseMultiplicativeValues11 x))) = _
  exact phaseMultiplicativeValues11.apply_symm_apply _

theorem phaseGramValues11_dilation_vertex
    (r : ZMod 5) (x : PhaseCoords11) (a : Fin 5) :
    phaseGramValues11
        ((Multiplicative.ofAdd (r, 0) : EvenSymmetry11) • x)
          (phaseGramVertex11 a) =
      phaseGramValues11 x
        (phaseGramRelabelIndex11 r (phaseGramVertex11 a)) := by
  rw [phaseGramRelabelIndex11_vertex, phaseGramValues11_vertex,
    phaseGramValues11_vertex]
  rw [congrFun (phaseMultiplicativeValues11_smul
    (Multiplicative.ofAdd (r, 0)) x) a]
  rfl

theorem phaseGramValues11_dilation
    (r : ZMod 5) (x : PhaseCoords11) (i : Fin 6) :
    phaseGramValues11
        ((Multiplicative.ofAdd (r, 0) : EvenSymmetry11) • x) i =
      phaseGramValues11 x (phaseGramRelabelIndex11 r i) := by
  fin_cases i
  · rfl
  · simpa [phaseGramVertex11] using
      phaseGramValues11_dilation_vertex r x (0 : Fin 5)
  · simpa [phaseGramVertex11] using
      phaseGramValues11_dilation_vertex r x (1 : Fin 5)
  · simpa [phaseGramVertex11] using
      phaseGramValues11_dilation_vertex r x (2 : Fin 5)
  · simpa [phaseGramVertex11] using
      phaseGramValues11_dilation_vertex r x (3 : Fin 5)
  · simpa [phaseGramVertex11] using
      phaseGramValues11_dilation_vertex r x (4 : Fin 5)

/-- Dilation cyclically relabels the last five rows and columns of the Gram
matrix. -/
theorem phaseGramMatrix11_dilation (r : ZMod 5) (x : PhaseCoords11) :
    phaseGramMatrix11
        ((Multiplicative.ofAdd (r, 0) : EvenSymmetry11) • x) =
      phaseGramRelabelMatrix11 r (phaseGramMatrix11 x) := by
  ext i j
  rw [phaseGramMatrix11_apply, phaseGramRelabelMatrix11,
    phaseGramMatrix11_apply, phaseGramValues11_dilation,
    phaseGramValues11_dilation]

/-- For the full order-ten action, conjugation disappears and only the
dilation coordinate relabels the Gram matrix. -/
theorem phaseGramMatrix11_smul (g : EvenSymmetry11) (x : PhaseCoords11) :
    phaseGramMatrix11 (g • x) =
      phaseGramRelabelMatrix11 g.toAdd.1 (phaseGramMatrix11 x) := by
  let r : ZMod 5 := g.toAdd.1
  let b : ZMod 2 := g.toAdd.2
  have hg : g = Multiplicative.ofAdd (r, b) := by
    dsimp [r, b]
    exact (ofAdd_toAdd g).symm
  have hb : b = 0 ∨ b = 1 := by native_decide +revert
  rcases hb with hb | hb
  · rw [hg, hb]
    simpa [r] using phaseGramMatrix11_dilation r x
  · have hfactor :
        (Multiplicative.ofAdd (r, 1) : EvenSymmetry11) =
          Multiplicative.ofAdd (r, 0) * phaseConjugationGenerator11 := by
      native_decide +revert
    rw [hg, hb, hfactor, mul_smul, phaseConjugationGenerator11_smul,
      phaseGramMatrix11_dilation, phaseGramMatrix11_conjugate]
    change phaseGramRelabelMatrix11 g.toAdd.1 (phaseGramMatrix11 x) =
      phaseGramRelabelMatrix11 (g.toAdd.1 + 0) (phaseGramMatrix11 x)
    rw [add_zero]

theorem phaseMultiplicativeValues11_normSq_one
    (x : PhaseCoords11) (hc : x.CircleEquations) (i : Fin 5) :
    Complex.normSq (phaseMultiplicativeValues11 x i) = 1 := by
  rcases hc with ⟨hab, hcd, hef, hgh, hjk⟩
  fin_cases i <;>
    simp [phaseMultiplicativeValues11, phaseC, Complex.normSq] <;>
    nlinarith

@[simp] theorem phaseMultiplicativeValues11_conjugate
    (x : PhaseCoords11) :
    phaseMultiplicativeValues11 (phaseConjugate11 x) =
      fun i ↦ conj (phaseMultiplicativeValues11 x i) := by
  funext i
  fin_cases i <;>
    norm_num [phaseMultiplicativeValues11, phaseConjugate11, phaseC,
      Complex.ext_iff]

theorem phaseGramMatrix11_zero_vertex
    (x : PhaseCoords11) (i : Fin 5) :
    phaseGramMatrix11 x 0 (phaseGramVertex11 i) =
      2 * (phaseMultiplicativeValues11 x i).re := by
  rw [phaseGramMatrix11_apply, phaseGramValues11_zero,
    phaseGramValues11_vertex]
  norm_num

theorem phaseGramMatrix11_vertex_vertex
    (x : PhaseCoords11) (i j : Fin 5) :
    phaseGramMatrix11 x (phaseGramVertex11 i) (phaseGramVertex11 j) =
      2 * ((phaseMultiplicativeValues11 x i).re *
          (phaseMultiplicativeValues11 x j).re +
        (phaseMultiplicativeValues11 x i).im *
          (phaseMultiplicativeValues11 x j).im) := by
  rw [phaseGramMatrix11_apply, phaseGramValues11_vertex,
    phaseGramValues11_vertex]

private theorem unitComplexFamily_eq_or_conj_of_gram_eq
    (c d : Fin 5 → ℂ)
    (hc : ∀ i, Complex.normSq (c i) = 1)
    (hd : ∀ i, Complex.normSq (d i) = 1)
    (hre : ∀ i, (c i).re = (d i).re)
    (hinner : ∀ i j,
      (c i).re * (c j).re + (c i).im * (c j).im =
        (d i).re * (d j).re + (d i).im * (d j).im) :
    d = c ∨ d = fun i ↦ conj (c i) := by
  have himsq (i : Fin 5) : (c i).im ^ 2 = (d i).im ^ 2 := by
    have hci := hc i
    have hdi := hd i
    simp only [Complex.normSq_apply] at hci hdi
    rw [hre i] at hci
    nlinarith [hci, hdi]
  by_cases hall : ∀ i, (c i).im = 0
  · left
    funext i
    have hdim : (d i).im = 0 := by
      nlinarith [himsq i, hall i]
    apply Complex.ext
    · exact (hre i).symm
    · rw [hall i, hdim]
  · rcases not_forall.mp hall with ⟨i, hi⟩
    have hprod (j : Fin 5) :
        (c i).im * (c j).im = (d i).im * (d j).im := by
      have h := hinner i j
      rw [hre i, hre j] at h
      nlinarith [h]
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp (himsq i)) with hsame | hneg
    · left
      funext j
      have hcancel :
          (c i).im * (c j).im = (c i).im * (d j).im := by
        simpa [hsame] using hprod j
      have him : (d j).im = (c j).im :=
        (mul_left_cancel₀ hi hcancel).symm
      apply Complex.ext
      · exact (hre j).symm
      · exact him
    · right
      funext j
      have hcancel :
          (c i).im * (c j).im = (c i).im * (-(d j).im) := by
        calc
          (c i).im * (c j).im = (d i).im * (d j).im := hprod j
          _ = (c i).im * (-(d j).im) := by rw [hneg]; ring
      have him : (d j).im = -(c j).im := by
        have := mul_left_cancel₀ hi hcancel
        linarith
      apply Complex.ext
      · simpa using (hre j).symm
      · simpa using him

/-- Converse Gram reconstruction: two unit phase tuples have the same
normalized Gram matrix exactly when they are equal or simultaneous complex
conjugates. -/
theorem phaseGramMatrix11_eq_iff_eq_or_conjugate
    (x y : PhaseCoords11) (hx : x.CircleEquations)
    (hy : y.CircleEquations) :
    phaseGramMatrix11 x = phaseGramMatrix11 y ↔
      y = x ∨ y = phaseConjugate11 x := by
  constructor
  · intro hxy
    have hre (i : Fin 5) :
        (phaseMultiplicativeValues11 x i).re =
          (phaseMultiplicativeValues11 y i).re := by
      have h := congrFun (congrFun hxy 0) (phaseGramVertex11 i)
      rw [phaseGramMatrix11_zero_vertex,
        phaseGramMatrix11_zero_vertex] at h
      linarith
    have hinner (i j : Fin 5) :
        (phaseMultiplicativeValues11 x i).re *
            (phaseMultiplicativeValues11 x j).re +
          (phaseMultiplicativeValues11 x i).im *
            (phaseMultiplicativeValues11 x j).im =
        (phaseMultiplicativeValues11 y i).re *
            (phaseMultiplicativeValues11 y j).re +
          (phaseMultiplicativeValues11 y i).im *
            (phaseMultiplicativeValues11 y j).im := by
      have h := congrFun (congrFun hxy (phaseGramVertex11 i))
        (phaseGramVertex11 j)
      rw [phaseGramMatrix11_vertex_vertex,
        phaseGramMatrix11_vertex_vertex] at h
      linarith
    rcases unitComplexFamily_eq_or_conj_of_gram_eq
        (phaseMultiplicativeValues11 x)
        (phaseMultiplicativeValues11 y)
        (phaseMultiplicativeValues11_normSq_one x hx)
        (phaseMultiplicativeValues11_normSq_one y hy)
        hre hinner with hsame | hconj
    · left
      exact phaseMultiplicativeValues11.injective hsame
    · right
      apply phaseMultiplicativeValues11.injective
      rw [phaseMultiplicativeValues11_conjugate]
      exact hconj
  · rintro (rfl | rfl)
    · rfl
    · exact (phaseGramMatrix11_conjugate x).symm

/-- The five linear simple-index relations on a Gram matrix. -/
def PhaseGramLinearRelations11 (K : Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
  ∀ a : Fin 5,
    1 + K 0 (phaseGramVertex11 a) +
      K (phaseGramVertex11 a)
        (phaseGramVertex11 (phaseGramShift11 1 a)) +
      K (phaseGramVertex11 (phaseGramShift11 1 a))
        (phaseGramVertex11 (phaseGramShift11 3 a)) +
      K (phaseGramVertex11 (phaseGramShift11 2 a))
        (phaseGramVertex11 (phaseGramShift11 3 a)) +
      K (phaseGramVertex11 (phaseGramShift11 2 a))
        (phaseGramVertex11 (phaseGramShift11 4 a)) = 0

/-- The five physical phase equations become the five linear Gram
relations, with no loss of information. -/
theorem phaseGramMatrix11_linearRelations
    (x : PhaseCoords11) (hs : x.IsPhaseSolution) :
    PhaseGramLinearRelations11 (phaseGramMatrix11 x) := by
  rcases hs with ⟨_, h1, h2, h3, h4, h5⟩
  simp only [PhaseCoords11.E1] at h1
  simp only [PhaseCoords11.E2] at h2
  simp only [PhaseCoords11.E3] at h3
  simp only [PhaseCoords11.E4] at h4
  simp only [PhaseCoords11.E5] at h5
  intro a
  fin_cases a
  all_goals
    norm_num [PhaseGramLinearRelations11, phaseGramVertex11,
      phaseGramShift11, phaseGramMatrix11_apply, phaseGramValues11,
      phaseC]
  · nlinarith [h1]
  · nlinarith [h2]
  · nlinarith [h4]
  · nlinarith [h3]
  · nlinarith [h5]

/-- For unit phase coordinates, the five linear Gram relations are equivalent
to the five physical phase equations. -/
theorem phaseGramMatrix11_linearRelations_iff
    (x : PhaseCoords11) (hc : x.CircleEquations) :
    PhaseGramLinearRelations11 (phaseGramMatrix11 x) ↔
      x.IsPhaseSolution := by
  constructor
  · intro hrel
    refine ⟨hc, ?_, ?_, ?_, ?_, ?_⟩
    · have h := hrel (0 : Fin 5)
      norm_num [PhaseGramLinearRelations11, phaseGramVertex11,
        phaseGramShift11, phaseGramMatrix11_apply, phaseGramValues11,
        phaseC] at h
      simp only [PhaseCoords11.E1]
      nlinarith [h]
    · have h := hrel (1 : Fin 5)
      norm_num [PhaseGramLinearRelations11, phaseGramVertex11,
        phaseGramShift11, phaseGramMatrix11_apply, phaseGramValues11,
        phaseC] at h
      simp only [PhaseCoords11.E2]
      nlinarith [h]
    · have h := hrel (3 : Fin 5)
      norm_num [PhaseGramLinearRelations11, phaseGramVertex11,
        phaseGramShift11, phaseGramMatrix11_apply, phaseGramValues11,
        phaseC] at h
      simp only [PhaseCoords11.E3]
      nlinarith [h]
    · have h := hrel (2 : Fin 5)
      norm_num [PhaseGramLinearRelations11, phaseGramVertex11,
        phaseGramShift11, phaseGramMatrix11_apply, phaseGramValues11,
        phaseC] at h
      simp only [PhaseCoords11.E4]
      nlinarith [h]
    · have h := hrel (4 : Fin 5)
      norm_num [PhaseGramLinearRelations11, phaseGramVertex11,
        phaseGramShift11, phaseGramMatrix11_apply, phaseGramValues11,
        phaseC] at h
      simp only [PhaseCoords11.E5]
      nlinarith [h]
  · exact phaseGramMatrix11_linearRelations x

/-- The affine-linear Gram coordinate used before the final squaring. -/
def phaseGramSigma11 (K : Matrix (Fin 6) (Fin 6) ℝ) : ℝ :=
  1 + ∑ a : Fin 5, K 0 (phaseGramVertex11 a)

/-- On a physical phase point, `σ(K)` is the zero-frequency Fourier
numerator. -/
theorem phaseGramSigma11_matrix (x : PhaseCoords11) :
    phaseGramSigma11 (phaseGramMatrix11 x) =
      1 + 2 * (x.a + x.c + x.e + x.g + x.j) := by
  simp [phaseGramSigma11, phaseGramVertex11, phaseGramMatrix11_apply,
    phaseGramValues11, phaseC, Fin.sum_univ_succ]
  ring

/-- The physical invariant is exactly `σ(K)² / 11`. -/
theorem phaseInvariantU11_eq_gramSigma (x : PhaseCoords11) :
    phaseInvariantU11 x =
      phaseGramSigma11 (phaseGramMatrix11 x) ^ 2 / 11 := by
  rw [phaseInvariantU11, phaseInvariantQ11, phaseGramSigma11_matrix,
    div_pow]
  have hsqrt : (Real.sqrt 11) ^ 2 = (11 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11)]
  rw [hsqrt]

end

end Biunimodular.F11
