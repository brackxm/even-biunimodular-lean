/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.InvariantIrreducibilityInterface
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# The degree-16 quotient polynomial for the Fourier-conjugate slice

The intrinsic quotient `Y = X / <F>` has degree 16. The project-level exact
calculation identifies the `u=q^2` characteristic polynomial, up to its leading
coefficient, with

  u (u - 176) A(u) B(u).

The fixed-slice geometry certificate identifies the actual invariant
coordinate algebra. `FixedSliceInvariantCharacteristicPolynomial` proves
that multiplication by this invariant has the displayed characteristic
polynomial.
-/

/-- Integral degree-16 numerator of the quotient characteristic polynomial. -/
def fixedSliceQuotientP16 : ℤ[X] :=
  279841*X^16
  - 1827652680*X^15
  + 3257049783088*X^14
  - 902834250825536*X^13
  + 80058287930181376*X^12
  - 2412533038010350592*X^11
  + 43751724749749010432*X^10
  - 331763738335657476096*X^9
  + 1548092135954010603520*X^8
  - 2774179840098089828352*X^7
  + 2176046167971809198080*X^6
  - 768292372028118269952*X^5
  + 117488117139862716416*X^4
  - 7393390199918559232*X^3
  + 163497433005817856*X^2
  - 966105648594944*X

/-- Exact factorization found in the fixed-slice quotient calculation. -/
theorem fixedSliceQuotientP16_factor :
    fixedSliceQuotientP16 = X * (X - C 176) * invariantA * invariantB := by
  norm_num [fixedSliceQuotientP16, invariantA, invariantB]
  ring_nf

/-- Rational form of the quotient polynomial. -/
def fixedSliceQuotientP16Q : ℚ[X] :=
  fixedSliceQuotientP16.map (Int.castRingHom ℚ)

/-- The certified quotient polynomial does not vanish at `u = 1`. -/
theorem fixedSliceQuotientP16Q_one_not_isRoot :
    ¬(fixedSliceQuotientP16Q.map (algebraMap ℚ ℂ)).IsRoot 1 := by
  intro h
  rw [Polynomial.IsRoot, Polynomial.eval_map] at h
  norm_num [fixedSliceQuotientP16Q, fixedSliceQuotientP16] at h

/-- The exact factorization after extension of coefficients to the rationals. -/
theorem fixedSliceQuotientP16Q_factor :
    fixedSliceQuotientP16Q =
      X * (X - C 176) *
        invariantA.map (Int.castRingHom ℚ) *
        invariantB.map (Int.castRingHom ℚ) := by
  rw [fixedSliceQuotientP16Q, fixedSliceQuotientP16_factor]
  rw [Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  norm_num

/-- The four algebraic sectors are exactly the rational zeros of the quotient
polynomial. -/
theorem fixedSliceQuotientP16Q_eval_eq_zero_iff (u : ℚ) :
    fixedSliceQuotientP16Q.eval u = 0 ↔
      u = 0 ∨ u = 176 ∨
        (invariantA.map (Int.castRingHom ℚ)).eval u = 0 ∨
        (invariantB.map (Int.castRingHom ℚ)).eval u = 0 := by
  rw [fixedSliceQuotientP16Q_factor]
  simp only [eval_mul, eval_X, eval_sub, eval_C, mul_eq_zero]
  rw [sub_eq_zero]
  tauto

private theorem coprime_X_invariantA :
    IsCoprime (X : ℚ[X]) (invariantA.map (Int.castRingHom ℚ)) := by
  rw [irreducible_X.coprime_iff_not_dvd, X_dvd_iff]
  norm_num [invariantA]

private theorem coprime_X_invariantB :
    IsCoprime (X : ℚ[X]) (invariantB.map (Int.castRingHom ℚ)) := by
  rw [irreducible_X.coprime_iff_not_dvd, X_dvd_iff]
  norm_num [invariantB]

private theorem coprime_X_sub_C176_invariantA :
    IsCoprime (X - C 176 : ℚ[X])
      (invariantA.map (Int.castRingHom ℚ)) := by
  rw [(irreducible_X_sub_C (176 : ℚ)).coprime_iff_not_dvd, dvd_iff_isRoot]
  norm_num [IsRoot, invariantA]

private theorem coprime_X_sub_C176_invariantB :
    IsCoprime (X - C 176 : ℚ[X])
      (invariantB.map (Int.castRingHom ℚ)) := by
  rw [(irreducible_X_sub_C (176 : ℚ)).coprime_iff_not_dvd, dvd_iff_isRoot]
  norm_num [IsRoot, invariantB]

private theorem coprime_X_X_sub_C176 :
    IsCoprime (X : ℚ[X]) (X - C 176) := by
  rw [irreducible_X.coprime_iff_not_dvd, X_dvd_iff]
  norm_num

private theorem coprime_invariantA_invariantB :
    IsCoprime (invariantA.map (Int.castRingHom ℚ))
      (invariantB.map (Int.castRingHom ℚ)) := by
  apply invariantA_irreducible_over_Q.coprime_iff_not_dvd.mpr
  intro hdvd
  have hassoc := invariantA_irreducible_over_Q.associated_of_dvd
    invariantB_irreducible_over_Q hdvd
  have hdegree := natDegree_eq_of_degree_eq
    (degree_eq_degree_of_associated hassoc)
  have hAdegree :
      (invariantA.map (Int.castRingHom ℚ)).natDegree = 6 := by
    norm_num [invariantA]
    compute_degree <;> norm_num
  have hBdegree :
      (invariantB.map (Int.castRingHom ℚ)).natDegree = 8 := by
    norm_num [invariantB]
    compute_degree <;> norm_num
  omega

/-- The quotient polynomial has no repeated algebraic roots. -/
theorem fixedSliceQuotientP16Q_separable :
    fixedSliceQuotientP16Q.Separable := by
  rw [fixedSliceQuotientP16Q_factor]
  apply Separable.mul
  · apply Separable.mul
    · exact irreducible_X.separable.mul
        (irreducible_X_sub_C (176 : ℚ)).separable coprime_X_X_sub_C176
    · exact invariantA_irreducible_over_Q.separable
    · exact coprime_X_invariantA.mul_left coprime_X_sub_C176_invariantA
  · exact invariantB_irreducible_over_Q.separable
  · exact
      (coprime_X_invariantB.mul_left coprime_X_sub_C176_invariantB).mul_left
        coprime_invariantA_invariantB

/-- The rational quotient polynomial has its advertised degree. -/
theorem fixedSliceQuotientP16Q_natDegree :
    fixedSliceQuotientP16Q.natDegree = 16 := by
  rw [fixedSliceQuotientP16Q_factor]
  have hx : (X : ℚ[X]) ≠ 0 := irreducible_X.ne_zero
  have hc : (X - C 176 : ℚ[X]) ≠ 0 :=
    (irreducible_X_sub_C (176 : ℚ)).ne_zero
  have hA : invariantA.map (Int.castRingHom ℚ) ≠ 0 :=
    invariantA_irreducible_over_Q.ne_zero
  have hB : invariantB.map (Int.castRingHom ℚ) ≠ 0 :=
    invariantB_irreducible_over_Q.ne_zero
  rw [natDegree_mul (mul_ne_zero (mul_ne_zero hx hc) hA) hB,
    natDegree_mul (mul_ne_zero hx hc) hA, natDegree_mul hx hc]
  have hAdegree :
      (invariantA.map (Int.castRingHom ℚ)).natDegree = 6 := by
    norm_num [invariantA]
    compute_degree <;> norm_num
  have hBdegree :
      (invariantB.map (Int.castRingHom ℚ)).natDegree = 8 := by
    norm_num [invariantB]
    compute_degree <;> norm_num
  norm_num [hAdegree, hBdegree]

/-- The intrinsic algebraic quotient point space: the complex roots of the
degree-16 quotient polynomial. -/
abbrev FixedSliceQuotientRoot := fixedSliceQuotientP16Q.rootSet ℂ

/-- There are exactly sixteen distinct complex quotient values. -/
theorem fixedSliceQuotientRoot_card :
    Fintype.card FixedSliceQuotientRoot = 16 := by
  rw [card_rootSet_eq_natDegree fixedSliceQuotientP16Q_separable
    (IsAlgClosed.splits _)]
  exact fixedSliceQuotientP16Q_natDegree

/-- The six distinct complex roots in the A-sector. -/
abbrev FixedSliceAQuotientRoot :=
  (invariantA.map (Int.castRingHom ℚ)).rootSet ℂ

/-- The eight distinct complex roots in the B-sector. -/
abbrev FixedSliceBQuotientRoot :=
  (invariantB.map (Int.castRingHom ℚ)).rootSet ℂ

theorem fixedSliceAQuotientRoot_card :
    Fintype.card FixedSliceAQuotientRoot = 6 := by
  rw [card_rootSet_eq_natDegree invariantA_irreducible_over_Q.separable
    (IsAlgClosed.splits _)]
  norm_num [invariantA]
  compute_degree <;> norm_num

theorem fixedSliceBQuotientRoot_card :
    Fintype.card FixedSliceBQuotientRoot = 8 := by
  rw [card_rootSet_eq_natDegree invariantB_irreducible_over_Q.separable
    (IsAlgClosed.splits _)]
  norm_num [invariantB]
  compute_degree <;> norm_num

/-- Factor-preserving algebraic labels for the quotient roots. -/
inductive FixedSliceQuotientSectorRoot where
  | gaussian
  | constant
  | A (root : FixedSliceAQuotientRoot)
  | B (root : FixedSliceBQuotientRoot)
  deriving Fintype

theorem fixedSliceQuotientSectorRoot_card :
    Fintype.card FixedSliceQuotientSectorRoot = 16 := by
  let encode : FixedSliceQuotientSectorRoot →
      Unit ⊕ (Unit ⊕ (FixedSliceAQuotientRoot ⊕
        FixedSliceBQuotientRoot))
    | .gaussian => Sum.inl ()
    | .constant => Sum.inr (Sum.inl ())
    | .A root => Sum.inr (Sum.inr (Sum.inl root))
    | .B root => Sum.inr (Sum.inr (Sum.inr root))
  let decode : Unit ⊕ (Unit ⊕ (FixedSliceAQuotientRoot ⊕
      FixedSliceBQuotientRoot)) → FixedSliceQuotientSectorRoot
    | Sum.inl () => .gaussian
    | Sum.inr (Sum.inl ()) => .constant
    | Sum.inr (Sum.inr (Sum.inl root)) => .A root
    | Sum.inr (Sum.inr (Sum.inr root)) => .B root
  let e : FixedSliceQuotientSectorRoot ≃
      Unit ⊕ (Unit ⊕ (FixedSliceAQuotientRoot ⊕
        FixedSliceBQuotientRoot)) :=
    Equiv.mk encode decode
      (by intro x; cases x <;> rfl)
      (by intro x; rcases x with (_ | _ | _ | _) <;> rfl)
  rw [Fintype.card_congr e]
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum,
    fixedSliceAQuotientRoot_card, fixedSliceBQuotientRoot_card]
  norm_num

/-- Forget the factor tag and retain the corresponding root of the full
quotient polynomial. -/
def fixedSliceQuotientSectorRootValue :
    FixedSliceQuotientSectorRoot → FixedSliceQuotientRoot
  | .gaussian => ⟨0, by
      rw [mem_rootSet]
      refine ⟨fixedSliceQuotientP16Q_separable.ne_zero, ?_⟩
      rw [fixedSliceQuotientP16Q_factor]
      simp⟩
  | .constant => ⟨176, by
      rw [mem_rootSet]
      refine ⟨fixedSliceQuotientP16Q_separable.ne_zero, ?_⟩
      rw [fixedSliceQuotientP16Q_factor]
      simp⟩
  | .A root => ⟨root, by
      rw [mem_rootSet]
      refine ⟨fixedSliceQuotientP16Q_separable.ne_zero, ?_⟩
      rw [fixedSliceQuotientP16Q_factor]
      have hr := (mem_rootSet.mp root.property).2
      simp [hr]⟩
  | .B root => ⟨root, by
      rw [mem_rootSet]
      refine ⟨fixedSliceQuotientP16Q_separable.ne_zero, ?_⟩
      rw [fixedSliceQuotientP16Q_factor]
      have hr := (mem_rootSet.mp root.property).2
      simp [hr]⟩

theorem fixedSliceQuotientSectorRootValue_surjective :
    Function.Surjective fixedSliceQuotientSectorRootValue := by
  rintro ⟨u, hu⟩
  have hroot := (mem_rootSet.mp hu).2
  rw [fixedSliceQuotientP16Q_factor] at hroot
  simp only [map_mul, map_sub, aeval_X, aeval_C, mul_eq_zero] at hroot
  rcases hroot with ((hu0 | hu176) | hA) | hB
  · refine ⟨.gaussian, ?_⟩
    apply Subtype.ext
    change (0 : ℂ) = u
    exact hu0.symm
  · refine ⟨.constant, ?_⟩
    apply Subtype.ext
    change (176 : ℂ) = u
    exact (sub_eq_zero.mp hu176).symm
  · refine ⟨.A ⟨u, ?_⟩, rfl⟩
    rw [mem_rootSet]
    exact ⟨invariantA_irreducible_over_Q.ne_zero, hA⟩
  · refine ⟨.B ⟨u, ?_⟩, rfl⟩
    rw [mem_rootSet]
    exact ⟨invariantB_irreducible_over_Q.ne_zero, hB⟩

/-- The factor-tagged sector decomposition is exactly the full complex root
space of the quotient polynomial. -/
noncomputable def fixedSliceQuotientSectorRootEquiv :
    FixedSliceQuotientSectorRoot ≃ FixedSliceQuotientRoot :=
  Equiv.ofBijective fixedSliceQuotientSectorRootValue
    ((Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨fixedSliceQuotientSectorRootValue_surjective, by
        rw [fixedSliceQuotientSectorRoot_card,
          fixedSliceQuotientRoot_card]⟩)

end

end Biunimodular.F11
