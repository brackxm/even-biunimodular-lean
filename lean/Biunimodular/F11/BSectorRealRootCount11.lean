/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceRootIntervalCertificate

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

private theorem invariantBR_eval_expanded11 (x : ℝ) :
    invariantBR.eval x =
      279841*x^8 - 9805544*x^7 + 210448304*x^6 -
      1535826944*x^5 + 6984915200*x^4 - 8382980096*x^3 +
      3230461952*x^2 - 376668160*x + 7929856 := by
  norm_num [invariantBR, invariantB]

private theorem invariantBR_pos_nonpos11 (x : ℝ) (hx : x ≤ 0) :
    0 < invariantBR.eval x := by
  let t := -x
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hformula : invariantBR.eval x =
      279841*t^8 + 9805544*t^7 + 210448304*t^6 +
      1535826944*t^5 + 6984915200*t^4 + 8382980096*t^3 +
      3230461952*t^2 + 376668160*t + 7929856 := by
    rw [invariantBR_eval_expanded11]
    dsimp [t]
    ring
  rw [hformula]
  positivity

private theorem invariantBR_pos_one_to_five11 (x : ℝ)
    (hlo : 1 ≤ x) (hhi : x ≤ 5) :
    0 < invariantBR.eval x := by
  let t := x - 1
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have ht4 : t ≤ 4 := by dsimp [t]; linarith
  have hformula : invariantBR.eval x =
      128754409 + 2392131280*t + 7591387108*t^2 +
      8079854400*t^3 + (2138899870 - 463382448*t)*t^4 +
      (149645044 - 7566816*t)*t^6 + 279841*t^8 := by
    rw [invariantBR_eval_expanded11]
    dsimp [t]
    ring
  have hp4 : 0 ≤ (2138899870 - 463382448*t)*t^4 := by
    apply mul_nonneg
    · linarith
    · positivity
  have hp6 : 0 ≤ (149645044 - 7566816*t)*t^6 := by
    apply mul_nonneg
    · linarith
    · positivity
  rw [hformula]
  nlinarith [sq_nonneg t, sq_nonneg (t^2), sq_nonneg (t^3),
    sq_nonneg (t^4), hp4, hp6]

private theorem invariantBR_pos_ge_five11 (x : ℝ) (hx : 5 ≤ x) :
    0 < invariantBR.eval x := by
  let t := x - 5
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hformula : invariantBR.eval x =
      279841*t^8 + 1388096*t^7 + 63142964*t^6 +
      1588598576*t^5 + 16851144350*t^4 + 107955247904*t^3 +
      457333823012*t^2 + 1144527794160*t + 1228635941481 := by
    rw [invariantBR_eval_expanded11]
    dsimp [t]
    ring
  rw [hformula]
  positivity

/-- The octic B factor has no real roots outside the physical unit
interval. -/
theorem invariantBR_root_mem_openUnitInterval11 (x : ℝ)
    (hx : invariantBR.IsRoot x) : 0 < x ∧ x < 1 := by
  constructor
  · by_contra h
    have hle : x ≤ 0 := le_of_not_gt h
    have hp := invariantBR_pos_nonpos11 x hle
    exact (ne_of_gt hp) hx.eq_zero
  · by_contra h
    have hle : 1 ≤ x := le_of_not_gt h
    have hp : 0 < invariantBR.eval x := by
      by_cases h5 : x ≤ 5
      · exact invariantBR_pos_one_to_five11 x hle h5
      · exact invariantBR_pos_ge_five11 x (le_of_lt (lt_of_not_ge h5))
    exact (ne_of_gt hp) hx.eq_zero

abbrev BRealQuotientRoot11 :=
  {z : FixedSliceBQuotientRoot // (z.1 : ℂ).im = 0}

private theorem bRealQuotientRoot11_bounds (z : BRealQuotientRoot11) :
    0 < (z.1.1 : ℂ).re ∧ (z.1.1 : ℂ).re < 1 := by
  have hz : (z.1.1 : ℂ) = ((z.1.1 : ℂ).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using z.2
  have hrootC : ((invariantB.map (Int.castRingHom ℚ)).map
      (algebraMap ℚ ℂ)).IsRoot (z.1.1 : ℂ) := by
    simpa [Polynomial.IsRoot] using (mem_rootSet.mp z.1.property).2
  have hmap : invariantBR.map Complex.ofRealHom =
      (invariantB.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) := by
    rw [invariantBR, map_map]
    congr 1
  rw [hz, ← hmap] at hrootC
  have hrootR : invariantBR.IsRoot (z.1.1 : ℂ).re :=
    hrootC.of_map Complex.ofReal_injective
  exact invariantBR_root_mem_openUnitInterval11 _ hrootR

noncomputable def bRealQuotientRoot11Equiv :
    BRealQuotientRoot11 ≃ BComplexUnitRoot where
  toFun z := ⟨z.1, z.2, (bRealQuotientRoot11_bounds z).1,
    (bRealQuotientRoot11_bounds z).2⟩
  invFun z := ⟨z.1, z.2.1⟩
  left_inv z := by
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl

/-- Exactly four of the eight complex B roots are real. -/
theorem bRealQuotientRoot11_card :
    Fintype.card BRealQuotientRoot11 = 4 := by
  rw [Fintype.card_congr bRealQuotientRoot11Equiv]
  exact BComplexUnitRoot_card

/-- The other four B roots have nonzero imaginary part. -/
theorem bNonrealQuotientRoot11_card :
    Fintype.card {z : FixedSliceBQuotientRoot // (z.1 : ℂ).im ≠ 0} = 4 := by
  rw [Fintype.card_subtype_compl, fixedSliceBQuotientRoot_card,
    bRealQuotientRoot11_card]

private theorem bPolynomialRealRoot_eq_invariantBR_rootSet11 :
    (invariantB.map (Int.castRingHom ℚ)).rootSet ℝ =
      invariantBR.rootSet ℝ := by
  simpa only [invariantBR] using
    (Polynomial.rootSet_map ℝ ℝ
      (invariantB.map (Int.castRingHom ℚ)) :
      invariantBR.rootSet ℝ =
        (invariantB.map (Int.castRingHom ℚ)).rootSet ℝ).symm

noncomputable def bPolynomialRealRootEquivUnit11 :
    (invariantB.map (Int.castRingHom ℚ)).rootSet ℝ ≃ BUnitRoot where
  toFun x := by
    have hx : x.1 ∈ invariantBR.rootSet ℝ := by
      rw [← bPolynomialRealRoot_eq_invariantBR_rootSet11]
      exact x.2
    have hroot : invariantBR.IsRoot x.1 := (mem_rootSet.mp hx).2
    let hbounds := invariantBR_root_mem_openUnitInterval11 x.1 hroot
    exact ⟨⟨x.1, hx⟩, hbounds⟩
  invFun x := ⟨x.1.1, by
    rw [bPolynomialRealRoot_eq_invariantBR_rootSet11]
    exact x.1.2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl

theorem bPolynomialRealRoot11_card :
    Fintype.card ((invariantB.map (Int.castRingHom ℚ)).rootSet ℝ) = 4 := by
  rw [Fintype.card_congr bPolynomialRealRootEquivUnit11]
  exact BUnitRoot_card

private instance : Fact (((invariantB.map (Int.castRingHom ℚ)).map
    (algebraMap ℚ ℂ)).Splits) :=
  ⟨IsAlgClosed.splits _⟩

/-- Complex conjugation moves four of the eight B roots and fixes the
other four. -/
theorem bGaloisComplexConjugation_support_card_four11 :
    (Polynomial.Gal.galActionHom
      (invariantB.map (Int.castRingHom ℚ)) ℂ
      (Polynomial.Gal.restrict _ ℂ
        (Complex.conjAe.restrictScalars ℚ))).support.card = 4 := by
  let p : ℚ[X] := invariantB.map (Int.castRingHom ℚ)
  have hcount := Polynomial.Gal.card_complex_roots_eq_card_real_add_card_not_gal_inv
    p
  simp only [Set.toFinset_card, p] at hcount
  rw [fixedSliceBQuotientRoot_card, bPolynomialRealRoot11_card] at hcount
  omega

/-- On the eight B roots, complex conjugation has four fixed points and two
two-cycles.  The permutation cycle type records its moved points as `2,2`. -/
theorem bGaloisComplexConjugation_cycleType11 :
    (Polynomial.Gal.galActionHom
      (invariantB.map (Int.castRingHom ℚ)) ℂ
      (Polynomial.Gal.restrict _ ℂ
        (Complex.conjAe.restrictScalars ℚ))).cycleType =
          ({2, 2} : Multiset ℕ) := by
  let p : ℚ[X] := invariantB.map (Int.castRingHom ℚ)
  let σ : Equiv.Perm (p.rootSet ℂ) :=
    Polynomial.Gal.galActionHom p ℂ
      (Polynomial.Gal.restrict p ℂ
        (Complex.conjAe.restrictScalars ℚ))
  have hsquare : σ ^ 2 = 1 := by
    dsimp [σ]
    rw [← map_pow, ← map_pow,
      show AlgEquiv.restrictScalars ℚ Complex.conjAe ^ 2 = 1 from
        AlgEquiv.ext Complex.conj_conj,
      map_one, map_one]
  have hcycles := Equiv.Perm.cycleType_of_pow_prime_eq_one hsquare
  have hsupport : σ.support.card = 4 := by
    exact bGaloisComplexConjugation_support_card_four11
  have hsum := σ.sum_cycleType
  rw [hcycles, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hsupport] at hsum
  have hcard : σ.cycleType.card = 2 := by omega
  change σ.cycleType = _
  rw [hcycles, hcard]
  rfl

end Biunimodular.F11
