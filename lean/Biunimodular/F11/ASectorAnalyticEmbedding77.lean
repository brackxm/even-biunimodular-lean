/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Biunimodular.F11.ASectorCyclotomicCoordinateOrbit77

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial
open scoped IntermediateField
open NumberField

noncomputable section

local instance : IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  CyclotomicField.isCyclotomicExtension 77 ℚ

/-- The the specified complex root of unity, rather than an arbitrary
embedding of the abstract conductor-77 field. -/
def analyticZeta77 : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 77)

theorem analyticZeta77_primitive : IsPrimitiveRoot analyticZeta77 77 := by
  exact Complex.isPrimitiveRoot_exp 77 (by norm_num)

/-- The unique rational embedding sending the abstract chosen primitive root
to `exp(2πi/77)`. -/
def conductor77AnalyticEmbedding : Conductor77Cyclotomic →ₐ[ℚ] ℂ :=
  (IsPrimitiveRoot.embeddingsEquivPrimitiveRoots
      (IsCyclotomicExtension.zeta_spec 77 ℚ Conductor77Cyclotomic) ℂ
      (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 77))).symm
    ⟨analyticZeta77,
      (mem_primitiveRoots (by norm_num : 0 < 77)).2
        analyticZeta77_primitive⟩

theorem conductor77AnalyticEmbedding_zeta :
    conductor77AnalyticEmbedding zeta77 = analyticZeta77 := by
  change conductor77AnalyticEmbedding
    (IsCyclotomicExtension.zeta 77 ℚ Conductor77Cyclotomic) = analyticZeta77
  have h := IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe
      (IsCyclotomicExtension.zeta_spec 77 ℚ Conductor77Cyclotomic) ℂ
      (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 77))
      conductor77AnalyticEmbedding
  simpa only [conductor77AnalyticEmbedding,
    Equiv.apply_symm_apply] using h.symm

/-- At the specified embedding the abstract coordinate is exactly the
the explicit polynomial expression in the analytic root of unity. -/
theorem conductor77AnalyticEmbedding_coordinate (e : ℕ) :
    conductor77AnalyticEmbedding (aSectorX77AtExponent e) =
      aSectorX77Pair (analyticZeta77 ^ (26 * e)) := by
  simp [aSectorX77AtExponent, aSectorX77Pair,
    map_sum, map_add, map_mul, map_pow, map_intCast, map_ofNat, map_neg,
    conductor77AnalyticEmbedding_zeta]

/-- The explicit analytic coordinate is a real number. -/
def analyticASectorCoordinate (e : ℕ) : ℝ :=
  (aSectorX77Pair (analyticZeta77 ^ (26 * e))).re

theorem analyticASectorCoordinate_complex (e : ℕ) :
    (analyticASectorCoordinate e : ℂ) =
      conductor77AnalyticEmbedding (aSectorX77AtExponent e) := by
  have hpow : (analyticZeta77 ^ (26 * e)) ^ 77 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul,
      analyticZeta77_primitive.pow_eq_one, one_pow]
  have hreal := aSectorX77Pair_real
    (analyticZeta77 ^ (26 * e)) hpow
  have him : (aSectorX77Pair (analyticZeta77 ^ (26 * e))).im = 0 := by
    have h := congrArg Complex.im hreal
    simp only [Complex.star_def, Complex.conj_im] at h
    linarith
  rw [conductor77AnalyticEmbedding_coordinate]
  apply Complex.ext
  · rfl
  · simpa only [analyticASectorCoordinate, Complex.ofReal_im] using him.symm

/-- The analytic coordinate at exponent three has the exact degree-thirty
minimal polynomial, in the specified complex embedding. -/
theorem analyticASectorCoordinate_three_minpoly :
    minpoly ℚ (analyticASectorCoordinate 3) =
      aSectorG30.map (Int.castRingHom ℚ) := by
  let ι : Conductor77MaxReal →ₐ[ℚ] Conductor77Cyclotomic :=
    IsScalarTower.toAlgHom ℚ Conductor77MaxReal Conductor77Cyclotomic
  have hcyclo : minpoly ℚ aSectorX77 =
      aSectorG30.map (Int.castRingHom ℚ) := by
    have h := minpoly.algHom_eq ι ι.injective aSectorX77Real
    have hι : ι aSectorX77Real = aSectorX77 := rfl
    rw [hι] at h
    exact h.trans aSectorX77Real_minpoly.symm
  let ιR : ℝ →ₐ[ℚ] ℂ := IsScalarTower.toAlgHom ℚ ℝ ℂ
  have hreal := minpoly.algHom_eq ιR ιR.injective
    (analyticASectorCoordinate 3)
  rw [← hreal]
  change minpoly ℚ ((analyticASectorCoordinate 3 : ℝ) : ℂ) = _
  rw [analyticASectorCoordinate_complex,
    aSectorX77AtExponent_three,
    minpoly.algHom_eq conductor77AnalyticEmbedding
      conductor77AnalyticEmbedding.injective]
  exact hcyclo

/-- Every primitive exponent gives a real coordinate with the same
irreducible degree-thirty polynomial. -/
theorem analyticASectorCoordinate_minpoly (e : ℕ)
    (he : Nat.Coprime (26 * e) 77) :
    minpoly ℚ (analyticASectorCoordinate e) =
      aSectorG30.map (Int.castRingHom ℚ) := by
  let μ : ℂ := analyticZeta77 ^ (26 * e)
  have hprimitive : IsPrimitiveRoot μ 77 :=
    analyticZeta77_primitive.pow_of_coprime (26 * e) he
  have hcyclo : eval₂ (Int.castRingHom ℂ) μ (cyclotomic 77 ℤ) = 0 := by
    have hroot : (cyclotomic 77 ℂ).IsRoot μ :=
      (isRoot_cyclotomic_iff (R := ℂ)).2 hprimitive
    rw [← map_cyclotomic_int 77 ℂ] at hroot
    simpa only [eval₂_eq_eval_map] using hroot.eq_zero
  have hG := aSectorX77_G30_relation μ hcyclo
  rw [← aSectorX77Pair_eq_eval] at hG
  have heq : (analyticASectorCoordinate e : ℂ) = aSectorX77Pair μ := by
    exact (analyticASectorCoordinate_complex e).trans
      (conductor77AnalyticEmbedding_coordinate e)
  rw [← heq] at hG
  have hcomp : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) =
      Int.castRingHom ℂ := by
    ext n
    simp
  have hrootQ : (aeval (analyticASectorCoordinate e : ℂ))
      (aSectorG30.map (Int.castRingHom ℚ)) = 0 := by
    simpa only [aeval_def, eval₂_map, hcomp] using hG
  have hminC : minpoly ℚ (analyticASectorCoordinate e : ℂ) =
      aSectorG30.map (Int.castRingHom ℚ) :=
    (minpoly.eq_of_irreducible_of_monic
      aSectorG30_irreducible_over_Q hrootQ
      (aSectorG30_monic.map (Int.castRingHom ℚ))).symm
  let ιR : ℝ →ₐ[ℚ] ℂ := IsScalarTower.toAlgHom ℚ ℝ ℂ
  have hminR := minpoly.algHom_eq ιR ιR.injective
    (analyticASectorCoordinate e)
  calc
    minpoly ℚ (analyticASectorCoordinate e) =
        minpoly ℚ (analyticASectorCoordinate e : ℂ) := by
      exact hminR.symm
    _ = _ := hminC

private theorem aSectorPhaseExponents_coprime77 :
    ∀ row ∈ aSectorPhaseExponents,
      ∀ e ∈ row, Nat.Coprime (26 * e) 77 := by
  native_decide

/-- Each coordinate in all three of the displayed A-sector rows
is an explicit analytic root of the degree-thirty polynomial. -/
theorem analyticASectorRows_minpoly :
    ∀ row ∈ aSectorPhaseExponents,
      ∀ e ∈ row,
        minpoly ℚ (analyticASectorCoordinate e) =
          aSectorG30.map (Int.castRingHom ℚ) := by
  intro row hr e he
  exact analyticASectorCoordinate_minpoly e
    (aSectorPhaseExponents_coprime77 row hr e he)

private def conductor77AnalyticMaxRealComplexHom :
    Conductor77MaxReal →+* ℂ :=
  conductor77AnalyticEmbedding.toRingHom.comp
    (algebraMap Conductor77MaxReal Conductor77Cyclotomic)

private theorem conductor77AnalyticMaxRealComplexHom_isReal :
    ComplexEmbedding.IsReal conductor77AnalyticMaxRealComplexHom := by
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have hm := x.2
  rw [NumberField.mem_maximalRealSubfield_iff] at hm
  have hx := hm conductor77AnalyticEmbedding
  change star (conductor77AnalyticEmbedding x.1) =
    conductor77AnalyticEmbedding x.1
  exact hx

/-- The specified analytic embedding restricts to a rational embedding of
the maximal real conductor-77 field into `ℝ`. -/
def conductor77AnalyticRealEmbedding : Conductor77MaxReal →ₐ[ℚ] ℝ where
  toRingHom :=
    conductor77AnalyticMaxRealComplexHom_isReal.embedding
  commutes' q := by
    apply Complex.ofReal_injective
    change (conductor77AnalyticMaxRealComplexHom_isReal.embedding
      ((algebraMap ℚ Conductor77MaxReal) q) : ℂ) = (q : ℂ)
    rw [ComplexEmbedding.IsReal.coe_embedding_apply]
    simp [conductor77AnalyticMaxRealComplexHom]

/-- Its explicit degree-thirty generator is the real analytic coordinate at
exponent three. -/
theorem conductor77AnalyticRealEmbedding_generator :
    conductor77AnalyticRealEmbedding aSectorX77Real =
      analyticASectorCoordinate 3 := by
  apply Complex.ofReal_injective
  change (conductor77AnalyticMaxRealComplexHom_isReal.embedding
    aSectorX77Real : ℂ) = (analyticASectorCoordinate 3 : ℂ)
  rw [ComplexEmbedding.IsReal.coe_embedding_apply]
  change conductor77AnalyticEmbedding aSectorX77 =
    (analyticASectorCoordinate 3 : ℂ)
  rw [← aSectorX77AtExponent_three,
    ← analyticASectorCoordinate_complex]

end

end Biunimodular.F11
