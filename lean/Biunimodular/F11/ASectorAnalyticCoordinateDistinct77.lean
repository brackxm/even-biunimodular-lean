/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPhysicalAnalyticConjugacy77

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

noncomputable section

local instance : IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  CyclotomicField.isCyclotomicExtension 77 ℚ

/-- A second real generator used to distinguish embeddings that agree on the
degree-thirty A coordinate. -/
def conductor77ThetaPair : Conductor77Cyclotomic :=
  zeta77 + zeta77 ^ 76

theorem conductor77ThetaPair_mem_maximalReal :
    conductor77ThetaPair ∈
      NumberField.maximalRealSubfield Conductor77Cyclotomic := by
  rw [NumberField.mem_maximalRealSubfield_iff]
  intro φ
  let μ : ℂ := φ zeta77
  have hζ : zeta77 ^ 77 = 1 :=
    (IsCyclotomicExtension.zeta_spec 77 ℚ
      Conductor77Cyclotomic).pow_eq_one
  have hμ : μ ^ 77 = 1 := by
    simpa only [μ, map_pow, map_one] using congrArg φ hζ
  have h1 := star_pow_complement77 μ hμ 1 (by norm_num)
  have h76 := star_pow_complement77 μ hμ 76 (by norm_num)
  have hμstar : star μ = μ ^ 76 := by simpa only [pow_one] using h1
  have hμ76star : star (μ ^ 76) = μ := by
    simpa only [show 77 - 76 = 1 by norm_num, pow_one] using h76
  simp only [conductor77ThetaPair, map_add, map_pow]
  change star (μ + μ ^ 76) = μ + μ ^ 76
  rw [star_add, hμstar, hμ76star]
  ring

def conductor77ThetaPairReal : Conductor77MaxReal :=
  ⟨conductor77ThetaPair, conductor77ThetaPair_mem_maximalReal⟩

private theorem rootUnity_sum_eq_implies_eq_or_inv
    (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a + a⁻¹ = b + b⁻¹) :
    a = b ∨ a * b = 1 := by
  have hprod : (a - b) * (a * b - 1) = 0 := by
    have hmul : (a ^ 2 + 1) * b = a * (b ^ 2 + 1) := by
      field_simp [ha, hb] at h
      exact h
    calc
      (a - b) * (a * b - 1) =
          (a ^ 2 + 1) * b - a * (b ^ 2 + 1) := by ring
      _ = 0 := sub_eq_zero.mpr hmul
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private def conductor77AnalyticEmbeddingAtExponent
    (e : ℕ) (he : (26 * e).Coprime 77) :
    Conductor77Cyclotomic →ₐ[ℚ] ℂ :=
  (IsPrimitiveRoot.embeddingsEquivPrimitiveRoots
      (IsCyclotomicExtension.zeta_spec 77 ℚ Conductor77Cyclotomic) ℂ
      (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 77))).symm
    ⟨analyticZeta77 ^ (26 * e),
      (mem_primitiveRoots (by norm_num : 0 < 77)).2
        (analyticZeta77_primitive.pow_of_coprime (26 * e) he)⟩

private theorem conductor77AnalyticEmbeddingAtExponent_zeta
    (e : ℕ) (he : (26 * e).Coprime 77) :
    conductor77AnalyticEmbeddingAtExponent e he zeta77 =
      analyticZeta77 ^ (26 * e) := by
  change conductor77AnalyticEmbeddingAtExponent e he
    (IsCyclotomicExtension.zeta 77 ℚ Conductor77Cyclotomic) = _
  have h := IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe
      (IsCyclotomicExtension.zeta_spec 77 ℚ Conductor77Cyclotomic) ℂ
      (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 77))
      (conductor77AnalyticEmbeddingAtExponent e he)
  simpa only [conductor77AnalyticEmbeddingAtExponent,
    Equiv.apply_symm_apply] using h.symm

private def conductor77AnalyticRealHomAtExponent
    (e : ℕ) (he : (26 * e).Coprime 77) :
    Conductor77MaxReal →ₐ[ℚ] ℂ :=
  (conductor77AnalyticEmbeddingAtExponent e he).comp
    (IsScalarTower.toAlgHom ℚ Conductor77MaxReal Conductor77Cyclotomic)

private theorem conductor77AnalyticRealHomAtExponent_generator
    (e : ℕ) (he : (26 * e).Coprime 77) :
    conductor77AnalyticRealHomAtExponent e he aSectorX77Real =
      (analyticASectorCoordinate e : ℂ) := by
  have hmap : (IsScalarTower.toAlgHom ℚ Conductor77MaxReal
      Conductor77Cyclotomic) aSectorX77Real = aSectorX77 := rfl
  rw [conductor77AnalyticRealHomAtExponent, AlgHom.comp_apply, hmap,
    aSectorX77]
  simp only [aSectorX77Pair, map_sum, map_add, map_mul,
    map_pow, map_intCast, map_ofNat, map_neg,
    conductor77AnalyticEmbeddingAtExponent_zeta]
  exact ((analyticASectorCoordinate_complex e).trans
    (conductor77AnalyticEmbedding_coordinate e)).symm

private theorem aSectorCanonicalAnalyticExponents77_signed_unique :
    ∀ e ∈ aSectorCanonicalAnalyticExponents77,
      ∀ f ∈ aSectorCanonicalAnalyticExponents77,
        ((26 * e) % 77 = (26 * f) % 77 ∨
          (26 * e + 26 * f) % 77 = 0) → e = f := by
  native_decide

/-- The thirty signed primitive exponents give thirty different real values
of the explicit cyclotomic coordinate. -/
theorem analyticASectorCoordinate_injective_on_canonical :
    ∀ e ∈ aSectorCanonicalAnalyticExponents77,
      ∀ f ∈ aSectorCanonicalAnalyticExponents77,
        analyticASectorCoordinate e = analyticASectorCoordinate f → e = f := by
  intro e he f hf hcoord
  have hec := aSectorCanonicalAnalyticExponents77_coprime e he
  have hfc := aSectorCanonicalAnalyticExponents77_coprime f hf
  let φe := conductor77AnalyticRealHomAtExponent e hec
  let φf := conductor77AnalyticRealHomAtExponent f hfc
  have hφ : φe = φf := by
    apply AlgHom.ext_of_adjoin_eq_top aSectorX77Real_generates_maxReal
    intro x hx
    have hx' : x = aSectorX77Real := by simpa using hx
    subst x
    rw [show φe aSectorX77Real = (analyticASectorCoordinate e : ℂ) from
      conductor77AnalyticRealHomAtExponent_generator e hec]
    rw [show φf aSectorX77Real = (analyticASectorCoordinate f : ℂ) from
      conductor77AnalyticRealHomAtExponent_generator f hfc]
    exact congrArg (fun x : ℝ => (x : ℂ)) hcoord
  let a : ℂ := analyticZeta77 ^ (26 * e)
  let b : ℂ := analyticZeta77 ^ (26 * f)
  have hθe : φe conductor77ThetaPairReal = a + a ^ 76 := by
    change conductor77AnalyticEmbeddingAtExponent e hec conductor77ThetaPair = _
    simp [conductor77ThetaPair, a,
      conductor77AnalyticEmbeddingAtExponent_zeta]
  have hθf : φf conductor77ThetaPairReal = b + b ^ 76 := by
    change conductor77AnalyticEmbeddingAtExponent f hfc conductor77ThetaPair = _
    simp [conductor77ThetaPair, b,
      conductor77AnalyticEmbeddingAtExponent_zeta]
  have hθ := congrArg (fun (φ : Conductor77MaxReal →ₐ[ℚ] ℂ) =>
    φ conductor77ThetaPairReal) hφ
  rw [hθe, hθf] at hθ
  have hζ77 : analyticZeta77 ^ 77 = 1 :=
    analyticZeta77_primitive.pow_eq_one
  have hζne : analyticZeta77 ≠ 0 := by
    intro hz
    rw [hz] at hζ77
    norm_num at hζ77
  have ha : a ≠ 0 := pow_ne_zero _ hζne
  have hb : b ≠ 0 := pow_ne_zero _ hζne
  have ha77 : a ^ 77 = 1 := by
    change (analyticZeta77 ^ (26 * e)) ^ 77 = 1
    calc
      (analyticZeta77 ^ (26 * e)) ^ 77 =
          analyticZeta77 ^ ((26 * e) * 77) := by simp only [← pow_mul]
      _ = analyticZeta77 ^ (77 * (26 * e)) := by congr 1; omega
      _ = (analyticZeta77 ^ 77) ^ (26 * e) := by rw [pow_mul]
      _ = 1 := by rw [hζ77, one_pow]
  have hb77 : b ^ 77 = 1 := by
    change (analyticZeta77 ^ (26 * f)) ^ 77 = 1
    calc
      (analyticZeta77 ^ (26 * f)) ^ 77 =
          analyticZeta77 ^ ((26 * f) * 77) := by simp only [← pow_mul]
      _ = analyticZeta77 ^ (77 * (26 * f)) := by congr 1; omega
      _ = (analyticZeta77 ^ 77) ^ (26 * f) := by rw [pow_mul]
      _ = 1 := by rw [hζ77, one_pow]
  have ha76 : a ^ 76 = a⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using ha77
  have hb76 : b ^ 76 = b⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using hb77
  rw [ha76, hb76] at hθ
  rcases rootUnity_sum_eq_implies_eq_or_inv a b ha hb hθ with hab | hab
  · have hmod : (26 * e) % 77 = (26 * f) % 77 := by
      apply analyticZeta77_primitive.pow_inj
        (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num))
      calc
        analyticZeta77 ^ ((26 * e) % 77) = a := by
          exact (pow_eq_pow_mod _ hζ77).symm
        _ = b := hab
        _ = analyticZeta77 ^ ((26 * f) % 77) := by
          exact pow_eq_pow_mod _ hζ77
    exact aSectorCanonicalAnalyticExponents77_signed_unique
      e he f hf (Or.inl hmod)
  · have hmod : (26 * e + 26 * f) % 77 = 0 := by
      apply analyticZeta77_primitive.pow_inj
        (Nat.mod_lt _ (by norm_num)) (by norm_num : 0 < 77)
      calc
        analyticZeta77 ^ ((26 * e + 26 * f) % 77) = a * b := by
          rw [← pow_add]
          exact (pow_eq_pow_mod _ hζ77).symm
        _ = 1 := hab
        _ = analyticZeta77 ^ 0 := by simp
    exact aSectorCanonicalAnalyticExponents77_signed_unique
      e he f hf (Or.inr hmod)

/-- Each physical A-sector squared coordinate has a unique signed primitive
exponent in the canonical list. -/
theorem everyASectorPhase_coordinate_unique_analyticExponent
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    ∀ y ∈ [s.1.b, s.1.d, s.1.f, s.1.h, s.1.k],
      ∃! e : ℕ,
        e ∈ aSectorCanonicalAnalyticExponents77 ∧
          4 * y ^ 2 = analyticASectorCoordinate e := by
  intro y hy
  obtain ⟨e, he, hval⟩ :=
    everyASectorPhase_coordinate_in_analyticThirty s hA y hy
  refine ⟨e, ⟨he, hval⟩, ?_⟩
  intro f hf
  apply analyticASectorCoordinate_injective_on_canonical f hf.1 e he
  exact hf.2.symm.trans hval

/-- The thirty explicit analytic coordinates, viewed in `ℂ`. -/
def analyticASectorCoordinateFinset77 : Finset ℂ :=
  aSectorCanonicalAnalyticExponents77.toFinset.image
    (fun e => (analyticASectorCoordinate e : ℂ))

theorem analyticASectorCoordinateFinset77_card :
    analyticASectorCoordinateFinset77.card = 30 := by
  classical
  rw [analyticASectorCoordinateFinset77,
    Finset.card_image_of_injOn]
  · simpa only [List.toFinset_card_of_nodup
      aSectorCanonicalAnalyticExponents77_card.1] using
      aSectorCanonicalAnalyticExponents77_card.2
  · intro e he f hf h
    have hreal : analyticASectorCoordinate e =
        analyticASectorCoordinate f := Complex.ofReal_injective h
    exact analyticASectorCoordinate_injective_on_canonical e
      (List.mem_toFinset.mp he) f (List.mem_toFinset.mp hf) hreal

/-- The explicit analytic values exhaust the complex roots of `G30`. -/
theorem analyticASectorCoordinateFinset77_eq_G30_roots :
    analyticASectorCoordinateFinset77 =
      ((aSectorG30.map (Int.castRingHom ℚ)).aroots ℂ).toFinset := by
  classical
  let p : ℚ[X] := aSectorG30.map (Int.castRingHom ℚ)
  have hp : p ≠ 0 := aSectorG30_irreducible_over_Q.ne_zero
  have hsub : analyticASectorCoordinateFinset77 ⊆
      (p.aroots ℂ).toFinset := by
    intro x hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    have hminR := aSectorCanonicalAnalyticExponents77_minpoly e
      (List.mem_toFinset.mp he)
    let ιR : ℝ →ₐ[ℚ] ℂ := IsScalarTower.toAlgHom ℚ ℝ ℂ
    have hminC : minpoly ℚ (analyticASectorCoordinate e : ℂ) = p := by
      change minpoly ℚ (ιR (analyticASectorCoordinate e)) = p
      rw [minpoly.algHom_eq ιR ιR.injective]
      exact hminR
    have hroot : (aeval (analyticASectorCoordinate e : ℂ)) p = 0 := by
      rw [← hminC]
      exact minpoly.aeval ℚ _
    exact Multiset.mem_toFinset.mpr ((mem_aroots).2 ⟨hp, hroot⟩)
  have hdegree : p.natDegree = 30 := by
    change (aSectorG30.map (Int.castRingHom ℚ)).natDegree = 30
    rw [natDegree_map_eq_of_injective
      (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))]
    exact aSectorG30_natDegree
  have hroots : (p.aroots ℂ).toFinset.card = 30 := by
    have hcard := card_rootSet_eq_natDegree
      aSectorG30_irreducible_over_Q.separable
      (IsAlgClosed.splits (p.map (algebraMap ℚ ℂ)))
    change Fintype.card (p.rootSet ℂ) = p.natDegree at hcard
    rw [hdegree] at hcard
    simpa only [Polynomial.rootSet_def, Finset.coe_sort_coe,
      Fintype.card_coe] using hcard
  apply Finset.eq_of_subset_of_card_le hsub
  rw [analyticASectorCoordinateFinset77_card, hroots]

/-- The fifteen exponents in the three displayed physical rows are distinct
members of the canonical signed conductor-77 exponent set. -/
theorem aSectorDisplayedExponents77_nodup_mem :
    (aSectorPhaseExponents.flatten).Nodup ∧
      ∀ e ∈ aSectorPhaseExponents.flatten,
        e ∈ aSectorCanonicalAnalyticExponents77 := by
  native_decide

/-- All fifteen displayed analytic phase coordinates are distinct. -/
theorem aSectorDisplayedCoordinates77_nodup :
    (aSectorPhaseExponents.flatten.map analyticASectorCoordinate).Nodup := by
  apply aSectorDisplayedExponents77_nodup_mem.1.map_on
  intro e he f hf hef
  exact analyticASectorCoordinate_injective_on_canonical e
    (aSectorDisplayedExponents77_nodup_mem.2 e he) f
    (aSectorDisplayedExponents77_nodup_mem.2 f hf) hef

end

end Biunimodular.F11
