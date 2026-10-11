/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion1Colon
import Biunimodular.F11.HomogeneousCompletion2Colon
import Biunimodular.F11.HomogeneousCompletion3Colon
import Biunimodular.F11.HomogeneousCompletion4Colon

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

@[simp] theorem rationalSparsePolynomial_integer (p : FixedSliceSparsePolynomial) :
    rationalSparsePolynomial ⟨1, by decide, p⟩ = homogeneousSparsePolynomial p := by
  simp [rationalSparsePolynomial]

theorem ideal_ofList_ofFn {R : Type*} [CommRing R] {n : ℕ} (f : Fin n → R) :
    Ideal.ofList (List.ofFn f) = Ideal.span (Set.range f) := by
  apply congrArg Ideal.span
  ext x
  change (x ∈ List.ofFn f) ↔ ∃ i, f i = x
  exact List.mem_ofFn

theorem homogeneousCompletion1_previous_original :
    homogeneousCompletion1PreviousIdeal =
      Ideal.ofList ((homogeneousRegularOriginals.take 0).map homogeneousSparsePolynomial) := by
  have hs : (List.ofFn (fun i : Fin 0 => homogeneousCompletion1Original i.castSucc)) =
      (homogeneousRegularOriginals.take 0).map
        (fun p => (⟨1, by decide, p⟩ : RationalSparsePolynomial)) := by native_decide
  have heq := congrArg (List.map rationalSparsePolynomial) hs
  simp only [List.map_ofFn, List.map_map, Function.comp_def,
    rationalSparsePolynomial_integer] at heq
  rw [← heq, ideal_ofList_ofFn]
  rfl

theorem homogeneousCompletion1_last_original :
    homogeneousCompletion1OriginalPoly (Fin.last 0) = homogeneousSparsePolynomial homogeneousRegularOriginal1 := by
  change rationalSparsePolynomial ⟨1, by decide, homogeneousRegularOriginal1⟩ = _
  exact rationalSparsePolynomial_integer _

theorem homogeneousCompletion1_original_colon (x : MvPolynomial (Fin 6) ℂ)
    (hx : homogeneousSparsePolynomial homogeneousRegularOriginal1 * x ∈
      Ideal.ofList ((homogeneousRegularOriginals.take 0).map homogeneousSparsePolynomial)) :
    x ∈ Ideal.ofList ((homogeneousRegularOriginals.take 0).map homogeneousSparsePolynomial) := by
  rw [← homogeneousCompletion1_previous_original] at hx ⊢
  apply homogeneousCompletion1_colon x
  rwa [homogeneousCompletion1_last_original]

theorem homogeneousCompletion2_previous_original :
    homogeneousCompletion2PreviousIdeal =
      Ideal.ofList ((homogeneousRegularOriginals.take 1).map homogeneousSparsePolynomial) := by
  have hs : (List.ofFn (fun i : Fin 1 => homogeneousCompletion2Original i.castSucc)) =
      (homogeneousRegularOriginals.take 1).map
        (fun p => (⟨1, by decide, p⟩ : RationalSparsePolynomial)) := by native_decide
  have heq := congrArg (List.map rationalSparsePolynomial) hs
  simp only [List.map_ofFn, List.map_map, Function.comp_def,
    rationalSparsePolynomial_integer] at heq
  rw [← heq, ideal_ofList_ofFn]
  rfl

theorem homogeneousCompletion2_last_original :
    homogeneousCompletion2OriginalPoly (Fin.last 1) = homogeneousSparsePolynomial homogeneousRegularOriginal2 := by
  change rationalSparsePolynomial ⟨1, by decide, homogeneousRegularOriginal2⟩ = _
  exact rationalSparsePolynomial_integer _

theorem homogeneousCompletion2_original_colon (x : MvPolynomial (Fin 6) ℂ)
    (hx : homogeneousSparsePolynomial homogeneousRegularOriginal2 * x ∈
      Ideal.ofList ((homogeneousRegularOriginals.take 1).map homogeneousSparsePolynomial)) :
    x ∈ Ideal.ofList ((homogeneousRegularOriginals.take 1).map homogeneousSparsePolynomial) := by
  rw [← homogeneousCompletion2_previous_original] at hx ⊢
  apply homogeneousCompletion2_colon x
  rwa [homogeneousCompletion2_last_original]

theorem homogeneousCompletion3_previous_original :
    homogeneousCompletion3PreviousIdeal =
      Ideal.ofList ((homogeneousRegularOriginals.take 2).map homogeneousSparsePolynomial) := by
  have hs : (List.ofFn (fun i : Fin 2 => homogeneousCompletion3Original i.castSucc)) =
      (homogeneousRegularOriginals.take 2).map
        (fun p => (⟨1, by decide, p⟩ : RationalSparsePolynomial)) := by native_decide
  have heq := congrArg (List.map rationalSparsePolynomial) hs
  simp only [List.map_ofFn, List.map_map, Function.comp_def,
    rationalSparsePolynomial_integer] at heq
  rw [← heq, ideal_ofList_ofFn]
  rfl

theorem homogeneousCompletion3_last_original :
    homogeneousCompletion3OriginalPoly (Fin.last 2) = homogeneousSparsePolynomial homogeneousRegularOriginal3 := by
  change rationalSparsePolynomial ⟨1, by decide, homogeneousRegularOriginal3⟩ = _
  exact rationalSparsePolynomial_integer _

theorem homogeneousCompletion3_original_colon (x : MvPolynomial (Fin 6) ℂ)
    (hx : homogeneousSparsePolynomial homogeneousRegularOriginal3 * x ∈
      Ideal.ofList ((homogeneousRegularOriginals.take 2).map homogeneousSparsePolynomial)) :
    x ∈ Ideal.ofList ((homogeneousRegularOriginals.take 2).map homogeneousSparsePolynomial) := by
  rw [← homogeneousCompletion3_previous_original] at hx ⊢
  apply homogeneousCompletion3_colon x
  rwa [homogeneousCompletion3_last_original]

theorem homogeneousCompletion4_previous_original :
    homogeneousCompletion4PreviousIdeal =
      Ideal.ofList ((homogeneousRegularOriginals.take 3).map homogeneousSparsePolynomial) := by
  have hs : (List.ofFn (fun i : Fin 3 => homogeneousCompletion4Original i.castSucc)) =
      (homogeneousRegularOriginals.take 3).map
        (fun p => (⟨1, by decide, p⟩ : RationalSparsePolynomial)) := by native_decide
  have heq := congrArg (List.map rationalSparsePolynomial) hs
  simp only [List.map_ofFn, List.map_map, Function.comp_def,
    rationalSparsePolynomial_integer] at heq
  rw [← heq, ideal_ofList_ofFn]
  rfl

theorem homogeneousCompletion4_last_original :
    homogeneousCompletion4OriginalPoly (Fin.last 3) = homogeneousSparsePolynomial homogeneousRegularOriginal4 := by
  change rationalSparsePolynomial ⟨1, by decide, homogeneousRegularOriginal4⟩ = _
  exact rationalSparsePolynomial_integer _

theorem homogeneousCompletion4_original_colon (x : MvPolynomial (Fin 6) ℂ)
    (hx : homogeneousSparsePolynomial homogeneousRegularOriginal4 * x ∈
      Ideal.ofList ((homogeneousRegularOriginals.take 3).map homogeneousSparsePolynomial)) :
    x ∈ Ideal.ofList ((homogeneousRegularOriginals.take 3).map homogeneousSparsePolynomial) := by
  rw [← homogeneousCompletion4_previous_original] at hx ⊢
  apply homogeneousCompletion4_colon x
  rwa [homogeneousCompletion4_last_original]

end
end Biunimodular.F11
