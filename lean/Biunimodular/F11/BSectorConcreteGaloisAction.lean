/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceQuotientPolynomial
import Biunimodular.F11.DegreeEight875Normalization
import Biunimodular.F11.BSectorS8Assembly
import Biunimodular.F11.BSectorOriginalGaloisS8
import Mathlib.FieldTheory.PolynomialGaloisGroup

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

/-- The rational polynomial defining the residual degree-eight component. -/
noncomputable def invariantBQ : ℚ[X] := invariantB.map (Int.castRingHom ℚ)

abbrev BRoot := invariantBQ.rootSet ℂ

/-- A fixed labeling of the eight complex roots by `Fin 8`. -/
noncomputable def bRootLabels : BRoot ≃ Fin 8 :=
  Fintype.equivFinOfCardEq (by
    change Fintype.card FixedSliceBQuotientRoot = 8
    exact fixedSliceBQuotientRoot_card)

private noncomputable instance :
    Fact ((invariantBQ.map (algebraMap ℚ ℂ)).Splits) :=
  ⟨IsAlgClosed.splits _⟩

/-- The actual Galois action of the B polynomial, expressed on eight labels. -/
noncomputable def bGaloisPermHom : invariantBQ.Gal →* S8Perm :=
  (bRootLabels.permCongrHom.toMonoidHom).comp
    (Polynomial.Gal.galActionHom invariantBQ ℂ)

/-- Its image in `S_8`. -/
noncomputable def bGaloisImage : Subgroup S8Perm :=
  bGaloisPermHom.range

theorem bGaloisPermHom_injective : Function.Injective bGaloisPermHom :=
  bRootLabels.permCongrHom.injective.comp
    (Polynomial.Gal.galActionHom_injective invariantBQ ℂ)

/-- Rational irreducibility makes the genuine Galois action transitive on
the eight roots. -/
theorem bGaloisRootAction_transitive :
    MulAction.IsPretransitive invariantBQ.Gal BRoot :=
  Polynomial.Gal.galAction_isPretransitive invariantBQ ℂ
    (by simpa only [invariantBQ] using invariantB_irreducible_over_Q)

/-- The concrete image in `S_8` is transitive. -/
theorem bGaloisImage_transitive :
    MulAction.IsPretransitive bGaloisImage (Fin 8) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨g, hg⟩ := bGaloisRootAction_transitive.exists_smul_eq
    (bRootLabels.symm x) (bRootLabels.symm y)
  refine ⟨⟨bGaloisPermHom g, ⟨g, rfl⟩⟩, ?_⟩
  change bGaloisPermHom g x = y
  change bRootLabels (g • bRootLabels.symm x) = y
  rw [hg]
  exact bRootLabels.apply_symm_apply y

/-- The three local-to-global cycle witnesses are stated in the
actual Galois group of the B polynomial. -/
structure BSectorGaloisCycleWitnesses where
  eight : ∃ g : invariantBQ.Gal,
    (bGaloisPermHom g).IsCycle ∧ (bGaloisPermHom g).support.card = 8
  seven : ∃ g : invariantBQ.Gal,
    (bGaloisPermHom g).IsCycle ∧ (bGaloisPermHom g).support.card = 7
  five : ∃ g : invariantBQ.Gal,
    (bGaloisPermHom g).IsCycle ∧ (bGaloisPermHom g).support.card = 5

/-- Turn witnesses in the genuine polynomial Galois group into the finite
generation input. -/
noncomputable def BSectorGaloisCycleWitnesses.permutationData
    (h : BSectorGaloisCycleWitnesses) : DegreeEightGaloisPermutationData where
  image := bGaloisImage
  hasEightCycle := by
    obtain ⟨g, hg⟩ := h.eight
    exact ⟨⟨bGaloisPermHom g, ⟨g, rfl⟩⟩, hg⟩
  hasSevenCycle := by
    obtain ⟨g, hg⟩ := h.seven
    exact ⟨⟨bGaloisPermHom g, ⟨g, rfl⟩⟩, hg⟩
  hasFiveCycle := by
    obtain ⟨g, hg⟩ := h.five
    exact ⟨⟨bGaloisPermHom g, ⟨g, rfl⟩⟩, hg⟩

/-- The B-polynomial Galois action is full symmetric once the three Frobenius
cycle witnesses have been derived from the modular factorization data. -/
theorem bGaloisImage_eq_top_of_cycle_witnesses
    (h : BSectorGaloisCycleWitnesses) : bGaloisImage = ⊤ :=
  degreeEight_image_eq_top_of_875 degreeEight875Generation h.permutationData

/-- Faithfulness and full image identify the polynomial Galois group with
`S_8` under the same explicit cycle witness input. -/
noncomputable def bGaloisEquivS8_of_cycle_witnesses
    (h : BSectorGaloisCycleWitnesses) : invariantBQ.Gal ≃* S8Perm := by
  apply MulEquiv.ofBijective bGaloisPermHom
  refine ⟨bGaloisPermHom_injective, ?_⟩
  intro p
  have hp : p ∈ bGaloisImage := by
    rw [bGaloisImage_eq_top_of_cycle_witnesses h]
    trivial
  exact hp

/-- certificate attached to the actual B-polynomial
Galois action. -/
noncomputable def assemble_bSector_S8_from_cycle_witnesses
    (h : BSectorGaloisCycleWitnesses) : BSectorGaloisS8Certificate :=
  assemble_bSector_S8 h.permutationData

/-- Unconditional identification for the original degree-eight B
polynomial. The integral-root action gives the explicit isomorphism. -/
noncomputable def bGaloisEquivS8 : invariantBQ.Gal ≃* S8Perm :=
  bOriginalGaloisEquivS8

/-- The preexisting complex-root permutation representation also has full
image, by faithfulness and the established group order. -/
theorem bGaloisImage_eq_top_unconditional : bGaloisImage = ⊤ := by
  have hsurj : Function.Surjective bGaloisPermHom :=
    bGaloisPermHom_injective.surjective_of_finite bGaloisEquivS8
  apply top_unique
  intro x _
  exact hsurj x

/-- The concrete complex-root image carries the checked 8/7/5 cycles. -/
noncomputable def bConcreteGaloisPermutationData :
    DegreeEightGaloisPermutationData where
  image := bGaloisImage
  hasEightCycle := by
    obtain ⟨g, hg⟩ := bIntegralGaloisPermutationData.hasEightCycle
    exact ⟨⟨g.1, by rw [bGaloisImage_eq_top_unconditional]; trivial⟩, hg⟩
  hasSevenCycle := by
    obtain ⟨g, hg⟩ := bIntegralGaloisPermutationData.hasSevenCycle
    exact ⟨⟨g.1, by rw [bGaloisImage_eq_top_unconditional]; trivial⟩, hg⟩
  hasFiveCycle := by
    obtain ⟨g, hg⟩ := bIntegralGaloisPermutationData.hasFiveCycle
    exact ⟨⟨g.1, by rw [bGaloisImage_eq_top_unconditional]; trivial⟩, hg⟩

noncomputable def bConcreteS8Certificate : BSectorGaloisS8Certificate :=
  assemble_bSector_S8 bConcreteGaloisPermutationData

end Biunimodular.F11
