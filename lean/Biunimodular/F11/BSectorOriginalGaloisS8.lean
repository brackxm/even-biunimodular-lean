/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.BSectorMod5ArithmeticCycle
import Biunimodular.F11.BSectorMod37ArithmeticCycle
import Biunimodular.F11.BSectorMod211ArithmeticCycle
import Biunimodular.F11.BSectorS8Assembly

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

private noncomputable instance :
    DecidableEq (invariantBMonicTransform.rootSet BIntegers) := Classical.decEq _

/-- Label the eight integral roots of the monic transform. -/
noncomputable def bIntegralRootLabels :
    invariantBMonicTransform.rootSet BIntegers ≃ Fin 8 :=
  Fintype.equivFinOfCardEq bMonicIntegralRoot_card

/-- The actual Galois group of the original B polynomial acts on those
eight integral roots. -/
noncomputable def bIntegralGaloisPermHom : BOriginalQ.Gal →* S8Perm :=
  (bIntegralRootLabels.permCongrHom.toMonoidHom).comp
    (MulAction.toPermHom BOriginalQ.Gal
      (invariantBMonicTransform.rootSet BIntegers))

private theorem bIntegral_cycle_transfer (σ : BOriginalQ.Gal)
    (hcycle : (MulAction.toPermHom BOriginalQ.Gal
      (invariantBMonicTransform.rootSet BIntegers) σ).IsCycle) :
    (bIntegralGaloisPermHom σ).IsCycle := by
  apply isCycle_of_equivariant_equiv bIntegralRootLabels.symm
    (bIntegralGaloisPermHom σ)
    (MulAction.toPermHom BOriginalQ.Gal
      (invariantBMonicTransform.rootSet BIntegers) σ)
  · intro x
    change bIntegralRootLabels.symm
      (bIntegralRootLabels
        ((MulAction.toPermHom BOriginalQ.Gal
          (invariantBMonicTransform.rootSet BIntegers) σ)
          (bIntegralRootLabels.symm x))) = _
    rw [bIntegralRootLabels.symm_apply_apply]
  · exact hcycle

private theorem bIntegral_support_transfer (σ : BOriginalQ.Gal) :
    (bIntegralGaloisPermHom σ).support.card =
      (MulAction.toPermHom BOriginalQ.Gal
        (invariantBMonicTransform.rootSet BIntegers) σ).support.card := by
  classical
  apply support_card_eq_of_equivariant_equiv bIntegralRootLabels.symm
    (bIntegralGaloisPermHom σ)
    (MulAction.toPermHom BOriginalQ.Gal
      (invariantBMonicTransform.rootSet BIntegers) σ)
  intro x
  change bIntegralRootLabels.symm
    (bIntegralRootLabels
      ((MulAction.toPermHom BOriginalQ.Gal
        (invariantBMonicTransform.rootSet BIntegers) σ)
        (bIntegralRootLabels.symm x))) = _
  rw [bIntegralRootLabels.symm_apply_apply]

noncomputable def bIntegralGaloisPermutationData : DegreeEightGaloisPermutationData where
  image := bIntegralGaloisPermHom.range
  hasEightCycle := by
    obtain ⟨σ, hc, hs⟩ := exists_bMonic_eight_cycle
    refine ⟨⟨bIntegralGaloisPermHom σ, ⟨σ, rfl⟩⟩, ?_⟩
    exact ⟨bIntegral_cycle_transfer σ hc,
      (bIntegral_support_transfer σ).trans hs⟩
  hasSevenCycle := by
    obtain ⟨σ, hc, hs⟩ := exists_bMonic_seven_cycle
    refine ⟨⟨bIntegralGaloisPermHom σ, ⟨σ, rfl⟩⟩, ?_⟩
    exact ⟨bIntegral_cycle_transfer σ hc,
      (bIntegral_support_transfer σ).trans hs⟩
  hasFiveCycle := by
    obtain ⟨σ, hc, hs⟩ := exists_bMonic_five_cycle
    refine ⟨⟨bIntegralGaloisPermHom σ, ⟨σ, rfl⟩⟩, ?_⟩
    exact ⟨bIntegral_cycle_transfer σ hc,
      (bIntegral_support_transfer σ).trans hs⟩

/-- Unconditional `S_8` certificate for the original B polynomial's
Galois action on its integral monicized roots. -/
noncomputable def bOriginalS8Certificate : BSectorGaloisS8Certificate :=
  assemble_bSector_S8 bIntegralGaloisPermutationData

theorem bIntegralGaloisPermHom_surjective :
    Function.Surjective bIntegralGaloisPermHom := by
  intro x
  have hx : x ∈ bIntegralGaloisPermHom.range := by
    rw [show bIntegralGaloisPermHom.range = ⊤ from
      bOriginalS8Certificate.image_eq_top]
    trivial
  exact hx

private theorem bOriginalRoot_card :
    Fintype.card (BOriginalQ.rootSet BSplit) = 8 := by
  rw [Polynomial.card_rootSet_eq_natDegree
    (by simpa only [BOriginalQ] using invariantB_irreducible_over_Q_closed.separable)
    (SplittingField.splits BOriginalQ)]
  norm_num [BOriginalQ, invariantB]
  compute_degree <;> norm_num

/-- The original B polynomial's Galois group is the full symmetric group
on eight letters. -/
noncomputable def bOriginalGaloisEquivS8 : BOriginalQ.Gal ≃* S8Perm := by
  classical
  letI : Fact ((BOriginalQ.map (algebraMap ℚ BSplit)).Splits) :=
    ⟨SplittingField.splits BOriginalQ⟩
  have hupper : Fintype.card BOriginalQ.Gal ≤
      Fintype.card (Equiv.Perm (BOriginalQ.rootSet BSplit)) :=
    Fintype.card_le_of_injective
      (Polynomial.Gal.galActionHom BOriginalQ BSplit)
      (Polynomial.Gal.galActionHom_injective BOriginalQ BSplit)
  have hpermcard : Fintype.card (Equiv.Perm (BOriginalQ.rootSet BSplit)) =
      Fintype.card S8Perm := by
    rw [Fintype.card_perm, Fintype.card_perm, bOriginalRoot_card]
    rfl
  have hle : Fintype.card BOriginalQ.Gal ≤ Fintype.card S8Perm :=
    hupper.trans_eq hpermcard
  have hge : Fintype.card S8Perm ≤ Fintype.card BOriginalQ.Gal :=
    Fintype.card_le_of_surjective bIntegralGaloisPermHom
      bIntegralGaloisPermHom_surjective
  have hcard : Fintype.card BOriginalQ.Gal = Fintype.card S8Perm :=
    le_antisymm hle hge
  have hinj : Function.Injective bIntegralGaloisPermHom :=
    bIntegralGaloisPermHom_surjective.injective_of_finite
      (Fintype.equivOfCardEq hcard)
  exact MulEquiv.ofBijective bIntegralGaloisPermHom
    ⟨hinj, bIntegralGaloisPermHom_surjective⟩

end Biunimodular.F11
