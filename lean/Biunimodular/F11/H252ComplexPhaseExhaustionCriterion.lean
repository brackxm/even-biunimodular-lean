/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252TorusToPhaseAlgebra
import Biunimodular.F11.H252ComplexPhaseDistinctPoints
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.IsPrincipal

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

/-- The univariate algebra is reduced and has dimension 252. Identifying
it with the full phase algebra requires the inverse-RUR surjectivity proof. -/
abbrev H252UnivariateCoordinateAlgebra := ℂ[X] ⧸ Ideal.span {h252KComplex}

theorem h252UnivariateCoordinateAlgebra_finrank :
    Module.finrank ℂ H252UnivariateCoordinateAlgebra = 252 :=
  finrank_quotient_span_eq_natDegree.trans h252KComplex_degree

instance h252UnivariateCoordinateAlgebra_isReduced : IsReduced H252UnivariateCoordinateAlgebra := by
  change IsReduced (ℂ[X] ⧸ Ideal.span {h252KComplex})
  rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
  exact (PerfectField.separable_iff_squarefree.mp h252KComplex_separable).isRadical

theorem h252ComplexPhaseKCoordinate_surjective_of_torus
    (h : Function.Surjective h252LocalizedTorusCoordinate) :
    Function.Surjective h252ComplexPhaseKCoordinate := by
  have hX := h252ComplexPhaseXCoordinate_surjective_of_torus h
  have hrot : h252ComplexPhaseKCoordinate.comp
      (Polynomial.aeval (C Complex.I * X) : ℂ[X] →ₐ[ℂ] ℂ[X]) =
      h252ComplexPhaseXCoordinate := by
    apply Polynomial.algHom_ext
    simp [h252ComplexPhaseKCoordinate, h252ComplexPhaseXCoordinate]
  intro a
  obtain ⟨p, hp⟩ := hX a
  refine ⟨Polynomial.aeval (C Complex.I * X) p, ?_⟩
  exact (AlgHom.congr_fun hrot p).trans hp

/-- First isomorphism theorem for the actual original ten-equation algebra.
The hypothesis is coordinate surjectivity. -/
def h252ComplexPhaseEquivOfSurjective
    (h : Function.Surjective h252ComplexPhaseKCoordinate) :
    H252UnivariateCoordinateAlgebra ≃ₐ[ℂ] H252ComplexPhaseAlgebra :=
  (Ideal.quotientEquivAlgOfEq ℂ h252ComplexPhaseKCoordinate_ker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective h)

theorem h252ComplexPhase_finrank_of_surjective
    (h : Function.Surjective h252ComplexPhaseKCoordinate) :
    Module.finrank ℂ H252ComplexPhaseAlgebra = 252 := by
  rw [← (h252ComplexPhaseEquivOfSurjective h).toLinearEquiv.finrank_eq]
  exact h252UnivariateCoordinateAlgebra_finrank

theorem h252ComplexPhase_isReduced_of_surjective
    (h : Function.Surjective h252ComplexPhaseKCoordinate) :
    IsReduced H252ComplexPhaseAlgebra :=
  isReduced_of_injective (h252ComplexPhaseEquivOfSurjective h).symm.toRingHom
    (h252ComplexPhaseEquivOfSurjective h).symm.injective

/-- Generation by k implies that a complex point is determined by its k-coordinate. -/
theorem h252ComplexPhase_point_ext_of_surjective
    (h : Function.Surjective h252ComplexPhaseKCoordinate)
    (g g' : H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ)
    (he : g (h252ComplexPhaseKCoordinate X) = g' (h252ComplexPhaseKCoordinate X)) :
    g = g' := by
  have hc : g.comp h252ComplexPhaseKCoordinate = g'.comp h252ComplexPhaseKCoordinate := by
    apply Polynomial.algHom_ext
    exact he
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := h a
  exact AlgHom.congr_fun hc p

/-- Every point of the actual phase scheme maps to an eliminant root. -/
def h252ComplexPhasePointRoot
    (g : H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ) : h252KComplex.rootSet ℂ := by
  let k := g (h252ComplexPhaseKCoordinate X)
  have hc : g.comp h252ComplexPhaseKCoordinate = (Polynomial.aeval k : ℂ[X] →ₐ[ℂ] ℂ) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, Polynomial.aeval_X, k]
  have hz : (Polynomial.aeval k : ℂ[X] →ₐ[ℂ] ℂ) h252KComplex = 0 := by
    rw [← hc, AlgHom.comp_apply, h252ComplexPhaseKCoordinate_eliminant_zero, map_zero]
  have hp : h252KComplex ≠ 0 := by
    intro hp
    have hd := h252KComplex_degree
    rw [hp, Polynomial.natDegree_zero] at hd
    norm_num at hd
  exact ⟨k, (Polynomial.mem_rootSet_of_ne hp).mpr hz⟩

theorem h252ComplexPhasePointRoot_surjective : Function.Surjective h252ComplexPhasePointRoot := by
  intro k
  have hk : h252KComplex.IsRoot k.val := by
    simpa only [Polynomial.IsRoot, Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id] using Polynomial.aeval_eq_zero_of_mem_rootSet k.property
  obtain ⟨g, hg⟩ := h252ComplexPhaseKCoordinate_root_lift k.val hk
  refine ⟨g, Subtype.ext ?_⟩
  exact hg

/-- Once the coordinate generates the algebra, the root lifts exhaust all
complex points. This criterion has no assumptions about reducedness. -/
def h252ComplexPhasePointsEquivOfSurjective
    (h : Function.Surjective h252ComplexPhaseKCoordinate) :
    (H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ) ≃ h252KComplex.rootSet ℂ :=
  Equiv.ofBijective h252ComplexPhasePointRoot ⟨by
    intro g g' he
    apply h252ComplexPhase_point_ext_of_surjective h g g'
    exact congrArg Subtype.val he, h252ComplexPhasePointRoot_surjective⟩

theorem h252ComplexPhase_point_count_of_surjective
    (h : Function.Surjective h252ComplexPhaseKCoordinate) :
    Nat.card (H252ComplexPhaseAlgebra →ₐ[ℂ] ℂ) = 252 :=
  (Nat.card_congr (h252ComplexPhasePointsEquivOfSurjective h)).trans
    h252KComplex_rootSet_card

end
end Biunimodular.F11
