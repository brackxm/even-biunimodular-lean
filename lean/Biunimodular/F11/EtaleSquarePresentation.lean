/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.Extension.Cotangent.Free
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Noetherian.Orzech

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace Biunimodular.F11
noncomputable section
open Algebra

/-- A square polynomial presentation of an etale algebra has invertible
Jacobian. This applies to the actual five equations, without changing them
to a trace-polynomial presentation. -/
theorem etaleSquarePresentation_jacobian_isUnit
    {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] [IsNoetherianRing S] [Fintype ι] [DecidableEq ι]
    (P : PreSubmersivePresentation R S ι ι) (hmap : P.map = _root_.id) : IsUnit P.jacobian := by
  have hb : Function.Bijective (P.cotangentRestrict Function.injective_id) := by
    apply P.toGenerators.cotangentRestrict_bijective_of_isCompl
      Function.injective_id (v := fun x : Empty => x.elim)
    · have he : Set.range (fun x : Empty => (x.elim : ι)) = ∅ := by
        ext x
        simp
      rw [he]
      simpa using (isCompl_bot_top : IsCompl (⊥ : Set ι) ⊤)
    · have he : Set.range (fun x : Empty =>
          KaehlerDifferential.D R S (P.val (x.elim : ι))) = ∅ := by ext x; simp
      rw [he, Submodule.span_empty]
      exact Subsingleton.elim _ _
    · have he : Set.range (fun x : Empty => P.cotangentSpaceBasis (x.elim : ι)) = ∅ := by
        ext x
        simp
      rw [he, Submodule.span_empty]
      exact disjoint_bot_right
  let G : P.toExtension.Cotangent →ₗ[S] (ι → S) :=
    (Finsupp.linearEquivFunOnFinite S S ι).toLinearMap.comp
      (P.cotangentRestrict Function.injective_id)
  have hG : Function.Surjective G :=
    (Finsupp.linearEquivFunOnFinite S S ι).surjective.comp hb.surjective
  have hspan := Extension.Cotangent.span_eq_top_of_span_eq_ker (P := P.toExtension)
    P.relation P.span_range_relation_eq_ker
  have hcols : Submodule.span S
      (Set.range (fun j i : ι => MvPolynomial.aeval P.val
        (MvPolynomial.pderiv (P.map i) (P.relation j)))) = ⊤ := by
    have h := congrArg (Submodule.map G) hspan
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
      LinearMap.range_eq_top_of_surjective G hG] at h
    convert h using 1
    congr 2
    funext j i
    simp [G, Generators.cotangentRestrict_mk, hmap]
  have hsurj : Function.Surjective P.aevalDifferential := by
    apply LinearMap.range_eq_top.mp
    calc
      LinearMap.range P.aevalDifferential =
          Submodule.map P.aevalDifferential (⊤ : Submodule S (ι → S)) :=
        (Submodule.map_top _).symm
      _ = Submodule.span S (Set.range (fun j i : ι => MvPolynomial.aeval P.val
          (MvPolynomial.pderiv (P.map i) (P.relation j)))) := by
        rw [← (Pi.basisFun S ι).span_eq, Submodule.map_span, ← Set.range_comp]
        congr 2
        funext j i
        simpa only [Function.comp_apply, Pi.basisFun_apply] using
          P.aevalDifferential_single j i
      _ = ⊤ := hcols
  exact P.isUnit_jacobian_iff_aevalDifferential_bijective.mpr
    (IsNoetherian.bijective_of_surjective_endomorphism P.aevalDifferential hsurj)

end
end Biunimodular.F11
