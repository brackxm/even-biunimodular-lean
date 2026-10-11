/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section

/-- An exact principal coordinate kernel and a matching upper dimension
bound imply coordinate surjectivity. The conclusion is about the entire
algebra, including nilpotents, rather than merely its complex points. -/
theorem coordinate_surjective_of_finrank_le
    {K A : Type*} [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A]
    (f : Polynomial K →ₐ[K] A) (H : Polynomial K)
    (hker : RingHom.ker f = Ideal.span ({H} : Set (Polynomial K)))
    (hbound : Module.finrank K A ≤ H.natDegree) : Function.Surjective f := by
  let g := Ideal.kerLiftAlg f
  have hi : Function.Injective g := Ideal.kerLiftAlg_injective f
  let : FiniteDimensional K (Polynomial K ⧸ RingHom.ker f) :=
    FiniteDimensional.of_injective g.toLinearMap hi
  have hd : Module.finrank K (Polynomial K ⧸ RingHom.ker f) = H.natDegree := by
    rw [hker]
    exact finrank_quotient_span_eq_natDegree
  have he : Module.finrank K (Polynomial K ⧸ RingHom.ker f) = Module.finrank K A := by
    apply le_antisymm (LinearMap.finrank_le_finrank_of_injective (f := g.toLinearMap) hi)
    simpa only [hd] using hbound
  have hs : Function.Surjective g :=
    (LinearEquiv.ofInjectiveOfFinrankEq g.toLinearMap hi he).surjective
  intro a
  obtain ⟨q, hq⟩ := hs a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨p, ?_⟩
  exact hq

end
end Biunimodular.F11
