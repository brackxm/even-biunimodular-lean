/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.RegularSequenceFromColon
import Biunimodular.F11.Even11HomogeneousQuadrics

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial

theorem even11FixedSliceHomogeneousGenerators_proper :
    (1 : MvPolynomial (Fin 6) ℂ) ∉ Ideal.ofList even11FixedSliceHomogeneousGenerators := by
  let e : MvPolynomial (Fin 6) ℂ →ₐ[ℂ] ℂ := aeval (0 : Even6 ℂ)
  have hle : Ideal.ofList even11FixedSliceHomogeneousGenerators ≤ RingHom.ker e.toRingHom := by
    apply Ideal.span_le.mpr
    intro p hp
    simp only [even11FixedSliceHomogeneousGenerators, fixedSliceHomogeneousGenerators,
      List.mem_ofFn] at hp
    obtain ⟨j, rfl⟩ := hp
    change aeval (0 : Even6 ℂ)
      (fixedSliceHomogeneousQuadric even11FourierNormalized j.succ) = 0
    simp [fixedSliceHomogeneousQuadric]
  intro h
  have hz := hle h
  rw [RingHom.mem_ker, map_one] at hz
  exact one_ne_zero hz

/-- The concrete homogeneous certificate consists of the
five prefix colon conditions. Properness has already been discharged. -/
theorem even11FixedSliceHomogeneousGenerators_regular_of_colon
    (hcolon : ∀ i (hi : i < even11FixedSliceHomogeneousGenerators.length)
      (x : MvPolynomial (Fin 6) ℂ),
      even11FixedSliceHomogeneousGenerators[i] * x ∈
        Ideal.ofList (even11FixedSliceHomogeneousGenerators.take i) →
      x ∈ Ideal.ofList (even11FixedSliceHomogeneousGenerators.take i)) :
    RingTheory.Sequence.IsRegular (MvPolynomial (Fin 6) ℂ) even11FixedSliceHomogeneousGenerators :=
  regularSequence_of_prefix_colon _ even11FixedSliceHomogeneousGenerators_proper hcolon

end
end Biunimodular.F11
