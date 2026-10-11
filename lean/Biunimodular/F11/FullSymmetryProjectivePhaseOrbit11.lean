/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryProjectiveOrbit11
import Biunimodular.F11.FullSymmetryProjectiveEvenGenerators11
import Biunimodular.F11.FullSymmetryProjectiveFourierPhysical11

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

def phaseProjective11 (s : PhaseSolution11) : FullProjectiveSignal11 :=
  fullProjectiveOfSignal11 (phaseSolutionSignalEquiv11 s)

theorem phaseProjective11_injective : Function.Injective phaseProjective11 := by
  intro s t h
  exact phaseSolutionSignalEquiv11.injective
    (fullProjectiveOfSignal11_injective h)

private def LinearPreservesEvenOrbit11 (k : LinearFourierLabel11) : Prop :=
  ∀ s : PhaseSolution11, ∃ g : EvenSymmetry11,
    k • phaseProjective11 s = phaseProjective11 (g • s)

private theorem linearPreservesEvenOrbit_one11 :
    LinearPreservesEvenOrbit11 1 := by
  intro s
  exact ⟨1, by simp⟩

private theorem linearPreservesEvenOrbit_mul11
    {k l : LinearFourierLabel11}
    (hk : LinearPreservesEvenOrbit11 k)
    (hl : LinearPreservesEvenOrbit11 l) :
    LinearPreservesEvenOrbit11 (k * l) := by
  intro s
  obtain ⟨g, hg⟩ := hl s
  obtain ⟨h, hh⟩ := hk (g • s)
  refine ⟨h * g, ?_⟩
  calc
    (k * l) • phaseProjective11 s =
        k • (l • phaseProjective11 s) := by rw [mul_smul]
    _ = k • phaseProjective11 (g • s) := by rw [hg]
    _ = phaseProjective11 (h • (g • s)) := hh
    _ = phaseProjective11 ((h * g) • s) := by rw [mul_smul]

private theorem linearPreservesEvenOrbit_pow11
    {k : LinearFourierLabel11}
    (hk : LinearPreservesEvenOrbit11 k) (n : ℕ) :
    LinearPreservesEvenOrbit11 (k ^ n) := by
  induction n with
  | zero => simpa using linearPreservesEvenOrbit_one11
  | succ n ih =>
      rw [pow_succ]
      exact linearPreservesEvenOrbit_mul11 ih hk

private theorem linearPreservesEvenOrbit_D11 :
    LinearPreservesEvenOrbit11 linearD11 := by
  intro s
  refine ⟨phaseDilationGenerator11, ?_⟩
  change projectiveLinearFourierPerm11 linearD11 (phaseProjective11 s) =
    phaseProjective11 (phaseDilationGenerator11 • s)
  rw [projectiveLinearFourierPerm11_D]
  exact (fullProjectiveD2_11_phaseSolution s).symm

private theorem linearPreservesEvenOrbit_C11 :
    LinearPreservesEvenOrbit11 linearC11 := by
  intro s
  refine ⟨phaseConjugationGenerator11, ?_⟩
  change projectiveLinearFourierPerm11 linearC11 (phaseProjective11 s) =
    phaseProjective11 (phaseConjugationGenerator11 • s)
  rw [projectiveLinearFourierPerm11_C]
  exact (fullProjectiveConj11_phaseSolution s).symm

private theorem linearPreservesEvenOrbit_F11 :
    LinearPreservesEvenOrbit11 linearF11 := by
  intro s
  obtain ⟨g, hg⟩ := phaseSolution11_normalizedFourier_same_orbit s
  refine ⟨g, ?_⟩
  change projectiveLinearFourierPerm11 linearF11 (phaseProjective11 s) =
    phaseProjective11 (g • s)
  rw [projectiveLinearFourierPerm11_F, ← hg]
  exact (fullProjectiveFourier11_phaseSolution s).symm

theorem projectiveLinearFourier_phase_even_orbit
    (k : LinearFourierLabel11) (s : PhaseSolution11) :
    ∃ g : EvenSymmetry11,
      k • phaseProjective11 s = phaseProjective11 (g • s) := by
  have hD := linearPreservesEvenOrbit_pow11
    linearPreservesEvenOrbit_D11 k.dilate.val
  have hC : LinearPreservesEvenOrbit11
      (if k.conjugate then linearC11 else 1) := by
    split
    · exact linearPreservesEvenOrbit_C11
    · exact linearPreservesEvenOrbit_one11
  have hF : LinearPreservesEvenOrbit11
      (if k.fourier then linearF11 else 1) := by
    split
    · exact linearPreservesEvenOrbit_F11
    · exact linearPreservesEvenOrbit_one11
  rw [linearFourierLabel11_normal_form k]
  exact linearPreservesEvenOrbit_mul11
    (linearPreservesEvenOrbit_mul11 hD hC) hF s

/-- The ten normalized even symmetries sit inside the concrete
forty-element linear/Fourier group. -/
def evenToLinear11 : EvenSymmetry11 →* LinearFourierLabel11 where
  toFun g := linearD11 ^ (6 * g.toAdd.1.val) *
    linearC11 ^ g.toAdd.2.val
  map_one' := by native_decide
  map_mul' := by native_decide +revert

theorem evenToLinear11_D :
    evenToLinear11 phaseDilationGenerator11 = linearD11 ^ 6 := by
  native_decide

theorem evenToLinear11_C :
    evenToLinear11 phaseConjugationGenerator11 = linearC11 := by
  native_decide

private def EvenLinearEquivariant11 (g : EvenSymmetry11) : Prop :=
  ∀ s : PhaseSolution11,
    phaseProjective11 (g • s) = evenToLinear11 g • phaseProjective11 s

private theorem evenLinearEquivariant_one11 :
    EvenLinearEquivariant11 1 := by
  intro s
  simp

private theorem evenLinearEquivariant_mul11
    {g h : EvenSymmetry11}
    (hg : EvenLinearEquivariant11 g)
    (hh : EvenLinearEquivariant11 h) :
    EvenLinearEquivariant11 (g * h) := by
  intro s
  calc
    phaseProjective11 ((g * h) • s) =
        phaseProjective11 (g • (h • s)) := by rw [mul_smul]
    _ = evenToLinear11 g • phaseProjective11 (h • s) := hg (h • s)
    _ = evenToLinear11 g •
          (evenToLinear11 h • phaseProjective11 s) := by rw [hh]
    _ = evenToLinear11 (g * h) • phaseProjective11 s := by
      rw [map_mul, mul_smul]

private theorem evenLinearEquivariant_pow11
    {g : EvenSymmetry11}
    (hg : EvenLinearEquivariant11 g) (n : ℕ) :
    EvenLinearEquivariant11 (g ^ n) := by
  induction n with
  | zero => simpa using evenLinearEquivariant_one11
  | succ n ih =>
      rw [pow_succ]
      exact evenLinearEquivariant_mul11 ih hg

private theorem evenLinearEquivariant_D11 :
    EvenLinearEquivariant11 phaseDilationGenerator11 := by
  intro s
  have hD6 : linearD11 ^ 6 = linearR11 * linearD11 := by native_decide
  have hr (t : PhaseSolution11) :
      linearR11 • phaseProjective11 t = phaseProjective11 t := by
    change projectiveLinearFourierPerm11 linearR11 (phaseProjective11 t) =
      phaseProjective11 t
    rw [projectiveLinearFourierPerm11_R]
    exact fullProjectiveOfSignal11_reflection _
  have hDphys : linearD11 • phaseProjective11 s =
      phaseProjective11 (phaseDilationGenerator11 • s) := by
    change projectiveLinearFourierPerm11 linearD11 (phaseProjective11 s) =
      phaseProjective11 (phaseDilationGenerator11 • s)
    rw [projectiveLinearFourierPerm11_D]
    exact (fullProjectiveD2_11_phaseSolution s).symm
  change phaseProjective11 (phaseDilationGenerator11 • s) =
    projectiveLinearFourierPerm11
      (evenToLinear11 phaseDilationGenerator11) (phaseProjective11 s)
  rw [evenToLinear11_D, hD6, map_mul,
    Equiv.Perm.mul_apply,
    projectiveLinearFourierPerm11_D]
  change phaseProjective11 (phaseDilationGenerator11 • s) =
    linearR11 • (linearD11 • phaseProjective11 s)
  rw [hDphys, hr]

private theorem evenLinearEquivariant_C11 :
    EvenLinearEquivariant11 phaseConjugationGenerator11 := by
  intro s
  change phaseProjective11 (phaseConjugationGenerator11 • s) =
    projectiveLinearFourierPerm11
      (evenToLinear11 phaseConjugationGenerator11) (phaseProjective11 s)
  rw [evenToLinear11_C, projectiveLinearFourierPerm11_C]
  exact fullProjectiveConj11_phaseSolution s

theorem phaseProjective11_evenToLinear (g : EvenSymmetry11)
    (s : PhaseSolution11) :
    phaseProjective11 (g • s) = evenToLinear11 g • phaseProjective11 s := by
  have hD := evenLinearEquivariant_pow11 evenLinearEquivariant_D11
    g.toAdd.1.val
  have hC := evenLinearEquivariant_pow11 evenLinearEquivariant_C11
    g.toAdd.2.val
  rw [evenSymmetry11_generator_decomposition g]
  exact evenLinearEquivariant_mul11 hD hC s

/-- The concrete forty-element action has exactly the same orbit on a
normalized even solution as its free ten-element dilation/conjugation action. -/
def phaseEvenOrbitEquivLinearOrbit11 (s : PhaseSolution11) :
    EvenSymmetry11 ≃
      MulAction.orbit fullLinearSubgroup11 (phaseProjective11 s) := by
  let f : EvenSymmetry11 →
      MulAction.orbit fullLinearSubgroup11 (phaseProjective11 s) :=
    fun g => ⟨phaseProjective11 (g • s), by
      change ∃ k : fullLinearSubgroup11,
        k • phaseProjective11 s = phaseProjective11 (g • s)
      refine ⟨⟨SemidirectProduct.inr (evenToLinear11 g),
        ⟨evenToLinear11 g, rfl⟩⟩, ?_⟩
      change fullProjectiveSymmetryPerm11
        (SemidirectProduct.inr (evenToLinear11 g))
        (phaseProjective11 s) = phaseProjective11 (g • s)
      rw [fullProjectiveSymmetryPerm11_linear]
      exact (phaseProjective11_evenToLinear g s).symm⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro g h hgh
    have hp : phaseProjective11 (g • s) =
        phaseProjective11 (h • s) := congrArg Subtype.val hgh
    exact IsCancelSMul.right_cancel g h s
      (phaseProjective11_injective hp)
  · rintro ⟨z, hz⟩
    obtain ⟨k, hk⟩ := hz
    obtain ⟨j, hj⟩ := k.2
    change fullProjectiveSymmetryPerm11 k.1
      (phaseProjective11 s) = z at hk
    rw [← hj] at hk
    obtain ⟨g, hg⟩ := projectiveLinearFourier_phase_even_orbit j s
    refine ⟨g, Subtype.ext ?_⟩
    change phaseProjective11 (g • s) = z
    rw [← hk, fullProjectiveSymmetryPerm11_linear]
    exact hg.symm

theorem phaseProjective11_linear_orbit_card_ten (s : PhaseSolution11) :
    Fintype.card
      (MulAction.orbit fullLinearSubgroup11 (phaseProjective11 s)) = 10 := by
  rw [← Fintype.card_congr (phaseEvenOrbitEquivLinearOrbit11 s)]
  exact evenSymmetry11_card

/-- Every non-Gaussian normalized even phase solution has a concrete
1210-point orbit under the full Fourier/Weyl symmetry group. -/
theorem phaseProjective11_full_orbit_card_1210
    (s : PhaseSolution11)
    (hNonG : ¬ IsQuadraticGaussianSignal11
      (phaseSolutionSignalEquiv11 s)) :
    Fintype.card
      (MulAction.orbit FullSymmetryLabel11 (phaseProjective11 s)) = 1210 := by
  exact fullProjectiveOfSignal11_orbit_card_1210
    (phaseSolutionSignalEquiv11 s) hNonG
    (phaseProjective11_linear_orbit_card_ten s)

/-- Two normalized even non-Gaussian points in one full projective orbit
already lie in the same original ten-element even orbit. -/
theorem phaseProjective11_full_orbit_even_reduction
    (s t : PhaseSolution11)
    (hNonG_t : ¬ IsQuadraticGaussianSignal11
      (phaseSolutionSignalEquiv11 t))
    (h : phaseProjective11 t ∈
      MulAction.orbit FullSymmetryLabel11 (phaseProjective11 s)) :
    ∃ g : EvenSymmetry11, t = g • s := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨k, hk, hks⟩ := fullSymmetryLabel11_even_orbit_reduction
    (phaseProjective11 s) (phaseProjective11 t)
    (fullReflection11_fixed_signal _)
    (fullReflection11_fixed_signal _)
    (fullWeylSubgroup11_signal_stabilizer_trivial
      (phaseSolutionSignalEquiv11 t) hNonG_t)
    ha
  obtain ⟨j, hj⟩ := hk
  change fullProjectiveSymmetryPerm11 k
    (phaseProjective11 s) = phaseProjective11 t at hks
  rw [← hj, fullProjectiveSymmetryPerm11_linear] at hks
  obtain ⟨g, hg⟩ := projectiveLinearFourier_phase_even_orbit j s
  have hp : phaseProjective11 (g • s) = phaseProjective11 t :=
    hg.symm.trans hks
  exact ⟨g, (phaseProjective11_injective hp).symm⟩

end
end Biunimodular.F11
