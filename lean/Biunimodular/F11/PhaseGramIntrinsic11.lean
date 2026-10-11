/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.RealRankTwoGram
import Biunimodular.F11.PhaseGramQuotient11
import Mathlib.Algebra.Group.Action.TransferInstance

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

/-- The intrinsic real Gram locus: positive semidefiniteness, rank at most
two, diagonal two, and the five linear autocorrelation relations. -/
def phaseGramIntrinsicSet11 : Set (Matrix (Fin 6) (Fin 6) ℝ) :=
  {K | K.PosSemidef ∧ K.rank ≤ 2 ∧ (∀ i, K i i = 2) ∧
    PhaseGramLinearRelations11 K}

abbrev PhaseGramIntrinsicLocus11 := phaseGramIntrinsicSet11

/-- Every matrix satisfying the intrinsic conditions reconstructs an actual
normalized phase solution, with exactly that Gram matrix. -/
theorem phaseGramIntrinsic11_reconstruction
    (K : Matrix (Fin 6) (Fin 6) ℝ) (hK : K ∈ phaseGramIntrinsicSet11) :
    ∃ s : PhaseSolution11, phaseSolution11GramMap s = K := by
  obtain ⟨y, hy0, hyc, hyg⟩ := real_psd_rank_le_two_normalized_gram
    K (0 : Fin 6) hK.1 hK.2.1 hK.2.2.1
  let x : PhaseCoords11 :=
    ⟨(y 1).re, (y 1).im, (y 2).re, (y 2).im,
      (y 4).re, (y 4).im, (y 3).re, (y 3).im,
      (y 5).re, (y 5).im⟩
  have hx : x.CircleEquations :=
    ⟨hyc 1, hyc 2, hyc 4, hyc 3, hyc 5⟩
  have hvalues : phaseGramValues11 x = y := by
    funext i
    fin_cases i
    · exact hy0.symm
    all_goals rfl
  have hgram : phaseGramMatrix11 x = K := by
    ext i j
    rw [phaseGramMatrix11_apply, hvalues]
    exact (hyg i j).symm
  have hs : x.IsPhaseSolution :=
    (phaseGramMatrix11_linearRelations_iff x hx).mp
      (hgram.symm ▸ hK.2.2.2)
  exact ⟨⟨x, hs⟩, hgram⟩

/-- The image locus equals the intrinsic PSD rank-two locus. -/
theorem phaseGramLocus11_eq_intrinsic :
    Set.range phaseSolution11GramMap = phaseGramIntrinsicSet11 := by
  ext K
  constructor
  · intro h
    obtain ⟨_, hp, hd, hr, hl⟩ :=
      phaseGramLocus11_properties (⟨K, h⟩ : PhaseGramLocus11)
    exact ⟨hp, hr, hd, hl⟩
  · exact phaseGramIntrinsic11_reconstruction K

/-- Matrix-preserving equivalence between the image and intrinsic loci. -/
def phaseGramLocus11IntrinsicEquiv :
    PhaseGramLocus11 ≃ PhaseGramIntrinsicLocus11 :=
  Set.equivOfEq phaseGramLocus11_eq_intrinsic

@[simp] theorem phaseGramLocus11IntrinsicEquiv_val (K : PhaseGramLocus11) :
    (phaseGramLocus11IntrinsicEquiv K).val = K.val := rfl

/-- Phases modulo simultaneous conjugation are exactly the intrinsic real
positive semidefinite rank-two Gram matrices. -/
def phaseSolution11ConjQuotientIntrinsicGramEquiv :
    AddAction.orbitRel.Quotient Bool PhaseSolution11 ≃ PhaseGramIntrinsicLocus11 :=
  phaseSolution11ConjQuotientGramEquiv.trans phaseGramLocus11IntrinsicEquiv

instance : AddAction (ZMod 5) PhaseGramIntrinsicLocus11 :=
  phaseGramLocus11IntrinsicEquiv.symm.addAction (ZMod 5)

/-- The transported action is exactly cyclic relabelling of the actual
matrix entries. -/
@[simp] theorem phaseGramIntrinsic11_vadd_val
    (r : ZMod 5) (K : PhaseGramIntrinsicLocus11) :
    (r +ᵥ K).val = phaseGramRelabelMatrix11 r K.val := rfl

theorem phaseGramLocus11IntrinsicEquiv_orbitRel (K L : PhaseGramLocus11) :
    AddAction.orbitRel (ZMod 5) PhaseGramLocus11 K L ↔
      AddAction.orbitRel (ZMod 5) PhaseGramIntrinsicLocus11
        (phaseGramLocus11IntrinsicEquiv K) (phaseGramLocus11IntrinsicEquiv L) := by
  simp only [AddAction.orbitRel_apply]
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    change phaseGramLocus11IntrinsicEquiv (r +ᵥ L) = phaseGramLocus11IntrinsicEquiv K
    exact congrArg phaseGramLocus11IntrinsicEquiv hr
  · rintro ⟨r, hr⟩
    refine ⟨r, phaseGramLocus11IntrinsicEquiv.injective ?_⟩
    exact hr

abbrev PhaseGramIntrinsicOrbit11 :=
  AddAction.orbitRel.Quotient (ZMod 5) PhaseGramIntrinsicLocus11

/-- The Gram orbit equivalence uses the intrinsic matrix conditions. -/
def phaseGramOrbit11IntrinsicEquiv : PhaseGramOrbit11 ≃ PhaseGramIntrinsicOrbit11 :=
  Quotient.congr phaseGramLocus11IntrinsicEquiv
    phaseGramLocus11IntrinsicEquiv_orbitRel

/-- The physical order-ten orbit quotient equals the cyclic quotient of the
intrinsic Gram locus, including the converse for arbitrary PSD matrices. -/
def phaseSolution11OrbitIntrinsicGramEquiv :
    PhaseSolution11Orbit ≃ PhaseGramIntrinsicOrbit11 :=
  phaseSolution11OrbitGramEquiv.trans phaseGramOrbit11IntrinsicEquiv

def phaseGramIntrinsicOrbitInvariantU11 (q : PhaseGramIntrinsicOrbit11) : ℝ :=
  phaseGramOrbitInvariantU11 (phaseGramOrbit11IntrinsicEquiv.symm q)

@[simp] theorem phaseGramIntrinsicOrbitInvariantU11_mk
    (K : PhaseGramIntrinsicLocus11) :
    phaseGramIntrinsicOrbitInvariantU11 (Quotient.mk'' K) =
      phaseGramSigma11 K.val ^ 2 / 11 := rfl

theorem phaseSolution11OrbitIntrinsicGramEquiv_value (q : PhaseSolution11Orbit) :
    phaseGramIntrinsicOrbitInvariantU11 (phaseSolution11OrbitIntrinsicGramEquiv q) =
      phaseSolution11OrbitInvariantU q := by
  simp only [phaseGramIntrinsicOrbitInvariantU11, phaseSolution11OrbitIntrinsicGramEquiv,
    Equiv.trans_apply, Equiv.symm_apply_apply]
  exact phaseSolution11OrbitGramEquiv_value q

end

end Biunimodular.F11
