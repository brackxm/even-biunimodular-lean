/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryProjectiveFourierPhysical11

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open scoped ComplexConjugate LinearAlgebra.Projectivization

noncomputable section

private theorem d2Val11 (x : ZMod 11) :
    (2 * x).val = (2 * x.val) % 11 := by native_decide +revert

theorem phaseOnZMod11_dilation_generator (s : PhaseSolution11) :
    phaseOnZMod11 (phaseDilationGenerator11 • s).1 =
      fullD2Linear11 (phaseOnZMod11 s.1) := by
  funext x
  rw [show (phaseDilationGenerator11 • s).1 =
      phaseDilate11 s.1 from phaseDilationGenerator11_smul s.1]
  change phaseSignal11 (phaseDilate11 s.1) ⟨x.val, x.val_lt⟩ =
    phaseSignal11 s.1 ⟨(2 * x).val, (2 * x).val_lt⟩
  have hidx : (⟨(2 * x).val, (2 * x).val_lt⟩ : Fin 11) =
      ⟨(2 * x.val) % 11, Nat.mod_lt _ (by norm_num)⟩ :=
    Fin.ext (d2Val11 x)
  rw [hidx]
  fin_cases x <;> norm_num [ZMod.val, phaseSignal11, phaseDilate11, phaseC]

theorem phaseOnZMod11_conjugation_generator (s : PhaseSolution11) :
    phaseOnZMod11 (phaseConjugationGenerator11 • s).1 =
      fullConjSignal11 (phaseOnZMod11 s.1) := by
  funext x
  rw [show (phaseConjugationGenerator11 • s).1 =
      phaseConjugate11 s.1 from phaseConjugationGenerator11_smul s.1]
  fin_cases x <;> norm_num [ZMod.val, phaseOnZMod11, phaseSignal11,
    phaseConjugate11, fullConjSignal11, phaseC, Complex.ext_iff]

theorem fullProjectiveD2_11_phaseSolution (s : PhaseSolution11) :
    fullProjectiveOfSignal11
      (phaseSolutionSignalEquiv11 (phaseDilationGenerator11 • s)) =
    fullProjectiveD2_11
      (fullProjectiveOfSignal11 (phaseSolutionSignalEquiv11 s)) := by
  simp only [fullProjectiveOfSignal11, fullProjectiveD2_11_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨1, ?_⟩
  simpa only [one_smul, phaseSignalEquiv11_fullSignal] using
    (phaseOnZMod11_dilation_generator s).symm

theorem fullProjectiveConj11_phaseSolution (s : PhaseSolution11) :
    fullProjectiveOfSignal11
      (phaseSolutionSignalEquiv11 (phaseConjugationGenerator11 • s)) =
    fullProjectiveConj11
      (fullProjectiveOfSignal11 (phaseSolutionSignalEquiv11 s)) := by
  simp only [fullProjectiveOfSignal11, fullProjectiveConj11_mk]
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨1, ?_⟩
  simpa only [one_smul, phaseSignalEquiv11_fullSignal] using
    (phaseOnZMod11_conjugation_generator s).symm

end
end Biunimodular.F11
