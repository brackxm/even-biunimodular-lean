/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPhysicalAnalyticSigns77

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Biunimodular.F11

/-- The three displayed boxes represent precisely the three previously
certified A-sector candidate orbits. -/
theorem aSectorAnalyticRowBoxes77_symmetry_cover :
    ∀ q ∈ aSectorCandidateOrbitRepresentatives11,
      ∀ p ∈ candidateSymmetryOrbit11 q,
        ∃ r : Fin 3, ∃ g : EvenSymmetry11,
          candidateSymmetryImage11 g (aSectorAnalyticRowBoxes77[r.1]!).2 = p := by
  native_decide +revert

/-- Every actual A-sector solution is obtained from one of this construction's
explicit analytic representatives by dilation and conjugation. -/
theorem everyASectorPhase_eq_smul_analyticRepresentative77
    (s : PhaseSolution11) (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    ∃ r : Fin 3, ∃ g : EvenSymmetry11,
      s.1 = g • analyticASectorRepresentative77 r := by
  obtain ⟨q, hq, p, hp, hbox⟩ := everyASectorPhase_in_taggedBox11 s hA
  obtain ⟨r, g, hg⟩ := aSectorAnalyticRowBoxes77_symmetry_cover q hq p hp
  have hrow : aSectorAnalyticRowBoxes77[r.1]! ∈ aSectorAnalyticRowBoxes77 := by
    fin_cases r <;> decide
  have haccepted := (aSectorAnalyticRowBoxes77_accepted_certificate _ hrow).1
  let t : PhaseSolution11 := g⁻¹ • s
  have haction : g • t.1 = s.1 := by
    change g • (g⁻¹ • s.1) = s.1
    simp
  have htbox : phaseCandidateQuintupleBox11 (1 / 10000) t.1
      (aSectorAnalyticRowBoxes77[r.1]!).2 := by
    apply (phaseBox_symmetryImage_iff11 g t.1 _ haccepted).mp
    rw [hg, haction]
    exact hbox
  have ht : t.1 = analyticASectorRepresentative77 r := by
    apply phaseCirclePairsList77_injective
    rw [analyticASectorRepresentative77_pairs]
    exact phaseSolution_in_phaseBox_signed_analytic_row77 r t htbox
  exact ⟨r, g, haction.symm.trans (congrArg (fun x : PhaseCoords11 => g • x) ht)⟩

/-- Exact analytic classification of the A sector in the original phase
coordinates. Both existence and exhaustion are unconditional. -/
theorem phaseCoords11_aSector_iff_analytic77 (x : PhaseCoords11) :
    (x.IsPhaseSolution ∧ invariantAR.IsRoot (phaseInvariantU11 x)) ↔
      ∃ r : Fin 3, ∃ g : EvenSymmetry11,
        x = g • analyticASectorRepresentative77 r := by
  constructor
  · rintro ⟨hs, hA⟩
    exact everyASectorPhase_eq_smul_analyticRepresentative77 ⟨x, hs⟩ hA
  · rintro ⟨r, g, rfl⟩
    have hr := analyticASectorRepresentative77_isPhaseSolution r
    refine ⟨(phaseCoords11_isPhaseSolution_smul_iff g _).mpr hr.1, ?_⟩
    rw [phaseInvariantU11_smul]
    exact hr.2

end Biunimodular.F11
