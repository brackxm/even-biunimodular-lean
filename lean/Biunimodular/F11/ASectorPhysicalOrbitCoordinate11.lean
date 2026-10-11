/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPhysicalInvariantBoxes11

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open scoped IntermediateField

private def candidateDilationPow11 : ℕ → PhaseCandidateQuintuple11 →
    PhaseCandidateQuintuple11
  | 0, q => q
  | n + 1, q => candidateDilate11 (candidateDilationPow11 n q)

private def candidateConjugationPow11 : ℕ → PhaseCandidateQuintuple11 →
    PhaseCandidateQuintuple11
  | 0, q => q
  | n + 1, q => candidateConjugate11 (candidateConjugationPow11 n q)

private theorem candidateConjugationPow11_accepted
    (n : ℕ) (q : PhaseCandidateQuintuple11)
    (hq : q ∈ acceptedCandidateQuintuples) :
    candidateConjugationPow11 n q ∈ acceptedCandidateQuintuples := by
  induction n with
  | zero => simpa [candidateConjugationPow11] using hq
  | succ n ih =>
    simpa [candidateConjugationPow11] using
      acceptedCandidate_conjugate_mem _ ih

private theorem phaseBox_dilationPow_iff11
    (n : ℕ) (x : PhaseCoords11) (q : PhaseCandidateQuintuple11) :
    phaseCandidateQuintupleBox11 (1 / 10000)
      ((phaseDilationGenerator11 ^ n) • x)
      (candidateDilationPow11 n q) ↔
    phaseCandidateQuintupleBox11 (1 / 10000) x q := by
  induction n with
  | zero => simp [candidateDilationPow11]
  | succ n ih =>
    rw [pow_succ', mul_smul, phaseDilationGenerator11_smul]
    change phaseCandidateQuintupleBox11 (1 / 10000)
        (phaseDilate11 ((phaseDilationGenerator11 ^ n) • x))
        (candidateDilate11 (candidateDilationPow11 n q)) ↔ _
    rw [phaseCandidateQuintupleBox11_dilate_iff, ih]

private theorem phaseBox_conjugationPow_iff11
    (n : ℕ) (x : PhaseCoords11) (q : PhaseCandidateQuintuple11)
    (hq : q ∈ acceptedCandidateQuintuples) :
    phaseCandidateQuintupleBox11 (1 / 10000)
      ((phaseConjugationGenerator11 ^ n) • x)
      (candidateConjugationPow11 n q) ↔
    phaseCandidateQuintupleBox11 (1 / 10000) x q := by
  induction n with
  | zero => simp [candidateConjugationPow11]
  | succ n ih =>
    rw [pow_succ', mul_smul, phaseConjugationGenerator11_smul]
    change phaseCandidateQuintupleBox11 (1 / 10000)
        (phaseConjugate11 ((phaseConjugationGenerator11 ^ n) • x))
        (candidateConjugate11 (candidateConjugationPow11 n q)) ↔ _
    rw [phaseCandidateQuintupleBox11_conjugate_iff _ _ _
      (candidateConjugationPow11_accepted n q hq), ih]

def candidateSymmetryImage11
    (g : EvenSymmetry11) (q : PhaseCandidateQuintuple11) :
    PhaseCandidateQuintuple11 :=
  candidateDilationPow11 g.toAdd.1.val
    (candidateConjugationPow11 g.toAdd.2.val q)

theorem phaseBox_symmetryImage_iff11
    (g : EvenSymmetry11) (x : PhaseCoords11)
    (q : PhaseCandidateQuintuple11)
    (hq : q ∈ acceptedCandidateQuintuples) :
    phaseCandidateQuintupleBox11 (1 / 10000) (g • x)
      (candidateSymmetryImage11 g q) ↔
    phaseCandidateQuintupleBox11 (1 / 10000) x q := by
  have haction : g • x =
      (phaseDilationGenerator11 ^ g.toAdd.1.val) •
        ((phaseConjugationGenerator11 ^ g.toAdd.2.val) • x) := by
    conv_lhs => rw [evenSymmetry11_generator_decomposition g]
    rw [mul_smul]
  rw [haction]
  exact (phaseBox_dilationPow_iff11 _ _ _).trans
    (phaseBox_conjugationPow_iff11 _ _ _ hq)

private theorem aSectorCandidate_symmetryImage_mem11 :
    ∀ g : EvenSymmetry11,
      ∀ r ∈ aSectorCandidateOrbitRepresentatives11,
        candidateSymmetryImage11 g r ∈ candidateSymmetryOrbit11 r := by
  native_decide +revert

private theorem aSectorCandidate_symmetryImage_surj11 :
    ∀ r ∈ aSectorCandidateOrbitRepresentatives11,
      ∀ q ∈ candidateSymmetryOrbit11 r,
        ∃ g : EvenSymmetry11, candidateSymmetryImage11 g r = q := by
  native_decide +revert

/-- Every physical phase in an A-tagged candidate box has an invariant root
of the sextic A factor. -/
theorem phaseSolution_invariantA_of_taggedBox11
    (s : PhaseSolution11) (r q : PhaseCandidateQuintuple11)
    (hr : r ∈ aSectorCandidateOrbitRepresentatives11)
    (hq : q ∈ candidateSymmetryOrbit11 r)
    (hbox : phaseCandidateQuintupleBox11 (1 / 10000) s.1 q) :
    invariantAR.IsRoot (phaseInvariantU11 s.1) := by
  obtain ⟨g, hg⟩ := aSectorCandidate_symmetryImage_surj11 r hr q hq
  let t : PhaseSolution11 := g⁻¹ • s
  have hrAccepted : r ∈ acceptedCandidateQuintuples := by
    have h : ∀ r ∈ aSectorCandidateOrbitRepresentatives11,
        r ∈ acceptedCandidateQuintuples := by native_decide
    exact h r hr
  have haction : g • t.1 = s.1 := by
    change g • (g⁻¹ • s.1) = s.1
    simp
  have htbox : phaseCandidateQuintupleBox11 (1 / 10000) t.1 r := by
    have htransport := (phaseBox_symmetryImage_iff11 g t.1 r hrAccepted).1
    rw [hg, haction] at htransport
    exact htransport hbox
  have htA := aSectorRepresentativeBox_invariantA11 t r hr htbox
  have hv : phaseInvariantU11 t.1 = phaseInvariantU11 s.1 := by
    change phaseInvariantU11 (g⁻¹ • s.1) = _
    exact phaseInvariantU11_smul _ _
  rw [← hv]
  exact htA

/-- A physical phase has an A invariant exactly when its accepted box is in
one of the three degree-thirty A-tagged candidate orbits. -/
theorem everyASectorPhase_in_taggedBox11
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    ∃ r ∈ aSectorCandidateOrbitRepresentatives11,
      ∃ q ∈ candidateSymmetryOrbit11 r,
        phaseCandidateQuintupleBox11 (1 / 10000) s.1 q := by
  obtain ⟨r, hr, t, hbox, horbit⟩ :=
    everyASectorPhase_sameOrbitRepresentative11 s hA
  have hrel := Quotient.exact horbit
  change MulAction.orbitRel EvenSymmetry11 PhaseSolution11 s t at hrel
  rw [MulAction.orbitRel_apply] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hs : s.1 = g • t.1 := by
    have h := congrArg Subtype.val hg.symm
    change s.1 = g • t.1 at h
    exact h
  let q := candidateSymmetryImage11 g r
  refine ⟨r, hr, q, aSectorCandidate_symmetryImage_mem11 g r hr, ?_⟩
  rw [hs]
  have hrAccepted : r ∈ acceptedCandidateQuintuples := by
    have h : ∀ r ∈ aSectorCandidateOrbitRepresentatives11,
        r ∈ acceptedCandidateQuintuples := by native_decide
    exact h r hr
  exact (phaseBox_symmetryImage_iff11 g t.1 r hrAccepted).2 hbox

/-- The sextic A invariant sector is precisely the union of the three
A-tagged ten-box symmetry orbits in the exact finite scan. -/
theorem phaseSolution_invariantA_iff_taggedBox11
    (s : PhaseSolution11) :
    invariantAR.IsRoot (phaseInvariantU11 s.1) ↔
      ∃ r ∈ aSectorCandidateOrbitRepresentatives11,
        ∃ q ∈ candidateSymmetryOrbit11 r,
          phaseCandidateQuintupleBox11 (1 / 10000) s.1 q := by
  constructor
  · exact everyASectorPhase_in_taggedBox11 s
  · rintro ⟨r, hr, q, hq, hbox⟩
    exact phaseSolution_invariantA_of_taggedBox11 s r q hr hq hbox

/-- Every actual A-sector phase coordinate has the degree-thirty monic
polynomial of the maximal real conductor-77 field. -/
theorem everyASectorPhase_G30_minpoly11
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    minpoly ℚ (4 * s.1.k ^ 2 : ℝ) =
      aSectorG30.map (Int.castRingHom ℚ) := by
  obtain ⟨r, hr, q, hq, hbox⟩ := everyASectorPhase_in_taggedBox11 s hA
  exact phaseSolution_G30_minpoly_of_aSectorCandidateBox
    s r q hr hq hbox

/-- The squared last coordinate of every physical A-sector solution
generates a number field isomorphic to the maximal real conductor-77 field. -/
noncomputable def everyASectorPhase_squareCoordinateFieldEquivMaxReal11
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    ℚ⟮(4 * s.1.k ^ 2 : ℝ)⟯ ≃ₐ[ℚ] Conductor77MaxReal := by
  let hw := everyASectorPhase_in_taggedBox11 s hA
  let r := Classical.choose hw
  have hrw := Classical.choose_spec hw
  let q := Classical.choose hrw.2
  have hqw := Classical.choose_spec hrw.2
  exact phaseSolution_squareCoordinateFieldEquivMaxReal
    s r q hrw.1 hqw.1 hqw.2

/-- Dilation lets the degree-thirty statement apply to each of the five
imaginary phase coordinates. -/
theorem everyASectorPhase_all_G30_minpoly11
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    (∀ y ∈ [s.1.b, s.1.d, s.1.f, s.1.h, s.1.k],
      minpoly ℚ (4 * y ^ 2 : ℝ) =
        aSectorG30.map (Int.castRingHom ℚ)) := by
  let g := phaseDilationGenerator11
  have hrot (n : ℕ) :
      invariantAR.IsRoot (phaseInvariantU11 ((g ^ n • s).1)) := by
    have hv : phaseInvariantU11 ((g ^ n • s).1) =
        phaseInvariantU11 s.1 := by
      change phaseInvariantU11 ((g ^ n) • s.1) = _
      exact phaseInvariantU11_smul _ _
    rw [hv]
    exact hA
  have hn (n : ℕ) :=
    everyASectorPhase_G30_minpoly11 (g ^ n • s) (hrot n)
  have h1 : ((g ^ 1 • s).1).k = s.1.b := by
    change ((g ^ 1) • s.1).k = s.1.b
    simp [g, phaseDilationGenerator11_smul, phaseDilate11]
  have h2 : ((g ^ 2 • s).1).k = s.1.d := by
    change ((g ^ 2) • s.1).k = s.1.d
    simp [g, pow_succ', mul_smul, phaseDilationGenerator11_smul,
      phaseDilate11]
  have h3 : ((g ^ 3 • s).1).k = s.1.h := by
    change ((g ^ 3) • s.1).k = s.1.h
    simp [g, pow_succ', mul_smul, phaseDilationGenerator11_smul,
      phaseDilate11]
  have h4 : ((g ^ 4 • s).1).k = s.1.f := by
    change ((g ^ 4) • s.1).k = s.1.f
    simp [g, pow_succ', mul_smul, phaseDilationGenerator11_smul,
      phaseDilate11]
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl
  · simpa only [h1] using hn 1
  · simpa only [h2] using hn 2
  · simpa only [h4] using hn 4
  · simpa only [h3] using hn 3
  · exact everyASectorPhase_G30_minpoly11 s hA

/-- The field identification depends only on the common degree-thirty
minimal polynomial, so it applies to every imaginary coordinate. -/
noncomputable def aSectorCoordinateFieldEquivMaxReal11
    (y : ℝ)
    (hy : minpoly ℚ (4 * y ^ 2 : ℝ) =
      aSectorG30.map (Int.castRingHom ℚ)) :
    ℚ⟮(4 * y ^ 2 : ℝ)⟯ ≃ₐ[ℚ] Conductor77MaxReal := by
  let x : ℝ := 4 * y ^ 2
  have hxmin : minpoly ℚ x = minpoly ℚ aSectorX77Real := by
    rw [hy, ← aSectorX77Real_minpoly]
  have hx : IsIntegral ℚ x :=
    minpoly.ne_zero_iff.mp (by
      rw [hxmin]
      exact (minpoly.monic (IsIntegral.of_finite ℚ aSectorX77Real)).ne_zero)
  have hz : IsIntegral ℚ aSectorX77Real :=
    IsIntegral.of_finite ℚ aSectorX77Real
  have htop : ℚ⟮aSectorX77Real⟯ =
      (⊤ : IntermediateField ℚ Conductor77MaxReal) :=
    IntermediateField.adjoin_eq_top_iff.mpr
      aSectorX77Real_generates_maxReal
  exact (IntermediateField.adjoinRootEquivAdjoin ℚ hx).symm.trans
    ((AdjoinRoot.algEquivOfEq ℚ _ _ hxmin).trans
      ((IntermediateField.adjoinRootEquivAdjoin ℚ hz).trans
        ((IntermediateField.equivOfEq htop).trans
          IntermediateField.topEquiv)))

theorem aSectorCoordinateFieldEquivMaxReal11_gen
    (y : ℝ)
    (hy : minpoly ℚ (4 * y ^ 2 : ℝ) =
      aSectorG30.map (Int.castRingHom ℚ)) :
    aSectorCoordinateFieldEquivMaxReal11 y hy
      (IntermediateField.AdjoinSimple.gen ℚ (4 * y ^ 2 : ℝ)) = aSectorX77Real := by
  unfold aSectorCoordinateFieldEquivMaxReal11
  simp only [AlgEquiv.trans_apply,
    IntermediateField.adjoinRootEquivAdjoin_symm_apply_gen,
    AdjoinRoot.algEquivOfEq_root,
    IntermediateField.adjoinRootEquivAdjoin_apply_root]
  rfl

/-- Each physical squared coordinate determines a rational embedding of the
explicit conductor-77 real field into the real numbers. -/
noncomputable def aSectorCoordinateEmbedding11
    (y : ℝ)
    (hy : minpoly ℚ (4 * y ^ 2 : ℝ) =
      aSectorG30.map (Int.castRingHom ℚ)) :
    Conductor77MaxReal →ₐ[ℚ] ℝ :=
  (IntermediateField.val ℚ⟮(4 * y ^ 2 : ℝ)⟯).comp
    (aSectorCoordinateFieldEquivMaxReal11 y hy).symm.toAlgHom

theorem aSectorCoordinateEmbedding11_generator
    (y : ℝ)
    (hy : minpoly ℚ (4 * y ^ 2 : ℝ) =
      aSectorG30.map (Int.castRingHom ℚ)) :
    aSectorCoordinateEmbedding11 y hy aSectorX77Real = 4 * y ^ 2 := by
  have hgen := aSectorCoordinateFieldEquivMaxReal11_gen y hy
  have h := congrArg (aSectorCoordinateFieldEquivMaxReal11 y hy).symm hgen
  simp only [AlgEquiv.symm_apply_apply] at h
  change IntermediateField.AdjoinSimple.gen ℚ (4 * y ^ 2 : ℝ) =
    (aSectorCoordinateFieldEquivMaxReal11 y hy).symm aSectorX77Real at h
  simp only [aSectorCoordinateEmbedding11, AlgHom.comp_apply]
  change (((aSectorCoordinateFieldEquivMaxReal11 y hy).symm
    aSectorX77Real : ℚ⟮(4 * y ^ 2 : ℝ)⟯) : ℝ) = 4 * y ^ 2
  rw [← h]
  exact IntermediateField.AdjoinSimple.coe_gen ℚ (4 * y ^ 2 : ℝ)

theorem everyASectorPhase_all_coordinate_fields11
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    ∀ y ∈ [s.1.b, s.1.d, s.1.f, s.1.h, s.1.k],
      Nonempty (ℚ⟮(4 * y ^ 2 : ℝ)⟯ ≃ₐ[ℚ] Conductor77MaxReal) := by
  intro y hy
  exact ⟨aSectorCoordinateFieldEquivMaxReal11 y
    (everyASectorPhase_all_G30_minpoly11 s hA y hy)⟩

/-- For every physical A-sector phase coordinate, some rational embedding of
the explicit real cyclotomic field sends its degree-thirty generator to that
coordinate's scaled square. -/
theorem everyASectorPhase_coordinate_cyclotomicEmbedding11
    (s : PhaseSolution11)
    (hA : invariantAR.IsRoot (phaseInvariantU11 s.1)) :
    ∀ y ∈ [s.1.b, s.1.d, s.1.f, s.1.h, s.1.k],
      ∃ φ : Conductor77MaxReal →ₐ[ℚ] ℝ,
        φ aSectorX77Real = 4 * y ^ 2 := by
  intro y hy
  let hmin := everyASectorPhase_all_G30_minpoly11 s hA y hy
  exact ⟨aSectorCoordinateEmbedding11 y hmin,
    aSectorCoordinateEmbedding11_generator y hmin⟩

end Biunimodular.F11
