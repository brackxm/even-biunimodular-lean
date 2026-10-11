/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.CenterTailScaling
public import Biunimodular.F11.FinitePhaseScanDataReconstructed
public import Biunimodular.F11.PhaseSymmetry11
public meta import Biunimodular.F11.ProofTactics
public meta import Biunimodular.F11.CenterTailScaling
public meta import Biunimodular.F11.FinitePhaseScanDataReconstructed
public meta import Biunimodular.F11.PhaseSymmetry11

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Symmetry orbits of the 80 accepted phase boxes

The candidate tuples use additive phase order `(a,c,e,g,j)`.  Dilation sends
that order to `(c,g,j,e,a)`, while conjugation flips the low bit of each
fixed-point center index.  The finite theorems below certify that the 80
accepted scanner tuples split into eight disjoint ten-element candidate
orbits.
-/

abbrev PhaseCandidateQuintuple11 := Nat × Nat × Nat × Nat × Nat

/-- The finite type of tuples accepted by the exact scanner. -/
abbrev AcceptedPhaseCandidate11 :=
  ↥acceptedCandidateQuintuples.toFinset

/-- A ten-coordinate open box around one scanner tuple. -/
def phaseCandidateQuintupleBox11
    (δ : ℝ) (x : PhaseCoords11)
    (q : PhaseCandidateQuintuple11) : Prop :=
  match q with
  | (ia, ic, ie, ig, ij) =>
      |x.a - centerCoordR (phaseCenters160[ia]!).re| < δ ∧
      |x.b - centerCoordR (phaseCenters160[ia]!).im| < δ ∧
      |x.c - centerCoordR (phaseCenters160[ic]!).re| < δ ∧
      |x.d - centerCoordR (phaseCenters160[ic]!).im| < δ ∧
      |x.e - centerCoordR (phaseCenters160[ie]!).re| < δ ∧
      |x.f - centerCoordR (phaseCenters160[ie]!).im| < δ ∧
      |x.g - centerCoordR (phaseCenters160[ig]!).re| < δ ∧
      |x.h - centerCoordR (phaseCenters160[ig]!).im| < δ ∧
      |x.j - centerCoordR (phaseCenters160[ij]!).re| < δ ∧
      |x.k - centerCoordR (phaseCenters160[ij]!).im| < δ

/-- Conjugation exchanges the two imaginary signs within each consecutive
pair of fixed-point center indices. -/
def candidateConjugateIndex11 (i : Nat) : Nat :=
  if i % 2 = 0 then i + 1 else i - 1

theorem candidateConjugateIndex11_lt (i : Fin 160) :
    candidateConjugateIndex11 i.1 < 160 := by
  unfold candidateConjugateIndex11
  split <;> omega

/-- The fixed-point center table implements complex conjugation by flipping
the low index bit. -/
theorem phaseCenter_candidateConjugateIndex11 (i : Fin 160) :
    (phaseCenters160[candidateConjugateIndex11 i.1]!).re =
        (phaseCenters160[i.1]!).re ∧
      (phaseCenters160[candidateConjugateIndex11 i.1]!).im =
        -(phaseCenters160[i.1]!).im := by
  native_decide +revert

theorem phaseCenterR_candidateConjugateIndex11
    (i : Nat) (hi : i < 160) :
    centerCoordR (phaseCenters160[candidateConjugateIndex11 i]!).re =
        centerCoordR (phaseCenters160[i]!).re ∧
      centerCoordR (phaseCenters160[candidateConjugateIndex11 i]!).im =
        -centerCoordR (phaseCenters160[i]!).im := by
  have h := phaseCenter_candidateConjugateIndex11 (⟨i, hi⟩ : Fin 160)
  constructor
  · exact congrArg centerCoordR h.1
  · rw [h.2]
    simp only [centerCoordR, Int.cast_neg]
    ring

/-- Dilation in additive phase order `(a,c,e,g,j)`. -/
def candidateDilate11
    (q : PhaseCandidateQuintuple11) : PhaseCandidateQuintuple11 :=
  match q with
  | (ia, ic, ie, ig, ij) => (ic, ig, ij, ie, ia)

/-- Simultaneous conjugation of a candidate quintuple. -/
def candidateConjugate11
    (q : PhaseCandidateQuintuple11) : PhaseCandidateQuintuple11 :=
  match q with
  | (ia, ic, ie, ig, ij) =>
      (candidateConjugateIndex11 ia, candidateConjugateIndex11 ic,
        candidateConjugateIndex11 ie, candidateConjugateIndex11 ig,
        candidateConjugateIndex11 ij)

/-- The five dilation translates of one candidate box. -/
def candidateDilationOrbit11
    (q : PhaseCandidateQuintuple11) : List PhaseCandidateQuintuple11 :=
  [q, candidateDilate11 q, candidateDilate11 (candidateDilate11 q),
    candidateDilate11 (candidateDilate11 (candidateDilate11 q)),
    candidateDilate11
      (candidateDilate11 (candidateDilate11 (candidateDilate11 q)))]

/-- The ten dilation/conjugation translates of one candidate box. -/
def candidateSymmetryOrbit11
    (q : PhaseCandidateQuintuple11) : List PhaseCandidateQuintuple11 :=
  candidateDilationOrbit11 q ++
    (candidateDilationOrbit11 q).map candidateConjugate11

/-- Canonical representatives of the eight candidate symmetry orbits. -/
def acceptedCandidateOrbitRepresentatives11 :
    List PhaseCandidateQuintuple11 :=
  [(0, 15, 6, 16, 8),
    (22, 76, 71, 33, 31),
    (26, 61, 40, 55, 65),
    (36, 56, 73, 46, 50),
    (82, 119, 140, 101, 114),
    (84, 149, 124, 120, 106),
    (88, 108, 153, 130, 138),
    (92, 156, 132, 147, 98)]

theorem acceptedCandidateOrbitRepresentatives11_length :
    acceptedCandidateOrbitRepresentatives11.length = 8 := by
  native_decide

theorem acceptedPhaseCandidate11_card :
    Fintype.card AcceptedPhaseCandidate11 = 80 := by
  native_decide

/-- Every displayed candidate orbit has the full order-ten size. -/
theorem acceptedCandidate_symmetry_orbits_nodup :
    ∀ r ∈ acceptedCandidateOrbitRepresentatives11,
      (candidateSymmetryOrbit11 r).Nodup ∧
        (candidateSymmetryOrbit11 r).length = 10 := by
  native_decide

/-- The eight displayed candidate orbits are pairwise disjoint. -/
theorem acceptedCandidate_symmetry_orbits_pairwise_disjoint :
    acceptedCandidateOrbitRepresentatives11.Pairwise fun r s =>
      Disjoint (candidateSymmetryOrbit11 r).toFinset
        (candidateSymmetryOrbit11 s).toFinset := by
  native_decide

/-- The eight candidate orbits exhaust exactly the 80 accepted scanner
tuples. -/
theorem acceptedCandidateQuintuples_eq_symmetry_orbits :
    acceptedCandidateQuintuples.toFinset =
      (acceptedCandidateOrbitRepresentatives11.flatMap
        candidateSymmetryOrbit11).toFinset := by
  native_decide

/-- Every coordinate index in an accepted tuple points into the 160-element
center table. -/
theorem acceptedCandidate_indices_lt :
    ∀ q ∈ acceptedCandidateQuintuples,
      match q with
      | (ia, ic, ie, ig, ij) =>
          ia < 160 ∧ ic < 160 ∧ ie < 160 ∧ ig < 160 ∧ ij < 160 := by
  native_decide

theorem acceptedCandidate_dilate_mem
    (q : PhaseCandidateQuintuple11)
    (hq : q ∈ acceptedCandidateQuintuples) :
    candidateDilate11 q ∈ acceptedCandidateQuintuples := by
  revert q
  native_decide

theorem acceptedCandidate_conjugate_mem
    (q : PhaseCandidateQuintuple11)
    (hq : q ∈ acceptedCandidateQuintuples) :
    candidateConjugate11 q ∈ acceptedCandidateQuintuples := by
  revert q
  native_decide

/-- Candidate dilation is exactly the coordinate dilation on phase boxes. -/
theorem phaseCandidateQuintupleBox11_dilate_iff
    (δ : ℝ) (x : PhaseCoords11) (q : PhaseCandidateQuintuple11) :
    phaseCandidateQuintupleBox11 δ (phaseDilate11 x)
        (candidateDilate11 q) ↔
      phaseCandidateQuintupleBox11 δ x q := by
  rcases q with ⟨ia, ic, ie, ig, ij⟩
  simp only [phaseCandidateQuintupleBox11, candidateDilate11, phaseDilate11]
  tauto

/-- Candidate conjugation is exactly coordinatewise complex conjugation on
every accepted phase box. -/
theorem phaseCandidateQuintupleBox11_conjugate_iff
    (δ : ℝ) (x : PhaseCoords11) (q : PhaseCandidateQuintuple11)
    (hq : q ∈ acceptedCandidateQuintuples) :
    phaseCandidateQuintupleBox11 δ (phaseConjugate11 x)
        (candidateConjugate11 q) ↔
      phaseCandidateQuintupleBox11 δ x q := by
  rcases q with ⟨ia, ic, ie, ig, ij⟩
  have hb := acceptedCandidate_indices_lt (ia, ic, ie, ig, ij) hq
  dsimp only at hb
  rcases hb with ⟨hia, hic, hie, hig, hij⟩
  have ha := phaseCenterR_candidateConjugateIndex11 ia hia
  have hc := phaseCenterR_candidateConjugateIndex11 ic hic
  have he := phaseCenterR_candidateConjugateIndex11 ie hie
  have hg := phaseCenterR_candidateConjugateIndex11 ig hig
  have hj := phaseCenterR_candidateConjugateIndex11 ij hij
  have hneg (u v : ℝ) : |-u - -v| = |u - v| := by
    rw [show -u - -v = -(u - v) by ring, abs_neg]
  simp only [phaseCandidateQuintupleBox11, candidateConjugate11,
    phaseConjugate11]
  rw [ha.1, ha.2, hc.1, hc.2, he.1, he.2, hg.1, hg.2, hj.1, hj.2]
  simp only [hneg]

/-- Elementwise form of the exact eight-orbit decomposition. -/
theorem acceptedCandidate_mem_symmetry_orbit
    (q : PhaseCandidateQuintuple11)
    (hq : q ∈ acceptedCandidateQuintuples) :
    ∃ r ∈ acceptedCandidateOrbitRepresentatives11,
      q ∈ candidateSymmetryOrbit11 r := by
  have hq' : q ∈ acceptedCandidateQuintuples.toFinset := by simpa using hq
  rw [acceptedCandidateQuintuples_eq_symmetry_orbits] at hq'
  simpa using hq'

end Biunimodular.F11
