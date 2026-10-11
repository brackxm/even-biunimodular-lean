/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FixedSliceQuotientGeometry
import Biunimodular.F11.PhaseGramQuotient11
import Biunimodular.F11.PhaseClassification11

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

/-!
# The concrete Gram-to-fixed-slice bridge

This module replaces the arbitrary physical orbit/root equivalence in the
generic normalized even classification assembly by two semantic spectrum certificates: one for
the actual fixed-slice quotient coordinate and one for the actual rank-two
Gram coordinate.  Both maps land in the same certified root space by their
concrete `u` values.
-/

/-- The eight-point physical part of the concrete fixed-slice quotient. -/
abbrev Even11PhysicalFixedSliceQuotient
    (F : Even11FixedSliceGeometryCertificate) :=
  {y : Even11FixedSliceFourierQuotient //
    fixedSliceQuotientRootSplit (F.quotientRootEquiv y)}

/-- Restrict the concrete fixed-slice quotient/root equivalence to its eight
split points. -/
noncomputable def Even11FixedSliceGeometryCertificate.splitRootEquiv
    (F : Even11FixedSliceGeometryCertificate) :
    Even11PhysicalFixedSliceQuotient F ≃ SplitQuotientRoot where
  toFun y := ⟨F.quotientRootEquiv y.1, y.2⟩
  invFun r := ⟨F.quotientRootEquiv.symm r.1, by
    simpa using r.2⟩
  left_inv y := by
    apply Subtype.ext
    simp
  right_inv r := by
    apply Subtype.ext
    simp

/-- The rank-two Gram moduli and the physical split part of the fixed-slice
quotient are identified by their common concrete `u` coordinate. -/
noncomputable def phaseGramFixedSliceQuotientEquiv
    (F : Even11FixedSliceGeometryCertificate)
    (G : PhaseGramSpectrumCertificate) :
    PhaseGramOrbit11 ≃ Even11PhysicalFixedSliceQuotient F :=
  G.gramRootEquiv.trans F.splitRootEquiv.symm

/-- The Gram/fixed-slice equivalence preserves `u = σ²/11`. -/
theorem phaseGramFixedSliceQuotientEquiv_value
    (F : Even11FixedSliceGeometryCertificate)
    (G : PhaseGramSpectrumCertificate) (q : PhaseGramOrbit11) :
    even11FixedSliceQuotientU
        (phaseGramFixedSliceQuotientEquiv F G q).1 =
      (phaseGramOrbitInvariantU11 q : ℂ) := by
  change even11FixedSliceQuotientU
      (F.quotientRootEquiv.symm (G.gramRootEquiv q).1) = _
  calc
    even11FixedSliceQuotientU
        (F.quotientRootEquiv.symm (G.gramRootEquiv q).1) =
        ((G.gramRootEquiv q : SplitQuotientRoot) : ℂ) := by
          symm
          simpa using F.quotientRootEquiv_value
            (F.quotientRootEquiv.symm (G.gramRootEquiv q).1)
    _ = (phaseGramOrbitInvariantU11 q : ℂ) :=
      G.gramRootEquiv_value q

/-- The final physical-to-fixed-slice equivalence, after quotienting the
physical phases by dilation and conjugation. -/
noncomputable def phaseSolution11FixedSliceQuotientEquiv
    (F : Even11FixedSliceGeometryCertificate)
    (G : PhaseGramSpectrumCertificate) :
    PhaseSolution11Orbit ≃ Even11PhysicalFixedSliceQuotient F :=
  phaseSolution11OrbitGramEquiv.trans
    (phaseGramFixedSliceQuotientEquiv F G)

@[simp] theorem phaseSolution11FixedSliceQuotientEquiv_value
    (F : Even11FixedSliceGeometryCertificate)
    (G : PhaseGramSpectrumCertificate) (q : PhaseSolution11Orbit) :
    even11FixedSliceQuotientU
        (phaseSolution11FixedSliceQuotientEquiv F G q).1 =
      (phaseSolution11OrbitInvariantU q : ℂ) := by
  change even11FixedSliceQuotientU
      (phaseGramFixedSliceQuotientEquiv F G
        (phaseSolution11OrbitGramEquiv q)).1 = _
  rw [phaseGramFixedSliceQuotientEquiv_value]
  exact congrArg ((↑) : ℝ → ℂ)
    (phaseSolution11OrbitGramEquiv_value q)

/-- Assemble the specialized normalized even classification certificate from the concrete
fixed-slice geometry and the concrete Gram spectrum. -/
noncomputable def phaseSolution11FixedSliceCertificateOfGram
    (F : Even11FixedSliceGeometryCertificate)
    (G : PhaseGramSpectrumCertificate) :
    PhaseSolution11FixedSliceCertificate
      Even11FixedSlicePoint Even11FixedSliceFourierQuotient where
  fixedSlice := F.toFixedSliceGeometryCertificate
  orbitRoots := phaseSolution11OrbitGramEquiv.trans G.gramRootEquiv
  orbitRoots_value s := by
    change ((G.gramRootEquiv
      (phaseSolution11OrbitGramEquiv (Quotient.mk'' s)) :
        SplitQuotientRoot) : ℂ) = (phaseInvariantU11 s.1 : ℂ)
    rw [G.gramRootEquiv_value]
    exact congrArg ((↑) : ℝ → ℂ)
      (phaseSolution11OrbitGramEquiv_value (Quotient.mk'' s))

/-- The value-preserving orbit/root equivalence obtained through the Gram
moduli problem. -/
noncomputable def phaseSolution11OrbitRootEquivOfGram
    (G : PhaseGramSpectrumCertificate) :
    PhaseSolution11Orbit ≃ SplitQuotientRoot :=
  phaseSolution11OrbitGramEquiv.trans G.gramRootEquiv

@[simp] theorem phaseSolution11OrbitRootEquivOfGram_value
    (G : PhaseGramSpectrumCertificate) (q : PhaseSolution11Orbit) :
    ((phaseSolution11OrbitRootEquivOfGram G q : SplitQuotientRoot) : ℂ) =
      (phaseSolution11OrbitInvariantU q : ℂ) := by
  change ((G.gramRootEquiv (phaseSolution11OrbitGramEquiv q) :
    SplitQuotientRoot) : ℂ) = _
  rw [G.gramRootEquiv_value]
  exact congrArg ((↑) : ℝ → ℂ)
    (phaseSolution11OrbitGramEquiv_value q)

/-- The concrete Gram and fixed-slice spectrum certificates give the full
`80/10/70` result together with the independent
`32/16/8/7` fixed-slice count. -/
theorem classification11_phaseSolution_from_gram
    (F : Even11FixedSliceGeometryCertificate)
    (G : PhaseGramSpectrumCertificate) :
    (Nat.card Even11FixedSlicePoint = 32 ∧
      Nat.card {p : Even11FixedSlicePoint // even11FixedSliceIsReal p} = 16 ∧
      Fintype.card SplitQuotientRoot = 8 ∧
      Fintype.card NonGaussianSplitQuotientRoot = 7) ∧
    (Nat.card PhaseSolution11 = 80 ∧
      Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 = 0} = 10 ∧
      Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 ≠ 0} = 70) := by
  let C := phaseSolution11FixedSliceCertificateOfGram F G
  exact ⟨F.cardinality_core,
    classification11_phaseSolution_semantic_classification C⟩

end

end Biunimodular.F11
