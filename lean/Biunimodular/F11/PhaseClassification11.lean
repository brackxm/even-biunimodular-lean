/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ProofTactics
import Biunimodular.F11.PhaseInvariant11
import Biunimodular.F11.PhaseSignalSemantic11
import Biunimodular.F11.FixedSliceClassification11

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Normalized even phase classification at prime 11

The concrete problem is represented by the ten real phase coordinates in
`PhaseCoords11`. Its cardinality follows from the value-preserving equivalence
between the symmetry quotient and the admissible fixed-slice invariant roots.
-/

/-- A fixed-slice/Gram bypass certificate specialized to the actual `p = 11`
phase-solution type.  Besides identifying the symmetry quotient with the eight
admissible roots, the equivalence must preserve the concrete physical
invariant `u`; this rules out an arbitrary permutation of the root labels. -/
structure PhaseSolution11FixedSliceCertificate (X Y : Type*) where
  fixedSlice : FixedSliceGeometryCertificate X Y
  orbitRoots : PhaseSolution11Orbit ≃ SplitQuotientRoot
  orbitRoots_value : ∀ s : PhaseSolution11,
    ((orbitRoots (Quotient.mk'' s) : SplitQuotientRoot) : ℂ) =
      (phaseInvariantU11 s.1 : ℂ)

/-- Forgetting value preservation gives the generic finite-orbit bypass
certificate. -/
def PhaseSolution11FixedSliceCertificate.toFixedSliceClassificationCertificate
    {X Y : Type*}
    (C : PhaseSolution11FixedSliceCertificate X Y) :
    FixedSliceClassificationCertificate PhaseSolution11 X Y where
  fixedSlice := C.fixedSlice
  orbitRoots := C.orbitRoots

/-- Gaussianity on the specialized certificate, inherited from the
distinguished zero root of the quotient spectrum. -/
noncomputable def PhaseSolution11FixedSliceCertificate.IsGaussian
    {X Y : Type*}
    (C : PhaseSolution11FixedSliceCertificate X Y)
    (s : PhaseSolution11) : Prop :=
  C.toFixedSliceClassificationCertificate.IsGaussian s

noncomputable instance {X Y : Type*}
    (C : PhaseSolution11FixedSliceCertificate X Y) (s : PhaseSolution11) :
    Decidable (C.IsGaussian s) :=
  Classical.propDecidable _

/-- The quotient root attached to a phase solution has exactly its concrete
physical invariant value. -/
theorem PhaseSolution11FixedSliceCertificate.physicalRoot_value
    {X Y : Type*}
    (C : PhaseSolution11FixedSliceCertificate X Y)
    (s : PhaseSolution11) :
    (((C.toFixedSliceClassificationCertificate.physicalFibers s).1 :
        SplitQuotientRoot) : ℂ) = (phaseInvariantU11 s.1 : ℂ) := by
  rw [C.toFixedSliceClassificationCertificate.physicalFibers_fst]
  exact C.orbitRoots_value s

/-- The abstract Gaussian fiber is now identified with the semantic condition
`u = 0` on the original phase coordinates. -/
theorem PhaseSolution11FixedSliceCertificate.isGaussian_iff_invariantU_eq_zero
    {X Y : Type*}
    (C : PhaseSolution11FixedSliceCertificate X Y)
    (s : PhaseSolution11) :
    C.IsGaussian s ↔ phaseInvariantU11 s.1 = 0 := by
  rw [PhaseSolution11FixedSliceCertificate.IsGaussian,
    FixedSliceClassificationCertificate.IsGaussian,
    splitQuotientRoot_eq_gaussian_iff, C.physicalRoot_value]
  norm_cast

/-- Value preservation holds intrinsically on every quotient point, not only
on a chosen representative. -/
theorem PhaseSolution11FixedSliceCertificate.orbitRoots_value_quotient
    {X Y : Type*}
    (C : PhaseSolution11FixedSliceCertificate X Y)
    (q : PhaseSolution11Orbit) :
    ((C.orbitRoots q : SplitQuotientRoot) : ℂ) =
      (phaseSolution11OrbitInvariantU q : ℂ) := by
  refine Quotient.inductionOn' q ?_
  intro s
  exact C.orbitRoots_value s

/-- The physical value `u` is a complete invariant of normalized even
symmetry orbits. -/
theorem PhaseSolution11FixedSliceCertificate.orbitInvariantU_injective
    {X Y : Type*}
    (C : PhaseSolution11FixedSliceCertificate X Y) :
    Function.Injective phaseSolution11OrbitInvariantU := by
  intro q r hqr
  apply C.orbitRoots.injective
  apply Subtype.ext
  apply Subtype.ext
  exact C.orbitRoots_value_quotient q |>.trans <|
    (congrArg ((↑) : ℝ → ℂ) hqr).trans <|
      C.orbitRoots_value_quotient r |>.symm

/-- Once the value-preserving orbit/root bridge is supplied, every physical
invariant lies in the strict admissible interval. -/
theorem PhaseSolution11FixedSliceCertificate.invariantU_mem_Ico
    {X Y : Type*}
    (C : PhaseSolution11FixedSliceCertificate X Y)
    (s : PhaseSolution11) :
    0 ≤ phaseInvariantU11 s.1 ∧ phaseInvariantU11 s.1 < 1 := by
  let r : SplitQuotientRoot := C.orbitRoots (Quotient.mk'' s)
  have hr := (fixedSliceQuotientRootSplit_iff r.1).mp r.2
  have hvalue : (r : ℂ).re = phaseInvariantU11 s.1 := by
    simpa [r] using congrArg Complex.re (C.orbitRoots_value s)
  constructor
  · rw [← hvalue]
    exact hr.2.1
  · rw [← hvalue]
    exact hr.2.2

section

variable {X Y : Type*}

/-- normalized even classification, cardinality form, on the repository's concrete phase system. -/
theorem classification11_phaseSolution_card_80
    (C : PhaseSolution11FixedSliceCertificate X Y) :
    Nat.card PhaseSolution11 = 80 :=
  classification11_fixedSlice_card_80
    C.toFixedSliceClassificationCertificate

/-- The concrete dilation/conjugation quotient has exactly eight orbits. -/
theorem classification11_phaseSolution_orbit_card_8
    (C : PhaseSolution11FixedSliceCertificate X Y) :
    Nat.card PhaseSolution11Orbit = 8 := by
  calc
    Nat.card PhaseSolution11Orbit = Nat.card SplitQuotientRoot :=
      Nat.card_congr C.orbitRoots
    _ = 8 := by
      simp [Nat.card_eq_fintype_card, splitQuotientRoot_card]

/-- The ten Gaussian solutions in normalized even classification. -/
theorem classification11_phaseSolution_gaussian_card_10
    (C : PhaseSolution11FixedSliceCertificate X Y) :
    Nat.card {s : PhaseSolution11 // C.IsGaussian s} = 10 :=
  classification11_fixedSlice_gaussian_card_10
    C.toFixedSliceClassificationCertificate

/-- The seventy non-Gaussian solutions in normalized even classification. -/
theorem classification11_phaseSolution_nonGaussian_card_70
    (C : PhaseSolution11FixedSliceCertificate X Y) :
    Nat.card {s : PhaseSolution11 // ¬ C.IsGaussian s} = 70 :=
  classification11_fixedSlice_nonGaussian_card_70
    C.toFixedSliceClassificationCertificate

/-- The Gaussian count stated directly in terms of the physical phase
invariant, rather than the distinguished quotient-root label. -/
theorem classification11_phaseSolution_invariantU_zero_card_10
    (C : PhaseSolution11FixedSliceCertificate X Y) :
    Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 = 0} = 10 := by
  calc
    Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 = 0} =
        Nat.card {s : PhaseSolution11 // C.IsGaussian s} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun s =>
        (C.isGaussian_iff_invariantU_eq_zero s).symm)
    _ = 10 := classification11_phaseSolution_gaussian_card_10 C

/-- The non-Gaussian count stated directly as `u ≠ 0`. -/
theorem classification11_phaseSolution_invariantU_ne_zero_card_70
    (C : PhaseSolution11FixedSliceCertificate X Y) :
    Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 ≠ 0} = 70 := by
  calc
    Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 ≠ 0} =
        Nat.card {s : PhaseSolution11 // ¬ C.IsGaussian s} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun s =>
        (not_congr (C.isGaussian_iff_invariantU_eq_zero s)).symm)
    _ = 70 := classification11_phaseSolution_nonGaussian_card_70 C

/-- numerical statement of normalized even classification. -/
theorem classification11_phaseSolution_classification
    (C : PhaseSolution11FixedSliceCertificate X Y) :
    Nat.card PhaseSolution11 = 80 ∧
    Nat.card {s : PhaseSolution11 // C.IsGaussian s} = 10 ∧
    Nat.card {s : PhaseSolution11 // ¬ C.IsGaussian s} = 70 :=
  classification11_fixedSlice_bypass_core
    C.toFixedSliceClassificationCertificate

/-- numerical classification using only the original
phase system and its concrete invariant `u`. -/
theorem classification11_phaseSolution_semantic_classification
    (C : PhaseSolution11FixedSliceCertificate X Y) :
    Nat.card PhaseSolution11 = 80 ∧
    Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 = 0} = 10 ∧
    Nat.card {s : PhaseSolution11 // phaseInvariantU11 s.1 ≠ 0} = 70 := by
  exact ⟨classification11_phaseSolution_card_80 C,
    classification11_phaseSolution_invariantU_zero_card_10 C,
    classification11_phaseSolution_invariantU_ne_zero_card_70 C⟩

/-- The same bypass certificate proves normalized even classification together with the
independent `32/16` fixed-slice count from which its eight orbit labels come. -/
theorem classification11_phaseSolution_with_fixedSlice_32_16
    (C : PhaseSolution11FixedSliceCertificate X Y) :
    (Nat.card X = 32 ∧
      Nat.card {x : X // C.fixedSlice.IsReal x} = 16 ∧
      Fintype.card SplitQuotientRoot = 8 ∧
      Fintype.card NonGaussianSplitQuotientRoot = 7) ∧
    (Nat.card PhaseSolution11 = 80 ∧
      Nat.card {s : PhaseSolution11 // C.IsGaussian s} = 10 ∧
      Nat.card {s : PhaseSolution11 // ¬ C.IsGaussian s} = 70) :=
  classification11_fixedSlice_bypass_with_geometry
    C.toFixedSliceClassificationCertificate

end

end Biunimodular.F11
