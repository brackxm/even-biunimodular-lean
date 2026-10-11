/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ProofTactics
import Biunimodular.F11.EvenSymmetry11Group
import Biunimodular.F11.FixedSliceGeometryAssembly

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Normalized even classification from fixed-slice and Gram geometry

This file deliberately avoids the degree-150 `k` eliminant. The independent
fixed-slice calculation supplies eight real split quotient roots. The
geometric hypothesis is the symmetry-preserving Gram identification of
the physical quotient: every normalized even physical solution belongs to one
of those eight roots, and the free dilation/conjugation action contributes ten
normalized solutions over each root.

The bridge is constructed from the fixed-slice realization and exact phase-box
certificates, independently of the classification it proves.
-/

/-- Minimal non-circular bridge needed to turn the independent `32/16`
fixed-slice theorem into the exhaustive physical classification.

`S` is the type of normalized even biunimodular solutions.  The ambient
`EvenSymmetry11` action is the concrete dilation/conjugation action.
The free-action typeclass records that every physical `H`-orbit has ten
elements, while `orbitRoots` encodes the Gram-moduli statement

`S / H ≃ SplitQuotientRoot`

The direct product equivalence, Gaussianity, and the Gaussian/non-Gaussian
fiber equivalences are all derived below rather than duplicated as certificate
fields.

Crucially, no `Fintype S` hypothesis is assumed: finiteness is a consequence
of the finite orbit quotient and the finite symmetry group, rather than an
input to normalized even classification. We therefore state cardinalities using `Nat.card` on the
physical side.
-/
structure FixedSliceClassificationCertificate
    (S X Y : Type*) [MulAction EvenSymmetry11 S]
    [IsCancelSMul EvenSymmetry11 S] where
  fixedSlice : FixedSliceGeometryCertificate X Y
  orbitRoots : MulAction.orbitRel.Quotient EvenSymmetry11 S ≃
    SplitQuotientRoot

/-- A free physical action with quotient identified with the admissible root
space has ten points above each root.  This is now a theorem, not certificate
data. -/
noncomputable def FixedSliceClassificationCertificate.physicalFibers
    {S X Y : Type*} [MulAction EvenSymmetry11 S]
    [IsCancelSMul EvenSymmetry11 S]
    (C : FixedSliceClassificationCertificate S X Y) :
    S ≃ SplitQuotientRoot × EvenSymmetry11 :=
  (MulAction.selfEquivOrbitsQuotientProd
      (fun s => IsCancelSMul.stabilizer_eq_bot s)).trans
    (Equiv.prodCongr C.orbitRoots (Equiv.refl EvenSymmetry11))

/-- The first coordinate of the derived fiber decomposition is the actual
orbit class, transported through `orbitRoots`. -/
theorem FixedSliceClassificationCertificate.physicalFibers_fst
    {S X Y : Type*} [MulAction EvenSymmetry11 S]
    [IsCancelSMul EvenSymmetry11 S]
    (C : FixedSliceClassificationCertificate S X Y) (s : S) :
    (C.physicalFibers s).1 = C.orbitRoots (Quotient.mk'' s) := by
  rfl

/-- A physical solution is Gaussian exactly when its quotient root is the
distinguished `u = 0` root. -/
def FixedSliceClassificationCertificate.IsGaussian
    {S X Y : Type*} [MulAction EvenSymmetry11 S]
    [IsCancelSMul EvenSymmetry11 S]
    (C : FixedSliceClassificationCertificate S X Y) (s : S) : Prop :=
  (C.physicalFibers s).1 = gaussianSplitQuotientRoot

noncomputable instance {S X Y : Type*} [MulAction EvenSymmetry11 S]
    [IsCancelSMul EvenSymmetry11 S]
    (C : FixedSliceClassificationCertificate S X Y) (s : S) :
    Decidable (C.IsGaussian s) :=
  Classical.propDecidable _

/-- The Gaussian fiber equivalence follows from the physical orbit-label
equivalence; it is not extra certificate data. -/
noncomputable def FixedSliceClassificationCertificate.gaussianFibers
    {S X Y : Type*} [MulAction EvenSymmetry11 S]
    [IsCancelSMul EvenSymmetry11 S]
    (C : FixedSliceClassificationCertificate S X Y) :
    {s : S // C.IsGaussian s} ≃ EvenSymmetry11 where
  toFun s := (C.physicalFibers s.1).2
  invFun i := ⟨C.physicalFibers.symm (gaussianSplitQuotientRoot, i), by
    simp [FixedSliceClassificationCertificate.IsGaussian]⟩
  left_inv s := by
    apply Subtype.ext
    apply C.physicalFibers.injective
    rw [C.physicalFibers.apply_symm_apply]
    apply Prod.ext
    · exact s.2.symm
    · simp
  right_inv i := by simp

/-- The seven non-Gaussian orbit labels, each with its ten physical points,
are likewise derived from `physicalFibers`. -/
noncomputable def FixedSliceClassificationCertificate.nonGaussianFibers
    {S X Y : Type*} [MulAction EvenSymmetry11 S]
    [IsCancelSMul EvenSymmetry11 S]
    (C : FixedSliceClassificationCertificate S X Y) :
    {s : S // ¬ C.IsGaussian s} ≃
      NonGaussianSplitQuotientRoot × EvenSymmetry11 where
  toFun s :=
    let p := C.physicalFibers s.1
    (⟨p.1, s.2⟩, p.2)
  invFun p :=
    ⟨C.physicalFibers.symm (p.1.1, p.2), by
      simpa [FixedSliceClassificationCertificate.IsGaussian] using p.1.2⟩
  left_inv s := by
    apply Subtype.ext
    apply C.physicalFibers.injective
    simp
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      simp
    · simp

section Assembly

variable {S X Y : Type*} [MulAction EvenSymmetry11 S]
  [IsCancelSMul EvenSymmetry11 S]

/-- The fixed-slice/Gram bypass gives exactly eighty normalized even physical
solutions, without any use of the degree-150 eliminant. -/
theorem classification11_fixedSlice_card_80
    (C : FixedSliceClassificationCertificate S X Y) :
    Nat.card S = 80 := by
  calc
    Nat.card S = Nat.card (SplitQuotientRoot × EvenSymmetry11) :=
      Nat.card_congr C.physicalFibers
    _ = Nat.card SplitQuotientRoot * Nat.card EvenSymmetry11 := by
      rw [Nat.card_prod]
    _ = 80 := by
      simp [Nat.card_eq_fintype_card, splitQuotientRoot_card]

/-- Exactly ten of the eighty normalized even physical solutions are
quadratic Gaussian. -/
theorem classification11_fixedSlice_gaussian_card_10
    (C : FixedSliceClassificationCertificate S X Y) :
    Nat.card {s : S // C.IsGaussian s} = 10 := by
  calc
    Nat.card {s : S // C.IsGaussian s} = Nat.card EvenSymmetry11 :=
      Nat.card_congr C.gaussianFibers
    _ = 10 := by
      simp [Nat.card_eq_fintype_card]

/-- Exactly seventy of the eighty normalized even physical solutions are
non-Gaussian. -/
theorem classification11_fixedSlice_nonGaussian_card_70
    (C : FixedSliceClassificationCertificate S X Y) :
    Nat.card {s : S // ¬ C.IsGaussian s} = 70 := by
  calc
    Nat.card {s : S // ¬ C.IsGaussian s}
        = Nat.card (NonGaussianSplitQuotientRoot × EvenSymmetry11) :=
          Nat.card_congr C.nonGaussianFibers
    _ = Nat.card NonGaussianSplitQuotientRoot * Nat.card EvenSymmetry11 := by
      rw [Nat.card_prod]
    _ = 70 := by
      simp [Nat.card_eq_fintype_card, splitQuotientRoot_card]

/-- numerical core of normalized even classification through the independent
fixed-slice `32/16` route. -/
theorem classification11_fixedSlice_bypass_core
    (C : FixedSliceClassificationCertificate S X Y) :
    Nat.card S = 80 ∧
    Nat.card {s : S // C.IsGaussian s} = 10 ∧
    Nat.card {s : S // ¬ C.IsGaussian s} = 70 := by
  exact ⟨classification11_fixedSlice_card_80 C,
    classification11_fixedSlice_gaussian_card_10 C,
    classification11_fixedSlice_nonGaussian_card_70 C⟩

/-- The same certificate simultaneously contains the independent fixed-slice
`32 complex / 16 real / 8 pairs / 7 non-Gaussian pairs` theorem. -/
theorem classification11_fixedSlice_bypass_with_geometry
    (C : FixedSliceClassificationCertificate S X Y) :
    (Nat.card X = 32 ∧
      Nat.card {x : X // C.fixedSlice.IsReal x} = 16 ∧
      Fintype.card SplitQuotientRoot = 8 ∧
      Fintype.card NonGaussianSplitQuotientRoot = 7) ∧
    (Nat.card S = 80 ∧
      Nat.card {s : S // C.IsGaussian s} = 10 ∧
      Nat.card {s : S // ¬ C.IsGaussian s} = 70) := by
  exact ⟨fixedSlice_cardinality_core C.fixedSlice,
    classification11_fixedSlice_bypass_core C⟩

end Assembly

end Biunimodular.F11
