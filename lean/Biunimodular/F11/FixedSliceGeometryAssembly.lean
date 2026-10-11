/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceRootIntervalCertificate

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Final finite assembly for the F11 fixed-slice theorem

The geometry of the Fourier-conjugate slice produces a free two-sheeted
Fourier quotient `X -> Y`. The quotient `u`-spectrum has four arithmetic
sectors of sizes 1,1,6,8. The exact real-root distribution is:

* Gaussian `u=0`: split;
* constant algebraic branch `u=176`: nonsplit;
* A-sector: 3 split, 3 nonsplit;
* B-sector: 4 split, 4 nonreal.

This file contains all finite cardinality/orbit bookkeeping. The only object
which must be supplied by the geometric/certificate layer is an equivalence
between the actual quotient points and the sixteen polynomial roots, together
with the statement that real points upstairs are exactly the two lifts of an
admissible root.
-/

/-- Minimal certificate interface produced by the actual projective geometry.
`X` is the complex fixed-slice point type, `Y` its free Fourier quotient, and
`IsReal` is the real-locus predicate on `X`.

The quotient equivalence targets the actual roots of the certified
degree-16 polynomial. Splitting is a predicate on those root values. -/
structure FixedSliceGeometryCertificate
    (X Y : Type*) where
  IsReal : X → Prop
  decReal : DecidablePred IsReal
  twoSheeted : X ≃ Y × Bool
  quotientRoots : Y ≃ FixedSliceQuotientRoot
  real_iff_split : ∀ x,
    IsReal x ↔ fixedSliceQuotientRootSplit
      (quotientRoots (twoSheeted x).1)

/-- The real locus is the two-sheeted preimage of the semantic split-root
subset.  This equivalence is derived from the quotient maps and the pointwise
splitting criterion, rather than supplied as independent certificate data. -/
noncomputable def FixedSliceGeometryCertificate.realLifts
    {X Y : Type*}
    (C : FixedSliceGeometryCertificate X Y) :
    {x : X // C.IsReal x} ≃ SplitQuotientRoot × Bool where
  toFun x :=
    (⟨C.quotientRoots (C.twoSheeted x.1).1,
      (C.real_iff_split x.1).mp x.2⟩,
      (C.twoSheeted x.1).2)
  invFun p :=
    ⟨C.twoSheeted.symm (C.quotientRoots.symm p.1.1, p.2), by
      rw [C.real_iff_split]
      simpa only [Equiv.apply_symm_apply, Prod.fst] using p.1.2⟩
  left_inv x := by
    apply Subtype.ext
    apply C.twoSheeted.injective
    apply Prod.ext
    · simp
    · simp
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      simp
    · simp

attribute [instance] FixedSliceGeometryCertificate.decReal

section Assembly

variable {X Y : Type*}

/-- The complex fixed slice has exactly 32 points. -/
theorem fixedSlice_complex_card_32
    (C : FixedSliceGeometryCertificate X Y) :
    Nat.card X = 32 := by
  calc
    Nat.card X = Nat.card (Y × Bool) := Nat.card_congr C.twoSheeted
    _ = Nat.card Y * Nat.card Bool := Nat.card_prod Y Bool
    _ = Nat.card FixedSliceQuotientRoot * Nat.card Bool := by
      rw [Nat.card_congr C.quotientRoots]
    _ = 32 := by
      rw [Nat.card_eq_fintype_card, fixedSliceQuotientRoot_card]
      norm_num

/-- The Fourier quotient has exactly 16 points. -/
theorem fixedSlice_quotient_card_16
  (C : FixedSliceGeometryCertificate X Y) :
    Nat.card Y = 16 := by
  calc
    Nat.card Y = Nat.card FixedSliceQuotientRoot :=
      Nat.card_congr C.quotientRoots
    _ = 16 := by
      simpa [Nat.card_eq_fintype_card] using fixedSliceQuotientRoot_card

/-- Exactly sixteen complex fixed-slice points are real. -/
theorem fixedSlice_real_card_16
    (C : FixedSliceGeometryCertificate X Y) :
    Nat.card {x : X // C.IsReal x} = 16 := by
  calc
    Nat.card {x : X // C.IsReal x}
        = Nat.card (SplitQuotientRoot × Bool) :=
          Nat.card_congr C.realLifts
    _ = Nat.card SplitQuotientRoot * Nat.card Bool :=
      Nat.card_prod SplitQuotientRoot Bool
    _ = 16 := by
      simp [Nat.card_eq_fintype_card, splitQuotientRoot_card]

/-- The real points form eight Fourier/conjugate pairs. -/
theorem fixedSlice_real_pair_count_8 :
    Fintype.card SplitQuotientRoot = 8 :=
  splitQuotientRoot_card

/-- Of those eight real pairs, precisely seven are non-Gaussian. -/
theorem fixedSlice_nonGaussian_pair_count_7 :
    Fintype.card NonGaussianSplitQuotientRoot = 7 :=
  nonGaussianSplitQuotientRoot_card

/-- The cardinality statement for the fixed-slice geometry. -/
theorem fixedSlice_cardinality_core
    (C : FixedSliceGeometryCertificate X Y) :
    Nat.card X = 32 ∧
    Nat.card {x : X // C.IsReal x} = 16 ∧
    Fintype.card SplitQuotientRoot = 8 ∧
    Fintype.card NonGaussianSplitQuotientRoot = 7 := by
  exact ⟨fixedSlice_complex_card_32 C,
    fixedSlice_real_card_16 C,
    fixedSlice_real_pair_count_8,
    fixedSlice_nonGaussian_pair_count_7⟩

end Assembly

end Biunimodular.F11
