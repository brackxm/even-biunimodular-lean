/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FixedSliceHomogeneousAffineChart
import Biunimodular.F11.HomogeneousPolynomialScaling
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
namespace Biunimodular.F11
noncomputable section
open MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev FixedSliceProjectiveChartRing :=
  HomogeneousLocalization.Away (homogeneousSubmodule (Fin 6) ℂ)
    (X 0 : MvPolynomial (Fin 6) ℂ)

private def chartCoefficient : ℂ →+* (homogeneousSubmodule (Fin 6) ℂ 0) where
  toFun c := ⟨C c, isHomogeneous_C _ c⟩
  map_zero' := Subtype.ext (map_zero C)
  map_one' := Subtype.ext (map_one C)
  map_add' c d := Subtype.ext (map_add C c d)
  map_mul' c d := Subtype.ext (map_mul C c d)

def fixedSliceProjectiveChartCoeff : ℂ →+* FixedSliceProjectiveChartRing :=
  (fromZeroRingHom (homogeneousSubmodule (Fin 6) ℂ) _).comp chartCoefficient

instance : Algebra ℂ FixedSliceProjectiveChartRing :=
  fixedSliceProjectiveChartCoeff.toAlgebra

/-- Affine coordinates are the homogeneous ratios `hᵢ/h₀`. -/
def fixedSliceAffineToProjectiveChart :
    FixedSliceFivePolynomial →ₐ[ℂ] FixedSliceProjectiveChartRing :=
  aeval (fun i : Fin 5 => Away.mk (homogeneousSubmodule (Fin 6) ℂ)
    (isHomogeneous_X ℂ (0 : Fin 6)) 1 (X i.rev.succ)
      (by simpa using isHomogeneous_X ℂ i.rev.succ))

/-- Dehomogenization extends to the actual homogeneous localization. -/
def fixedSliceProjectiveChartToAffine :
    FixedSliceProjectiveChartRing →+* FixedSliceFivePolynomial :=
  (Localization.awayLift fixedSliceHomogeneousAffineMap.toRingHom
    (X 0 : MvPolynomial (Fin 6) ℂ) (by simp [fixedSliceHomogeneousAffineMap])).comp
      (algebraMap FixedSliceProjectiveChartRing
        (Localization.Away (X 0 : MvPolynomial (Fin 6) ℂ)))

theorem fixedSliceProjectiveChartToAffine_mk (n : ℕ)
    (p : MvPolynomial (Fin 6) ℂ)
    (hp : p ∈ homogeneousSubmodule (Fin 6) ℂ (n • (1 : ℕ))) :
    fixedSliceProjectiveChartToAffine
      (Away.mk (homogeneousSubmodule (Fin 6) ℂ)
        (isHomogeneous_X ℂ (0 : Fin 6)) n p hp) = fixedSliceHomogeneousAffineMap p := by
  unfold fixedSliceProjectiveChartToAffine
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  have hunit : fixedSliceHomogeneousAffineMap.toRingHom
      (X 0 : MvPolynomial (Fin 6) ℂ) * 1 = 1 := by
    simp [fixedSliceHomogeneousAffineMap]
  simpa using Localization.awayLift_mk fixedSliceHomogeneousAffineMap.toRingHom
    (X 0 : MvPolynomial (Fin 6) ℂ) p 1 hunit n

theorem fixedSliceProjectiveChartToAffine_coeff (c : ℂ) :
    fixedSliceProjectiveChartToAffine (algebraMap ℂ FixedSliceProjectiveChartRing c) = C c := by
  change fixedSliceProjectiveChartToAffine
    (Away.mk (homogeneousSubmodule (Fin 6) ℂ)
      (isHomogeneous_X ℂ (0 : Fin 6)) 0 (C c) (isHomogeneous_C (Fin 6) c)) = C c
  rw [fixedSliceProjectiveChartToAffine_mk]
  simp [fixedSliceHomogeneousAffineMap]

def fixedSliceProjectiveChartToAffineAlg :
    FixedSliceProjectiveChartRing →ₐ[ℂ] FixedSliceFivePolynomial where
  __ := fixedSliceProjectiveChartToAffine
  commutes' c := fixedSliceProjectiveChartToAffine_coeff c

theorem fixedSliceProjectiveChartToAffine_left_inverse (p : FixedSliceFivePolynomial) :
    fixedSliceProjectiveChartToAffineAlg (fixedSliceAffineToProjectiveChart p) = p := by
  have h : fixedSliceProjectiveChartToAffineAlg.comp fixedSliceAffineToProjectiveChart =
      AlgHom.id ℂ FixedSliceFivePolynomial := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, fixedSliceAffineToProjectiveChart, aeval_X]
    change fixedSliceProjectiveChartToAffine (Away.mk _ _ 1 _ _) = X i
    rw [fixedSliceProjectiveChartToAffine_mk]
    simp [fixedSliceHomogeneousAffineMap]
  exact congrArg (fun f : FixedSliceFivePolynomial →ₐ[ℂ] FixedSliceFivePolynomial => f p) h

private abbrev ChartLocalization :=
  Localization.Away (X 0 : MvPolynomial (Fin 6) ℂ)

theorem fixedSliceProjectiveChart_coeff_val (c : ℂ) :
    (algebraMap ℂ FixedSliceProjectiveChartRing c).val =
      algebraMap (MvPolynomial (Fin 6) ℂ) ChartLocalization (C c) := by
  change Localization.mk (C c) 1 = _
  exact Localization.mk_one_eq_algebraMap _

theorem fixedSliceProjectiveChart_mk_val (n : ℕ)
    (p : MvPolynomial (Fin 6) ℂ)
    (hp : p ∈ homogeneousSubmodule (Fin 6) ℂ (n • (1 : ℕ))) :
    (Away.mk (homogeneousSubmodule (Fin 6) ℂ)
      (isHomogeneous_X ℂ (0 : Fin 6)) n p hp).val =
      algebraMap (MvPolynomial (Fin 6) ℂ) ChartLocalization p *
        (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin 6) ℂ) : ChartLocalization) ^ n := by
  rw [Away.val_mk, Localization.mk_eq_mk']
  symm
  apply (IsLocalization.eq_mk'_iff_mul_eq).mpr
  simp only [map_pow]
  rw [mul_assoc, ← mul_pow]
  have hi := IsLocalization.Away.mul_invSelf
    (S := ChartLocalization) (X 0 : MvPolynomial (Fin 6) ℂ)
  rw [mul_comm _ (algebraMap _ _ (X 0)), hi, one_pow, mul_one]

theorem fixedSliceAffineToProjectiveChart_dehomogeneous_val
    (p : MvPolynomial (Fin 6) ℂ) :
    (fixedSliceAffineToProjectiveChart (fixedSliceHomogeneousAffineMap p)).val =
      eval₂ ((algebraMap (MvPolynomial (Fin 6) ℂ) ChartLocalization).comp C)
        (fun i => (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin 6) ℂ) :
          ChartLocalization) * algebraMap (MvPolynomial (Fin 6) ℂ) ChartLocalization (X i)) p := by
  let V := algebraMap FixedSliceProjectiveChartRing ChartLocalization
  let F := (V.comp fixedSliceAffineToProjectiveChart.toRingHom).comp
    fixedSliceHomogeneousAffineMap.toRingHom
  let G := eval₂Hom ((algebraMap (MvPolynomial (Fin 6) ℂ) ChartLocalization).comp C)
    (fun i => (IsLocalization.Away.invSelf (X 0 : MvPolynomial (Fin 6) ℂ) :
      ChartLocalization) * algebraMap (MvPolynomial (Fin 6) ℂ) ChartLocalization (X i))
  have hFG : F = G := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change (fixedSliceAffineToProjectiveChart (fixedSliceHomogeneousAffineMap (C c))).val = _
      simp only [fixedSliceHomogeneousAffineMap, aeval_C, AlgHom.commutes]
      rw [fixedSliceProjectiveChart_coeff_val]
      simp [G]
    · intro i
      change (fixedSliceAffineToProjectiveChart (fixedSliceHomogeneousAffineMap (X i))).val = _
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [fixedSliceHomogeneousAffineMap, aeval_X, Fin.cases_zero,
          map_one, val_one, G, coe_eval₂Hom, eval₂_X]
        symm
        rw [mul_comm]
        exact IsLocalization.Away.mul_invSelf (S := ChartLocalization) _
      · simp only [fixedSliceHomogeneousAffineMap, aeval_X, Fin.cases_succ,
          fixedSliceAffineToProjectiveChart, aeval_X, Fin.rev_rev]
        rw [fixedSliceProjectiveChart_mk_val]
        simp only [pow_one, G, coe_eval₂Hom, eval₂_X]
        exact mul_comm _ _
  exact congrArg (fun f : MvPolynomial (Fin 6) ℂ →+* ChartLocalization => f p) hFG

theorem fixedSliceProjectiveChartToAffine_right_inverse (x : FixedSliceProjectiveChartRing) :
    fixedSliceAffineToProjectiveChart (fixedSliceProjectiveChartToAffineAlg x) = x := by
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective
    (homogeneousSubmodule (Fin 6) ℂ) (isHomogeneous_X ℂ (0 : Fin 6)) x
  apply HomogeneousLocalization.val_injective
  change (fixedSliceAffineToProjectiveChart
    (fixedSliceProjectiveChartToAffine (Away.mk _ _ n p hp))).val = _
  rw [fixedSliceProjectiveChartToAffine_mk,
    fixedSliceAffineToProjectiveChart_dehomogeneous_val, fixedSliceProjectiveChart_mk_val]
  have hp' : p.IsHomogeneous n := by simpa using hp
  rw [homogeneousPolynomial_eval₂_scale _ _ _ hp']
  have hm : eval₂Hom ((algebraMap (MvPolynomial (Fin 6) ℂ) ChartLocalization).comp C)
      (fun i => algebraMap (MvPolynomial (Fin 6) ℂ) ChartLocalization (X i)) =
      algebraMap (MvPolynomial (Fin 6) ℂ) ChartLocalization := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp
  change _ * eval₂Hom _ _ p = _
  rw [hm, mul_comm]

/-- The degree-zero localization of the actual projective coordinate chart
is the five-variable polynomial algebra, with the certified coordinate order. -/
def fixedSliceProjectiveChartEquivPolynomial :
    FixedSliceProjectiveChartRing ≃ₐ[ℂ] FixedSliceFivePolynomial :=
  AlgEquiv.ofAlgHom fixedSliceProjectiveChartToAffineAlg fixedSliceAffineToProjectiveChart
    (AlgHom.ext fun x => fixedSliceProjectiveChartToAffine_left_inverse x)
    (AlgHom.ext fun x => fixedSliceProjectiveChartToAffine_right_inverse x)

end
end Biunimodular.F11
