/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.TorusFiberCoordinateCriterion
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

/-- A nonzero coordinate annihilator makes its image finite dimensional,
without assuming that the ambient algebra is finite or reduced. -/
theorem coordinate_range_finite
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : K[X] →ₐ[K] A) (H : K[X]) (hH : H ≠ 0) (hz : f H = 0) :
    Module.Finite K f.range := by
  apply coordinate_finite_of_surjective_annihilator f.rangeRestrict H hH
    _ f.rangeRestrict_surjective
  apply Subtype.ext
  exact hz

/-- The inverse of an ambient unit already in the coordinate image is again
in that image. Injectivity of multiplication on the finite image supplies
the inverse, without assuming the ambient algebra reduced. -/
theorem coordinate_inverse_mem_range
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : K[X] →ₐ[K] A) (H : K[X]) (hH : H ≠ 0) (hz : f H = 0)
    (y z : A) (hy : y ∈ f.range) (hyz : y * z = 1) : z ∈ f.range := by
  let _ : Module.Finite K f.range := coordinate_range_finite f H hH hz
  let y' : f.range := ⟨y, hy⟩
  have hinj : Function.Injective (LinearMap.mulLeft K y') := by
    intro u v huv
    apply Subtype.ext
    have he : y * (u : A) = y * (v : A) := congrArg Subtype.val huv
    calc
      (u : A) = z * (y * u) := by
        rw [← mul_assoc, mul_comm z y, hyz, one_mul]
      _ = z * (y * v) := congrArg (z * ·) he
      _ = (v : A) := by rw [← mul_assoc, mul_comm z y, hyz, one_mul]
  obtain ⟨u, hu⟩ := LinearMap.surjective_of_injective hinj 1
  have hue : y * (u : A) = 1 := congrArg Subtype.val hu
  have hzu : z = (u : A) := by
    calc
      z = z * (y * u) := by rw [hue, mul_one]
      _ = (u : A) := by rw [← mul_assoc, mul_comm z y, hyz, one_mul]
  rw [hzu]
  exact u.property

end
end Biunimodular.F11
