/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.UnivariateCoordinateSurjectivity
import Biunimodular.F11.CoordinateSurjectivityFromDimension
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

/-- A partition by polynomial projections reconstructs a coordinate from
its projected values. This works in the whole algebra, including nilpotents. -/
theorem coordinate_mem_range_of_projected_relations
    {K A ι : Type*} [Field K] [CommRing A] [Algebra K A] [Fintype ι]
    (f : K[X] →ₐ[K] A) (e n : ι → K[X]) (scale : K) (hs : scale ≠ 0)
    (y : A) (hpartition : ∑ i, f (e i) = algebraMap K A scale)
    (hproject : ∀ i, f (e i) * y = f (n i)) : y ∈ f.range := by
  have hsum : f (∑ i, n i) = algebraMap K A scale * y := by
    rw [map_sum, ← hpartition, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => (hproject i).symm)
  refine ⟨C scale⁻¹ * ∑ i, n i, ?_⟩
  change f (C scale⁻¹ * ∑ i, n i) = y
  rw [map_mul, C_eq_algebraMap, AlgHom.commutes, hsum, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ hs, map_one, one_mul]

/-- A projected linear equation supplies its polynomial projected value.
The nonzero scalar is inverted in the coefficient field, not in the target. -/
theorem projected_linear_relation_value
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : K[X] →ₐ[K] A) (e n : K[X]) (d : K) (hd : d ≠ 0) (y : A)
    (h : f e * (algebraMap K A d * y + f n) = 0) :
    f e * y = f (C (-d⁻¹) * e * n) := by
  have hu : IsUnit (algebraMap K A d) :=
    (isUnit_iff_ne_zero.mpr hd).map (algebraMap K A)
  have hi : algebraMap K A d * algebraMap K A d⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hd, map_one]
  apply hu.mul_left_cancel
  rw [map_mul, map_mul, C_eq_algebraMap, AlgHom.commutes, map_neg]
  linear_combination h + (f e * f n) * hi

/-- Surjective generation by a coordinate annihilated by a nonzero polynomial
supplies a finite-dimensional bound without assuming a reduced quotient. -/
theorem coordinate_finite_of_surjective_annihilator
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : K[X] →ₐ[K] A) (H : K[X]) (hH : H ≠ 0)
    (hz : f H = 0) (hf : Function.Surjective f) : Module.Finite K A := by
  have hI : Ideal.span ({H} : Set K[X]) ≤ RingHom.ker f := by
    rw [Ideal.span_le]
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    exact hz
  let g := Ideal.Quotient.liftₐ (Ideal.span ({H} : Set K[X])) f
    (fun p hp => hI hp)
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨p, rfl⟩ := hf a
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  let : Module.Finite K (K[X] ⧸ Ideal.span ({H} : Set K[X])) := by
    change Module.Finite K (AdjoinRoot H)
    exact Module.Finite.of_basis (AdjoinRoot.powerBasis hH).basis
  exact Module.Finite.of_surjective g.toLinearMap hg

theorem coordinate_finrank_le_of_surjective_annihilator
    {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (f : K[X] →ₐ[K] A) (H : K[X]) (hH : H ≠ 0)
    (hz : f H = 0) (hf : Function.Surjective f) : Module.finrank K A ≤ H.natDegree := by
  have hI : Ideal.span ({H} : Set K[X]) ≤ RingHom.ker f := by
    rw [Ideal.span_le]
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst p
    exact hz
  let g := Ideal.Quotient.liftₐ (Ideal.span ({H} : Set K[X])) f
    (fun p hp => hI hp)
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨p, rfl⟩ := hf a
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  let : Module.Finite K (K[X] ⧸ Ideal.span ({H} : Set K[X])) := by
    change Module.Finite K (AdjoinRoot H)
    exact Module.Finite.of_basis (AdjoinRoot.powerBasis hH).basis
  let := coordinate_finite_of_surjective_annihilator f H hH hz hf
  simpa only [finrank_quotient_span_eq_natDegree] using
    LinearMap.finrank_le_finrank_of_surjective (f := g.toLinearMap) hg

end
end Biunimodular.F11
