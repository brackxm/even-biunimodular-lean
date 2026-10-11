/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.ToLin
import Biunimodular.F11.FixedSliceBoundaryReduction

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Finite principal-minor reduction of the p = 11 uncertainty input

For the six-coordinate even Fourier model, the only uncertainty consequence
needed by the fixed-slice proof is coordinatewise non-disjointness of a vector
and its Fourier image. If `S` is the support of a nonzero six-vector and the
supports were disjoint, then the vector is supported on `S` while its Fourier
image vanishes on `S`. Thus it is enough to know that every nonempty
principal support restriction has trivial kernel.

For six coordinates this is a finite 63-case statement. The companion exact
certificate computes the 63 principal minors in Q(2 cos(2π/11)).
-/

section Field

variable {K : Type*} [Field K]

/-- Matrix of a linear operator on the six even coordinates, in the standard
coordinate basis. -/
noncomputable def even6LinearMatrix (F : Even6 K →ₗ[K] Even6 K) :
    Matrix (Fin 6) (Fin 6) K :=
  fun i j => F (Pi.single j 1) i

@[simp] theorem even6LinearMatrix_mulVec
    (F : Even6 K →ₗ[K] Even6 K) (h : Even6 K) :
    Matrix.mulVec (even6LinearMatrix F) h = F h := by
  classical
  funext i
  calc
    Matrix.mulVec (even6LinearMatrix F) h i =
        ∑ j, h j * F (Pi.single j 1) i := by
      simp [even6LinearMatrix, Matrix.mulVec, dotProduct, mul_comm]
    _ = F (∑ j, h j • Pi.single j 1) i := by
      rw [map_sum]
      simp
    _ = F h i := by rw [← pi_eq_sum_univ' h]

/-- Every nonempty principal submatrix of the coordinate matrix is
nonsingular.  This is the exact determinant-shaped interface implemented by
the 63-row order-11 certificate. -/
def PrincipalMinorsNonzero (F : Even6 K →ₗ[K] Even6 K) : Prop :=
  ∀ S : Finset (Fin 6), S.Nonempty →
    Matrix.det ((even6LinearMatrix F).submatrix
      (fun i : S => (i : Fin 6)) (fun j : S => (j : Fin 6))) ≠ 0

/-- Kernel-free formulation of all nonempty principal support restrictions. -/
def PrincipalSupportKernelFree (F : Even6 K →ₗ[K] Even6 K) : Prop :=
  ∀ S : Finset (Fin 6), S.Nonempty →
    ∀ h : Even6 K,
      (∀ j, j ∉ S → h j = 0) →
      (∀ j, j ∈ S → F h j = 0) →
      h = 0

/-- Nonvanishing of every nonempty principal minor implies the corresponding
principal support restriction has trivial kernel. -/
theorem principalSupportKernelFree_of_principalMinorsNonzero
    {F : Even6 K →ₗ[K] Even6 K}
    (hminor : PrincipalMinorsNonzero F) :
    PrincipalSupportKernelFree F := by
  classical
  intro S hS h hsupp hFzero
  let M : Matrix S S K := (even6LinearMatrix F).submatrix
    (fun i : S => (i : Fin 6)) (fun j : S => (j : Fin 6))
  let v : S → K := fun j => h j
  have hMv : Matrix.mulVec M v = 0 := by
    funext i
    have hFi : F h i = 0 := hFzero i i.property
    rw [← even6LinearMatrix_mulVec F h] at hFi
    change (∑ j : S, even6LinearMatrix F i j * h j) = 0
    calc
      _ = ∑ j ∈ S, even6LinearMatrix F i j * h j :=
        Finset.sum_attach S (fun j => even6LinearMatrix F i j * h j)
      _ = ∑ j, even6LinearMatrix F i j * h j := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro j _ hj
        simp [hsupp j hj]
      _ = 0 := by simpa [Matrix.mulVec, dotProduct] using hFi
  have hv : v = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero (hminor S hS) hMv
  funext j
  by_cases hj : j ∈ S
  · exact congrFun hv ⟨j, hj⟩
  · exact hsupp j hj

/-- The finite principal-support condition is exactly enough for the
fixed-slice support-uncertainty consequence. -/
theorem noDisjointFourierSupport_of_principalSupportKernelFree
    {F : Even6 K →ₗ[K] Even6 K}
    (hprincipal : PrincipalSupportKernelFree F) :
    NoDisjointFourierSupport F := by
  classical
  intro h hnz hdis
  let S : Finset (Fin 6) := Finset.univ.filter (fun j => h j ≠ 0)
  have hSnonempty : S.Nonempty := by
    by_contra hsempty
    rw [Finset.not_nonempty_iff_eq_empty] at hsempty
    apply hnz
    funext j
    have hjnot : j ∉ S := by simp [hsempty]
    simpa [S] using hjnot
  have hsupp : ∀ j, j ∉ S → h j = 0 := by
    intro j hj
    simpa [S] using hj
  have hFzero : ∀ j, j ∈ S → F h j = 0 := by
    intro j hj
    have hne : h j ≠ 0 := by simpa [S] using hj
    rcases hdis j with hj0 | hFj
    · exact False.elim (hne hj0)
    · exact hFj
  exact hnz (hprincipal S hSnonempty h hsupp hFzero)

/-- The determinant-shaped 63-case certificate implies the exact support
uncertainty statement used by the fixed-slice development. -/
theorem noDisjointFourierSupport_of_principalMinorsNonzero
    {F : Even6 K →ₗ[K] Even6 K}
    (hminor : PrincipalMinorsNonzero F) :
    NoDisjointFourierSupport F :=
  noDisjointFourierSupport_of_principalSupportKernelFree
    (principalSupportKernelFree_of_principalMinorsNonzero hminor)

/-- The fixed-slice boundary is therefore removed once the 63 principal
support cases have been certified. -/
theorem fixedSlice_common_ne_zero_of_principalSupportKernelFree
    {F : Even6 K →ₗ[K] Even6 K}
    (hprincipal : PrincipalSupportKernelFree F)
    {h : Even6 K}
    (hnz : h ≠ 0)
    (hh : FixedSliceEq F h) :
    fourierCoordProduct F h 0 ≠ 0 :=
  fixedSlice_common_ne_zero_of_uncertainty
    (noDisjointFourierSupport_of_principalSupportKernelFree hprincipal)
    hnz hh

/-- Direct no-boundary endpoint for a verified family of nonzero principal
minors. -/
theorem fixedSlice_common_ne_zero_of_principalMinorsNonzero
    {F : Even6 K →ₗ[K] Even6 K}
    (hminor : PrincipalMinorsNonzero F)
    {h : Even6 K}
    (hnz : h ≠ 0)
    (hh : FixedSliceEq F h) :
    fourierCoordProduct F h 0 ≠ 0 :=
  fixedSlice_common_ne_zero_of_principalSupportKernelFree
    (principalSupportKernelFree_of_principalMinorsNonzero hminor) hnz hh

end Field

end Biunimodular.F11
