/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryFiniteGroup11

set_option autoImplicit false

namespace Biunimodular.F11

def fullWeylSubgroup11 : Subgroup FullSymmetryLabel11 :=
  (SemidirectProduct.inl : WeylLabels11 →* FullSymmetryLabel11).range

def fullLinearSubgroup11 : Subgroup FullSymmetryLabel11 :=
  (SemidirectProduct.inr : LinearFourierLabel11 →* FullSymmetryLabel11).range

def fullReflection11 : FullSymmetryLabel11 :=
  SemidirectProduct.inr linearR11

theorem fullSymmetryLabel11_decomp (g : FullSymmetryLabel11) :
    ∃ p ∈ fullWeylSubgroup11, ∃ k ∈ fullLinearSubgroup11,
      g = p * k := by
  refine ⟨SemidirectProduct.inl g.left, ⟨g.left, rfl⟩,
    SemidirectProduct.inr g.right, ⟨g.right, rfl⟩, ?_⟩
  exact (SemidirectProduct.inl_left_mul_inr_right g).symm

theorem fullReflection11_comm_linear
    (k : FullSymmetryLabel11) (hk : k ∈ fullLinearSubgroup11) :
    k * fullReflection11 = fullReflection11 * k := by
  obtain ⟨j, rfl⟩ := hk
  simp only [fullReflection11, ← map_mul]
  rw [linearR11_central j]

theorem linearR11_sq : linearR11 ^ 2 = 1 := by native_decide

theorem fullReflection11_sq : fullReflection11 ^ 2 = 1 := by
  rw [fullReflection11, ← map_pow, linearR11_sq, map_one]

theorem linearR11_inverts_weyl (p : WeylLabels11) :
    linearFourierWeylAction11 linearR11 p = p⁻¹ := by
  native_decide +revert

theorem fullReflection11_inverts_weyl
    (p : FullSymmetryLabel11) (hp : p ∈ fullWeylSubgroup11) :
    fullReflection11 * p * fullReflection11 = p⁻¹ := by
  obtain ⟨q, rfl⟩ := hp
  have hrinv : fullReflection11⁻¹ = fullReflection11 := by
    exact inv_eq_of_mul_eq_one_left (by
      simpa [pow_two] using fullReflection11_sq)
  calc
    fullReflection11 * SemidirectProduct.inl q * fullReflection11 =
        fullReflection11 * SemidirectProduct.inl q * fullReflection11⁻¹ := by
          rw [hrinv]
    _ = SemidirectProduct.inl (linearFourierWeylAction11 linearR11 q) := by
      exact (SemidirectProduct.inl_aut linearR11 q).symm
    _ = (SemidirectProduct.inl q)⁻¹ := by
      rw [linearR11_inverts_weyl, map_inv]

theorem fullWeylSubgroup11_no_two_torsion
    (p : FullSymmetryLabel11) (hp : p ∈ fullWeylSubgroup11)
    (hp2 : p ^ 2 = 1) : p = 1 := by
  obtain ⟨q, rfl⟩ := hp
  have hq2 : q ^ 2 = 1 := by
    have hmap : (SemidirectProduct.inl (q ^ 2) : FullSymmetryLabel11) =
        SemidirectProduct.inl (1 : WeylLabels11) := by
      simpa only [map_pow, map_one] using hp2
    exact SemidirectProduct.inl_injective hmap
  rw [weylLabels11_no_two_torsion q hq2, map_one]

def fullLinearSubgroup11_equiv :
    fullLinearSubgroup11 ≃ LinearFourierLabel11 where
  toFun k := k.1.right
  invFun j := ⟨SemidirectProduct.inr j, ⟨j, rfl⟩⟩
  left_inv k := by
    apply Subtype.ext
    obtain ⟨j, hj⟩ := k.2
    change SemidirectProduct.inr k.1.right = k.1
    rw [← hj]
    rfl
  right_inv _ := rfl

instance : Fintype fullLinearSubgroup11 :=
  Fintype.ofEquiv LinearFourierLabel11 fullLinearSubgroup11_equiv.symm

theorem fullLinearSubgroup11_card :
    Fintype.card fullLinearSubgroup11 = 40 := by
  rw [Fintype.card_congr fullLinearSubgroup11_equiv,
    linearFourierLabel11_card]

/-- In any projective action of the explicit 4840-element group, an even
point with trivial Weyl stabilizer and a ten-point linear orbit has a
1210-point full orbit. -/
theorem fullSymmetryLabel11_orbit_card_1210
    {X : Type*} [MulAction FullSymmetryLabel11 X]
    (x : X) [Fintype (MulAction.orbit fullLinearSubgroup11 x)]
    [Fintype (MulAction.orbit FullSymmetryLabel11 x)]
    (hrx : fullReflection11 • x = x)
    (hPfree : ∀ p ∈ fullWeylSubgroup11, p • x = x → p = 1)
    (hKorbit : Fintype.card
      (MulAction.orbit fullLinearSubgroup11 x) = 10) :
    Fintype.card (MulAction.orbit FullSymmetryLabel11 x) = 1210 := by
  exact parity_full_orbit_card_1210
    fullWeylSubgroup11 fullLinearSubgroup11 fullReflection11
    fullSymmetryLabel11_decomp fullReflection11_comm_linear
    fullReflection11_inverts_weyl fullWeylSubgroup11_no_two_torsion
    x hrx hPfree fullSymmetryLabel11_card
    fullLinearSubgroup11_card hKorbit

/-- For the explicit finite group, a full symmetry between two
reflection-fixed points with trivial target Weyl stabilizer already lies
in the 40-element linear/Fourier subgroup. -/
theorem fullSymmetryLabel11_even_orbit_reduction
    {X : Type*} [MulAction FullSymmetryLabel11 X]
    (x y : X)
    (hrx : fullReflection11 • x = x)
    (hry : fullReflection11 • y = y)
    (hPfree_y : ∀ p ∈ fullWeylSubgroup11, p • y = y → p = 1)
    {g : FullSymmetryLabel11} (hgy : g • x = y) :
    ∃ k ∈ fullLinearSubgroup11, k • x = y := by
  exact parity_even_orbit_reduction
    fullWeylSubgroup11 fullLinearSubgroup11 fullReflection11
    fullSymmetryLabel11_decomp fullReflection11_comm_linear
    fullReflection11_inverts_weyl fullWeylSubgroup11_no_two_torsion
    x y hrx hry hPfree_y hgy

end Biunimodular.F11
