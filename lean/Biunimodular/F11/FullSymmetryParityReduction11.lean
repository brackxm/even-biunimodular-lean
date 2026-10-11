/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ProofTactics

set_option autoImplicit false

namespace Biunimodular.F11

abbrev WeylLabels11 := Multiplicative (ZMod 11 × ZMod 11)

/-- The projective Weyl group has odd order and no element of order two. -/
theorem weylLabels11_card : Fintype.card WeylLabels11 = 121 := by
  native_decide

theorem weylLabels11_no_two_torsion (p : WeylLabels11) :
    p ^ 2 = 1 → p = 1 := by
  native_decide +revert

/-!
The group-theoretic parity step in the full Fourier orbit argument.
Here `P` is the projective Weyl subgroup, `K` the linear/Fourier subgroup,
and `r` is reflection.  The statements are abstract so that the exact
semidirect-product calculation is independent of the signal model.
-/

section

variable {G X : Type*} [Group G] [MulAction G X]
    (P K : Subgroup G) (r : G)

/-- Conjugating reflection by a Weyl-linear element and multiplying by
reflection gives the square of its Weyl component. -/
theorem parity_conjugate_product
    (hcomm : ∀ k ∈ K, k * r = r * k)
    (hinv : ∀ p ∈ P, r * p * r = p⁻¹)
    {p k : G} (hp : p ∈ P) (hk : k ∈ K) :
    ((p * k) * r * (p * k)⁻¹) * r = p ^ 2 := by
  have hkr : k * r * k⁻¹ = r := by
    calc
      k * r * k⁻¹ = (r * k) * k⁻¹ := by rw [hcomm k hk]
      _ = r := by group
  have hpr : r * p⁻¹ * r = p := by
    simpa using hinv p⁻¹ (P.inv_mem hp)
  calc
    ((p * k) * r * (p * k)⁻¹) * r =
        p * (k * r * k⁻¹) * p⁻¹ * r := by group
    _ = p * r * p⁻¹ * r := by rw [hkr]
    _ = p * (r * p⁻¹ * r) := by group
    _ = p * p := by rw [hpr]
    _ = p ^ 2 := by simp [pow_two]

/-- If reflection fixes an even point and its Weyl stabilizer is trivial,
every full stabilizer element lies in the linear/Fourier subgroup. -/
theorem parity_stabilizer_le_linear
    (hdecomp : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    (hcomm : ∀ k ∈ K, k * r = r * k)
    (hinv : ∀ p ∈ P, r * p * r = p⁻¹)
    (hnoTwo : ∀ p ∈ P, p ^ 2 = 1 → p = 1)
    (x : X) (hrx : r • x = x)
    (hPfree : ∀ p ∈ P, p • x = x → p = 1)
    {g : G} (hg : g • x = x) : g ∈ K := by
  obtain ⟨p, hp, k, hk, rfl⟩ := hdecomp g
  have hginv : (p * k)⁻¹ • x = x := by
    calc
      (p * k)⁻¹ • x = (p * k)⁻¹ • ((p * k) • x) := by rw [hg]
      _ = x := by simp [smul_smul]
  have hconj : (((p * k) * r * (p * k)⁻¹) * r) • x = x := by
    calc
      (((p * k) * r * (p * k)⁻¹) * r) • x =
          (p * k) • (r • ((p * k)⁻¹ • (r • x))) := by
            simp only [mul_smul]
      _ = x := by rw [hrx, hginv, hrx, hg]
  have hp2 : (p ^ 2) • x = x := by
    rwa [parity_conjugate_product P K r hcomm hinv hp hk] at hconj
  have hp1 : p = 1 := hnoTwo p hp (hPfree (p ^ 2) (P.pow_mem hp 2) hp2)
  simpa [hp1] using hk

/-- A full symmetry between two reflection-fixed points already belongs to
the linear/Fourier orbit when the target has trivial Weyl stabilizer. -/
theorem parity_even_orbit_reduction
    (hdecomp : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    (hcomm : ∀ k ∈ K, k * r = r * k)
    (hinv : ∀ p ∈ P, r * p * r = p⁻¹)
    (hnoTwo : ∀ p ∈ P, p ^ 2 = 1 → p = 1)
    (x y : X) (hrx : r • x = x) (hry : r • y = y)
    (hPfree_y : ∀ p ∈ P, p • y = y → p = 1)
    {g : G} (hgy : g • x = y) :
    ∃ k ∈ K, k • x = y := by
  obtain ⟨p, hp, k, hk, rfl⟩ := hdecomp g
  have hginv : (p * k)⁻¹ • y = x := by
    calc
      (p * k)⁻¹ • y = (p * k)⁻¹ • ((p * k) • x) := by rw [hgy]
      _ = x := by simp [smul_smul]
  have hconj : (((p * k) * r * (p * k)⁻¹) * r) • y = y := by
    calc
      (((p * k) * r * (p * k)⁻¹) * r) • y =
          (p * k) • (r • ((p * k)⁻¹ • (r • y))) := by
            simp only [mul_smul]
      _ = y := by rw [hry, hginv, hrx, hgy]
  have hp2 : (p ^ 2) • y = y := by
    rwa [parity_conjugate_product P K r hcomm hinv hp hk] at hconj
  have hp1 : p = 1 := hnoTwo p hp (hPfree_y (p ^ 2) (P.pow_mem hp 2) hp2)
  refine ⟨k, hk, ?_⟩
  simpa [hp1] using hgy

/-- Once the parity reduction is known, the full and linear stabilizers have
the same elements. -/
noncomputable def parity_stabilizer_equiv_linear
    (x : X)
    (hsubset : ∀ g : G, g • x = x → g ∈ K) :
    MulAction.stabilizer K x ≃ MulAction.stabilizer G x where
  toFun h := ⟨h.1.1, h.2⟩
  invFun h := ⟨⟨h.1, hsubset h.1 h.2⟩, h.2⟩
  left_inv h := by cases h; rfl
  right_inv h := by cases h; rfl

/-- The numerical orbit-stabilizer step used for each non-Gaussian even
length-eleven point: a forty-element linear group with a ten-point orbit
gives a four-element full stabilizer inside the 4840-element full group. -/
theorem parity_full_orbit_card_1210
    [Fintype G] [Fintype K]
    (hdecomp : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    (hcomm : ∀ k ∈ K, k * r = r * k)
    (hinv : ∀ p ∈ P, r * p * r = p⁻¹)
    (hnoTwo : ∀ p ∈ P, p ^ 2 = 1 → p = 1)
    (x : X) [Fintype (MulAction.orbit K x)]
    [Fintype (MulAction.orbit G x)]
    (hrx : r • x = x)
    (hPfree : ∀ p ∈ P, p • x = x → p = 1)
    (hGcard : Fintype.card G = 4840)
    (hKcard : Fintype.card K = 40)
    (hKorbit : Fintype.card (MulAction.orbit K x) = 10) :
    Fintype.card (MulAction.orbit G x) = 1210 := by
  classical
  let hsubset : ∀ g : G, g • x = x → g ∈ K :=
    fun g hg => parity_stabilizer_le_linear P K r hdecomp hcomm hinv
      hnoTwo x hrx hPfree hg
  have hstab : Fintype.card (MulAction.stabilizer G x) =
      Fintype.card (MulAction.stabilizer K x) := by
    exact (Fintype.card_congr (parity_stabilizer_equiv_linear K x hsubset)).symm
  have hK := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := K) x
  rw [hKorbit, hKcard] at hK
  have hKstab : Fintype.card (MulAction.stabilizer K x) = 4 := by omega
  have hG := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) x
  rw [hstab, hKstab, hGcard] at hG
  omega

end

end Biunimodular.F11
