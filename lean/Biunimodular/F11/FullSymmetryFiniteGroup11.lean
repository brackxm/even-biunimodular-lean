/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryLinearGroup11
import Biunimodular.F11.FullSymmetryParityReduction11
import Mathlib.GroupTheory.SemidirectProduct

set_option autoImplicit false

namespace Biunimodular.F11

local instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- Action of the projective linear/Fourier labels on Weyl labels.
The normal form is `D^a C^c F^f`. -/
def linearFourierWeylLabelAction11
    (k : LinearFourierLabel11) (p : WeylLabels11) : WeylLabels11 :=
  let ab : ZMod 11 × ZMod 11 := Multiplicative.toAdd p
  let uv := if k.fourier then (-ab.2, ab.1) else ab
  let uv := if k.conjugate then (uv.1, -uv.2) else uv
  let d := (2 : ZMod 11) ^ k.dilate.val
  Multiplicative.ofAdd (d⁻¹ * uv.1, d * uv.2)

/-- Each linear/Fourier label induces an automorphism of the projective
Weyl group. -/
def linearFourierWeylLabelAut11
    (k : LinearFourierLabel11) : MulAut WeylLabels11 where
  toFun := linearFourierWeylLabelAction11 k
  invFun := linearFourierWeylLabelAction11 k⁻¹
  left_inv := by native_decide +revert
  right_inv := by native_decide +revert
  map_mul' := by native_decide +revert

/-- The Fourier/dilation/conjugation group acts on Weyl labels by automorphisms. -/
def linearFourierWeylAction11 :
    LinearFourierLabel11 →* MulAut WeylLabels11 where
  toFun := linearFourierWeylLabelAut11
  map_one' := by
    ext p <;> native_decide +revert
  map_mul' := by
    intro k l
    ext p <;> native_decide +revert

/-- The finite abstract projective full symmetry group at length eleven. -/
abbrev FullSymmetryLabel11 :=
  WeylLabels11 ⋊[linearFourierWeylAction11] LinearFourierLabel11

def fullSymmetryLabel11_equiv :
    FullSymmetryLabel11 ≃ WeylLabels11 × LinearFourierLabel11 where
  toFun g := (g.left, g.right)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype FullSymmetryLabel11 :=
  Fintype.ofEquiv (WeylLabels11 × LinearFourierLabel11)
    fullSymmetryLabel11_equiv.symm

theorem fullSymmetryLabel11_card :
    Fintype.card FullSymmetryLabel11 = 4840 := by
  rw [Fintype.card_congr fullSymmetryLabel11_equiv,
    Fintype.card_prod, weylLabels11_card,
    linearFourierLabel11_card]

end Biunimodular.F11
