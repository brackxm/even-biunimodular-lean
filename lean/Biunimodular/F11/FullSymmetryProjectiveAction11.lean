/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FullSymmetryProjectiveLinearWeyl11

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

/-- The concrete action of the 4840-element finite symmetry group on
all projective length-eleven signals. -/
def fullProjectiveSymmetryPerm11 :
    FullSymmetryLabel11 →* Equiv.Perm FullProjectiveSignal11 :=
  SemidirectProduct.lift
    (MulAction.toPermHom WeylLabels11 FullProjectiveSignal11)
    projectiveLinearFourierPerm11
    (by
      intro k
      ext p z
      have h : projectiveLinearFourierPerm11 k *
          (MulAction.toPermHom WeylLabels11 FullProjectiveSignal11) p =
          (MulAction.toPermHom WeylLabels11 FullProjectiveSignal11)
            (linearFourierWeylAction11 k p) *
            projectiveLinearFourierPerm11 k := by
        ext t
        exact projectiveLinearFourier_weyl_intertwine k p t
      have hi := congrArg
        (fun e : Equiv.Perm FullProjectiveSignal11 =>
          e * (projectiveLinearFourierPerm11 k)⁻¹) h
      have heq :
          (MulAction.toPermHom WeylLabels11 FullProjectiveSignal11)
            (linearFourierWeylAction11 k p) =
          projectiveLinearFourierPerm11 k *
            (MulAction.toPermHom WeylLabels11 FullProjectiveSignal11) p *
            (projectiveLinearFourierPerm11 k)⁻¹ := by
        simpa only [mul_assoc, mul_inv_cancel, mul_one] using hi.symm
      exact congrArg (fun e : Equiv.Perm FullProjectiveSignal11 => e z) heq)

instance : MulAction FullSymmetryLabel11 FullProjectiveSignal11 where
  smul g z := fullProjectiveSymmetryPerm11 g z
  one_smul z := by
    change fullProjectiveSymmetryPerm11 1 z = z
    rw [map_one]
    rfl
  mul_smul g h z := by
    change fullProjectiveSymmetryPerm11 (g * h) z =
      fullProjectiveSymmetryPerm11 g
        (fullProjectiveSymmetryPerm11 h z)
    rw [map_mul]
    rfl

theorem fullProjectiveSymmetryPerm11_weyl (p : WeylLabels11) :
    fullProjectiveSymmetryPerm11 (SemidirectProduct.inl p) =
      MulAction.toPermHom WeylLabels11 FullProjectiveSignal11 p :=
  SemidirectProduct.lift_inl _ _ _ p

theorem fullProjectiveSymmetryPerm11_linear (k : LinearFourierLabel11) :
    fullProjectiveSymmetryPerm11 (SemidirectProduct.inr k) =
      projectiveLinearFourierPerm11 k :=
  SemidirectProduct.lift_inr _ _ _ k

end
end Biunimodular.F11
