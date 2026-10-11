/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.GroupTheory.GroupAction.Quotient

set_option autoImplicit false

namespace Biunimodular.F11
noncomputable section

variable (R G X : Type*) [CommSemiring R] [AddGroup G] [AddAction G X]

/-- Functions unchanged by the given action form a subalgebra. -/
def orbitInvariantFunctionAlgebra : Subalgebra R (X → R) where
  carrier := {f | ∀ (g : G) (x : X), f (g +ᵥ x) = f x}
  mul_mem' hf hk g x := by simp only [Pi.mul_apply, hf g x, hk g x]
  add_mem' hf hk g x := by simp only [Pi.add_apply, hf g x, hk g x]
  algebraMap_mem' _ _ _ := rfl

/-- Pullback along the actual orbit projection. -/
def orbitFunctionPullback :
    (AddAction.orbitRel.Quotient G X → R) →ₐ[R]
      orbitInvariantFunctionAlgebra R G X where
  toFun f := ⟨fun x => f (Quotient.mk'' x), fun g x => by
    exact congrArg f (AddAction.orbitRel.Quotient.quotient_vadd_eq (g := g) (a := x))⟩
  map_zero' := Subtype.ext rfl
  map_one' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl

/-- Invariant functions are precisely functions on the orbit space, with
the isomorphism given by pullback along the orbit projection. -/
def orbitFunctionAlgebraEquiv :
    (AddAction.orbitRel.Quotient G X → R) ≃ₐ[R]
      orbitInvariantFunctionAlgebra R G X := by
  apply AlgEquiv.ofBijective (orbitFunctionPullback R G X)
  constructor
  · intro f k h
    funext q
    induction q using Quotient.inductionOn with
    | _ x => exact congrFun (congrArg Subtype.val h) x
  · intro f
    let descended : AddAction.orbitRel.Quotient G X → R :=
      Quotient.lift f.1 (fun x y h => by
        obtain ⟨g, rfl⟩ := AddAction.mem_orbit_iff.mp (AddAction.orbitRel_apply.mp h)
        exact f.2 g y)
    exact ⟨descended, Subtype.ext rfl⟩

@[simp] theorem orbitFunctionAlgebraEquiv_apply
    (f : AddAction.orbitRel.Quotient G X → R) (x : X) :
    (orbitFunctionAlgebraEquiv R G X f).1 x = f (Quotient.mk'' x) := rfl

end
end Biunimodular.F11
