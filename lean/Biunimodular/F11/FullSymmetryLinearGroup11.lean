/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ProofTactics
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false

namespace Biunimodular.F11

/-!
The projective linear/Fourier subgroup has normal forms `D^a C^c F^f`,
where `a` is modulo ten and `c,f` are bits.  The multiplication below
encodes `F D F⁻¹ = D⁻¹`, `F C F⁻¹ = D⁵ C`, and `F² = D⁵`.
-/

structure LinearFourierLabel11 where
  dilate : ZMod 10
  conjugate : Bool
  fourier : Bool
  deriving DecidableEq, Fintype

def fiveBit11 (b : Bool) : ZMod 10 := if b then 5 else 0

def linearFourierMul11
    (x y : LinearFourierLabel11) : LinearFourierLabel11 where
  dilate := x.dilate +
    (if x.fourier then -y.dilate + fiveBit11 y.conjugate else y.dilate) +
    (if x.fourier && y.fourier then 5 else 0)
  conjugate := xor x.conjugate y.conjugate
  fourier := xor x.fourier y.fourier

private def linearFourierOne11 : LinearFourierLabel11 :=
  ⟨0, false, false⟩

private def linearFourierInv11 (x : LinearFourierLabel11) :
    LinearFourierLabel11 :=
  if x.fourier then
    ⟨x.dilate + fiveBit11 x.conjugate + 5, x.conjugate, true⟩
  else
    ⟨-x.dilate, x.conjugate, false⟩

instance : Group LinearFourierLabel11 where
  mul := linearFourierMul11
  one := linearFourierOne11
  inv := linearFourierInv11
  mul_assoc := by native_decide +revert
  one_mul := by native_decide +revert
  mul_one := by native_decide +revert
  inv_mul_cancel := by native_decide +revert

theorem linearFourierLabel11_card :
    Fintype.card LinearFourierLabel11 = 40 := by native_decide

def linearD11 : LinearFourierLabel11 := ⟨1, false, false⟩
def linearC11 : LinearFourierLabel11 := ⟨0, true, false⟩
def linearF11 : LinearFourierLabel11 := ⟨0, false, true⟩
def linearR11 : LinearFourierLabel11 := ⟨5, false, false⟩

theorem linearF11_sq : linearF11 ^ 2 = linearR11 := by native_decide
theorem linearR11_eq_D_pow : linearR11 = linearD11 ^ 5 := by native_decide
theorem linearF11_conj_D :
    linearF11 * linearD11 * linearF11⁻¹ = linearD11⁻¹ := by native_decide
theorem linearF11_conj_C :
    linearF11 * linearC11 * linearF11⁻¹ = linearR11 * linearC11 := by
  native_decide
theorem linearR11_central (x : LinearFourierLabel11) :
    linearR11 * x = x * linearR11 := by native_decide +revert

end Biunimodular.F11
