/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.InvariantBMonicTransform

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 37) := ⟨by decide⟩
private instance : Fact (Nat.Prime 211) := ⟨by decide⟩

theorem bMonic_mod5_separable :
    (invariantBMonicTransform.map (Int.castRingHom (ZMod 5))).Separable := by
  rw [invariantBMonicTransform_mod5]
  exact PerfectField.separable_of_irreducible invariantB5_irreducible

private def b37SepU : (ZMod 37)[X] :=
  8*X^6 + 29*X^5 + 15*X^4 + 31*X^3 + 36*X^2 + 23*X + 7
private def b37SepV : (ZMod 37)[X] :=
  36*X^7 + 32*X^6 + 11*X^5 + 19*X^4 + 2*X^3 + 27*X^2 + 36*X + 6

theorem bMonic_mod37_separable :
    (invariantBMonicTransform.map (Int.castRingHom (ZMod 37))).Separable := by
  refine ⟨b37SepU, b37SepV, ?_⟩
  norm_num [b37SepU, b37SepV, invariantBMonicTransform]
  all_goals reduce_mod_char
  all_goals simp only [Polynomial.C_ofNat]
  all_goals ring_nf
  all_goals reduce_mod_char

private def b211SepU : (ZMod 211)[X] :=
  69*X^6 + 93*X^5 + 10*X^4 + 22*X^3 + 183*X^2 + 169*X + 26
private def b211SepV : (ZMod 211)[X] :=
  176*X^7 + 174*X^6 + 177*X^5 + 124*X^4 + 173*X^3 + 124*X^2 + 200*X + 122

theorem bMonic_mod211_separable :
    (invariantBMonicTransform.map (Int.castRingHom (ZMod 211))).Separable := by
  refine ⟨b211SepU, b211SepV, ?_⟩
  norm_num [b211SepU, b211SepV, invariantBMonicTransform]
  all_goals reduce_mod_char
  all_goals simp only [Polynomial.C_ofNat]
  all_goals ring_nf
  all_goals reduce_mod_char

end

end Biunimodular.F11
