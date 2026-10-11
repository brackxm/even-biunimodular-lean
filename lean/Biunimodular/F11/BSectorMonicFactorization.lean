/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.BSectorFrobeniusCertificates
import Biunimodular.F11.InvariantBMonicTransform

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

private instance : Fact (Nat.Prime 37) := ⟨by decide⟩
private instance : Fact (Nat.Prime 211) := ⟨by decide⟩

def B37monicSeven : (ZMod 37)[X] :=
  X^7 + 12*X^6 + 12*X^5 + 33*X^4 + 29*X^3 + 21*X^2 + 8*X + 25

theorem B37monicSeven_scaled :
    B37monicSeven = B37seven.scaleRoots 10 := by
  ext n
  rw [Polynomial.coeff_scaleRoots]
  have hdeg : B37seven.natDegree = 7 := by
    norm_num [B37seven]
    compute_degree <;> norm_num
  rw [hdeg]
  by_cases hn : n ≤ 7
  · interval_cases n <;>
      norm_num [B37monicSeven, B37seven, Polynomial.coeff_X,
        Polynomial.coeff_X_pow] <;> reduce_mod_char
  · have hgt : 7 < n := by omega
    have hL : B37monicSeven.coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have : B37monicSeven.natDegree = 7 := by
        norm_num [B37monicSeven]
        compute_degree <;> norm_num
      omega
    have hR : B37seven.coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    rw [hL, hR]
    simp

theorem B37monicSeven_irreducible : Irreducible B37monicSeven := by
  rw [B37monicSeven_scaled]
  exact (irreducible_scaleRoots_iff_of_ne_zero B37seven
    (by decide : (10 : ZMod 37) ≠ 0)).mpr B37seven_irreducible

theorem bMonic_mod37_factor :
    invariantBMonicTransform.map (Int.castRingHom (ZMod 37)) =
      (X + 36) * B37monicSeven := by
  norm_num [invariantBMonicTransform, B37monicSeven]
  all_goals reduce_mod_char
  all_goals ring_nf
  all_goals reduce_mod_char

def B211monicFive : (ZMod 211)[X] :=
  X^5 + 44*X^4 + 101*X^3 + 129*X^2 + 192*X + 128

theorem B211monicFive_scaled :
    B211monicFive = B211five.scaleRoots 55 := by
  ext n
  rw [Polynomial.coeff_scaleRoots]
  have hdeg : B211five.natDegree = 5 := by
    norm_num [B211five]
    compute_degree <;> norm_num
  rw [hdeg]
  by_cases hn : n ≤ 5
  · interval_cases n <;>
      norm_num [B211monicFive, B211five, Polynomial.coeff_X,
        Polynomial.coeff_X_pow] <;> reduce_mod_char
  · have hgt : 5 < n := by omega
    have hL : B211monicFive.coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have : B211monicFive.natDegree = 5 := by
        norm_num [B211monicFive]
        compute_degree <;> norm_num
      omega
    have hR : B211five.coeff n = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      omega
    rw [hL, hR]
    simp

theorem B211monicFive_irreducible : Irreducible B211monicFive := by
  rw [B211monicFive_scaled]
  exact (irreducible_scaleRoots_iff_of_ne_zero B211five
    (by decide : (55 : ZMod 211) ≠ 0)).mpr B211five_irreducible

theorem bMonic_mod211_factor :
    invariantBMonicTransform.map (Int.castRingHom (ZMod 211)) =
      (X + 7) * (X + 141) * (X + 67) * B211monicFive := by
  norm_num [invariantBMonicTransform, B211monicFive]
  all_goals reduce_mod_char
  all_goals ring_nf
  all_goals reduce_mod_char

end

end Biunimodular.F11
