/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.BSectorQ80MonicTransform
import Biunimodular.F11.Mod17DivisorConstantObstruction
import Biunimodular.F11.MonicRationalDivisorLift
import Biunimodular.F11.IrreducibleSquareViaDivisorConstant

set_option autoImplicit false
set_option maxRecDepth 100000
namespace Biunimodular.F11
open Polynomial
noncomputable section

theorem bSectorG40Monic_constant_mod17 : (bSectorG40Monic.coeff 0 : ZMod 17) = 9 := by
  have hc : integerCoefficientEval (0 : ℤ) bSectorG40MonicCoeffs % 17 = 9 := by native_decide
  have he : bSectorG40Monic.coeff 0 = integerCoefficientEval (0 : ℤ) bSectorG40MonicCoeffs := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact integerCoefficientPolynomial_eval (R := ℤ) (0 : ℤ) bSectorG40MonicCoeffs
  rw [he, CharP.intCast_eq_intCast_mod (ZMod 17) 17]
  change (Int.castRingHom (ZMod 17))
    (integerCoefficientEval (0 : ℤ) bSectorG40MonicCoeffs % (17 : ℤ)) = 9
  rw [hc]
  decide

theorem bSectorG80Monic_irreducible_Q :
    Irreducible (bSectorG80Monic.map (Int.castRingHom ℚ)) := by
  have hmap : bSectorG80Monic.map (Int.castRingHom ℚ) =
      (bSectorG40Monic.map (Int.castRingHom ℚ)).comp (X ^ 2) := by
    rw [bSectorG80Monic, Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X]
  rw [hmap]
  apply irreducible_comp_square_of_divisor_constant _
    (bSectorG40Monic_monic.map _) bSectorG40Monic_irreducible_Q
  intro q hq hd hdiv heq
  have hpdeg : (bSectorG40Monic.map (Int.castRingHom ℚ)).natDegree = 40 :=
    (bSectorG40Monic_monic.natDegree_map _).trans bSectorG40Monic_degree
  rw [hpdeg] at hd heq
  norm_num only [even_two, Even.neg_one_pow, one_mul] at heq
  have hv : q ∣ bSectorG80Monic.map (Int.castRingHom ℚ) := hmap.symm ▸ hdiv
  obtain ⟨g, hgm, hg, hgd, hgv⟩ := monic_rational_divisor_lift
    bSectorG80Monic bSectorG80Monic_monic q hq hv
  have hcZ : g.coeff 0 ^ 2 = bSectorG40Monic.coeff 0 := by
    rw [← hg, Polynomial.coeff_map, Polynomial.coeff_map] at heq
    change (g.coeff 0 : ℚ) ^ 2 = (bSectorG40Monic.coeff 0 : ℚ) at heq
    exact_mod_cast heq
  let r := g.map (Int.castRingHom (ZMod 17))
  have hrm : r.Monic := hgm.map _
  have hrd : r.natDegree = 40 := (hgm.natDegree_map _).trans (hgd.trans hd)
  have hrv : r ∣ coordinateMod17Factor1 * coordinateMod17Factor2 *
      coordinateMod17Factor3 * coordinateMod17Factor4 := by
    rw [← bSectorG80Monic_map17]
    exact Polynomial.map_dvd (Int.castRingHom (ZMod 17)) hgv
  have hrc : r.coeff 0 ^ 2 = 9 := by
    have h := congrArg (Int.castRingHom (ZMod 17)) hcZ
    simp only [map_pow] at h
    change (g.coeff 0 : ZMod 17) ^ 2 = (bSectorG40Monic.coeff 0 : ZMod 17) at h
    simp only [r, Polynomial.coeff_map]
    change (g.coeff 0 : ZMod 17) ^ 2 = 9
    exact h.trans bSectorG40Monic_constant_mod17
  apply mod17_divisor_constant_obstruction
    coordinateMod17Factor1 coordinateMod17Factor2 coordinateMod17Factor3
    coordinateMod17Factor4 r
    ⟨coordinateMod17Factor1_monic, coordinateMod17Factor1_irreducible⟩
    ⟨coordinateMod17Factor2_monic, coordinateMod17Factor2_irreducible⟩
    ⟨coordinateMod17Factor3_monic, coordinateMod17Factor3_irreducible⟩
    ⟨coordinateMod17Factor4_monic, coordinateMod17Factor4_irreducible⟩
    coordinateMod17Factor1_degree coordinateMod17Factor2_degree
    coordinateMod17Factor3_degree coordinateMod17Factor4_degree
    _ _ _ _ hrm hrd hrv hrc
  all_goals
    simp [coordinateMod17Factor1, coordinateMod17Factor1Coeffs,
      coordinateMod17Factor2, coordinateMod17Factor2Coeffs,
      coordinateMod17Factor3, coordinateMod17Factor3Coeffs,
      coordinateMod17Factor4, coordinateMod17Factor4Coeffs,
      integerCoefficientEval] <;> decide

end
end Biunimodular.F11
