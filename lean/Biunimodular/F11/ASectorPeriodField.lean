/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodRealization
import Biunimodular.F11.ArithmeticCyclotomicModel
import Mathlib.Algebra.Polynomial.Eval.Irreducible

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial
open scoped IntermediateField

noncomputable section

local instance : IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  CyclotomicField.isCyclotomicExtension 77 ℚ

/-- A primitive root in the canonical conductor-77 cyclotomic field. -/
def zeta77 : Conductor77Cyclotomic :=
  IsCyclotomicExtension.zeta 77 ℚ Conductor77Cyclotomic

/-- The Gaussian period indexed by the ten powers of 6 modulo 77. -/
def periodEta77 : Conductor77Cyclotomic :=
  eval₂ (Int.castRingHom Conductor77Cyclotomic) zeta77
    conductor77PeriodPolynomial

theorem zeta77_cyclotomic_root :
    eval₂ (Int.castRingHom Conductor77Cyclotomic) zeta77
      (cyclotomic 77 ℤ) = 0 := by
  have h := IsCyclotomicExtension.zeta_isRoot 77 ℚ Conductor77Cyclotomic
  change (cyclotomic 77 Conductor77Cyclotomic).eval zeta77 = 0 at h
  rw [← map_cyclotomic_int 77 Conductor77Cyclotomic] at h
  simpa only [eval₂_eq_eval_map] using h

/-- The actual conductor-77 period satisfies the sextic. -/
theorem periodEta77_isRoot_periodC77 :
    eval₂ (Int.castRingHom Conductor77Cyclotomic) periodEta77 periodC77 = 0 := by
  exact conductor77_period_sextic_relation zeta77 zeta77_cyclotomic_root

theorem periodC77_monic : periodC77.Monic := by
  let low : ℤ[X] := -X^5 - 20*X^4 + 20*X^3 + 106*X^2 - 106*X - 83
  have hlow : low.degree < 6 := by
    simp only [low]
    compute_degree
    norm_num
  rw [show periodC77 = X^6 + low by simp only [periodC77, low]; ring]
  exact monic_X_pow_add hlow

theorem periodC77_irreducible_over_Q :
    Irreducible (periodC77.map (Int.castRingHom ℚ)) := by
  have hZ : Irreducible periodC77 := by
    apply periodC77_monic.irreducible_of_irreducible_map
      (Int.castRingHom (ZMod 2))
    rw [periodC77_mod2]
    exact periodC77mod2_irreducible
  exact (periodC77_monic.irreducible_iff_irreducible_map_fraction_map).1 hZ

/-- The chosen Gaussian period has precisely the sextic minimal polynomial. -/
theorem periodEta77_minpoly :
    periodC77.map (Int.castRingHom ℚ) = minpoly ℚ periodEta77 := by
  have hroot : (aeval periodEta77)
      (periodC77.map (Int.castRingHom ℚ)) = 0 := by
    have hcomp : (algebraMap ℚ Conductor77Cyclotomic).comp
        (Int.castRingHom ℚ) = Int.castRingHom Conductor77Cyclotomic := by
      ext n
      simp
    simpa only [aeval_def, eval₂_map, hcomp] using
      periodEta77_isRoot_periodC77
  exact minpoly.eq_of_irreducible_of_monic
    periodC77_irreducible_over_Q hroot
    (periodC77_monic.map (Int.castRingHom ℚ))

/-- The concrete Gaussian-period field inside the conductor-77 field. -/
def conductor77PeriodField : IntermediateField ℚ Conductor77Cyclotomic :=
  ℚ⟮periodEta77⟯

theorem conductor77PeriodField_finrank :
    Module.finrank ℚ conductor77PeriodField = 6 := by
  have hint : IsIntegral ℚ periodEta77 := IsIntegral.of_finite ℚ periodEta77
  change Module.finrank ℚ ℚ⟮periodEta77⟯ = 6
  rw [IntermediateField.adjoin.finrank hint, ← periodEta77_minpoly]
  norm_num [periodC77]
  compute_degree <;> norm_num

theorem conductor77PeriodField_isAbelianGalois :
    IsAbelianGalois ℚ conductor77PeriodField := by
  let : IsAbelianGalois ℚ Conductor77Cyclotomic :=
    conductor77_isAbelianGalois
  infer_instance

end
end Biunimodular.F11
