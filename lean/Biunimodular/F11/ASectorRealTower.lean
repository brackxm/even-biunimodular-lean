/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodRealSubfield
import Biunimodular.F11.ASectorFieldGeneration

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial
open scoped IntermediateField

noncomputable section

/-- The explicit Gaussian period viewed in the maximal real subfield. -/
def periodEta77Real : Conductor77MaxReal :=
  ⟨periodEta77, periodEta77_mem_maximalReal⟩

/-- Its real sextic field. -/
def conductor77RealPeriodField : IntermediateField ℚ Conductor77MaxReal :=
  ℚ⟮periodEta77Real⟯

private theorem periodEta77Real_isRoot_periodC77 :
    eval₂ (Int.castRingHom Conductor77MaxReal) periodEta77Real periodC77 = 0 := by
  apply Subtype.ext
  have h := periodEta77_isRoot_periodC77
  simp [periodC77, periodEta77Real] at h ⊢
  exact h

private theorem periodEta77Real_minpoly :
    periodC77.map (Int.castRingHom ℚ) = minpoly ℚ periodEta77Real := by
  have hroot : (aeval periodEta77Real)
      (periodC77.map (Int.castRingHom ℚ)) = 0 := by
    have hcomp : (algebraMap ℚ Conductor77MaxReal).comp
        (Int.castRingHom ℚ) = Int.castRingHom Conductor77MaxReal := by
      ext n
      simp
    simpa only [aeval_def, eval₂_map, hcomp] using
      periodEta77Real_isRoot_periodC77
  exact minpoly.eq_of_irreducible_of_monic
    periodC77_irreducible_over_Q hroot
    (periodC77_monic.map (Int.castRingHom ℚ))

/-- The real period field has degree six over the rationals. -/
theorem conductor77RealPeriodField_finrank :
    Module.finrank ℚ conductor77RealPeriodField = 6 := by
  have hint : IsIntegral ℚ periodEta77Real :=
    IsIntegral.of_finite ℚ periodEta77Real
  change Module.finrank ℚ ℚ⟮periodEta77Real⟯ = 6
  rw [IntermediateField.adjoin.finrank hint, ← periodEta77Real_minpoly]
  norm_num [periodC77]
  compute_degree <;> norm_num

/-- The explicit real conductor-77 field is degree five over its actual
Gaussian-period sextic subfield. -/
theorem conductor77_real_relative_finrank :
    Module.finrank conductor77RealPeriodField Conductor77MaxReal = 5 := by
  have htower := Module.finrank_mul_finrank ℚ
    conductor77RealPeriodField Conductor77MaxReal
  rw [conductor77RealPeriodField_finrank,
    conductor77_maxReal_finrank] at htower
  omega

end
end Biunimodular.F11
