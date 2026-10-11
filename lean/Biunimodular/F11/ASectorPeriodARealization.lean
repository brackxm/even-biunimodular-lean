/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodField
import Biunimodular.F11.ASectorPeriodAIdentity
import Biunimodular.F11.InvariantIrreducibilityInterface

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial
open scoped IntermediateField

noncomputable section

/-- The the invariant coordinate `u = N(η)/13` in the conductor-77 field. -/
def periodInvariantU77 : Conductor77Cyclotomic :=
  eval₂ (Int.castRingHom Conductor77Cyclotomic) periodEta77 periodN77 / 13

/-- The explicitly identified period coordinate is a root of the actual
A-sector invariant polynomial. -/
theorem periodInvariantU77_isRoot_invariantA :
    eval₂ (Int.castRingHom Conductor77Cyclotomic)
      periodInvariantU77 invariantA = 0 := by
  let E : ℤ[X] →+* Conductor77Cyclotomic :=
    eval₂RingHom (Int.castRingHom Conductor77Cyclotomic) periodEta77
  let n : Conductor77Cyclotomic := E periodN77
  have hC : E periodC77 = 0 := periodEta77_isRoot_periodC77
  have hraw : n^6 - 6320*13*n^5 + 10298240*13^2*n^4 -
      1009036608*13^3*n^3 + 1012283392*13^4*n^2 -
      84262912*13^5*n + 692224*13^6 = 0 := by
    have h := congrArg E periodN77_A_identity
    simp only [map_pow, map_mul, map_add, map_sub, map_ofNat,
      hC, zero_mul] at h
    simpa only [n] using h
  have hscale : (13 : Conductor77Cyclotomic)^6 *
      eval₂ (Int.castRingHom Conductor77Cyclotomic) (n / 13) invariantA =
      n^6 - 6320*13*n^5 + 10298240*13^2*n^4 -
        1009036608*13^3*n^3 + 1012283392*13^4*n^2 -
        84262912*13^5*n + 692224*13^6 := by
    simp only [invariantA, eval₂_add, eval₂_sub, eval₂_mul,
      eval₂_pow, eval₂_X, eval₂_ofNat]
    field_simp
  have h : (13 : Conductor77Cyclotomic)^6 *
      eval₂ (Int.castRingHom Conductor77Cyclotomic) (n / 13) invariantA = 0 := by
    rw [hscale]
    exact hraw
  have h13 : (13 : Conductor77Cyclotomic)^6 ≠ 0 := by norm_num
  have hroot := (mul_eq_zero.mp h).resolve_left h13
  exact hroot

/-- The actual A invariant has the displayed irreducible sextic as its
minimal polynomial over the rationals. -/
theorem periodInvariantU77_minpoly :
    minpoly ℚ periodInvariantU77 =
      invariantA.map (Int.castRingHom ℚ) := by
  have hrootQ : (aeval periodInvariantU77)
      (invariantA.map (Int.castRingHom ℚ)) = 0 := by
    have hcomp : (algebraMap ℚ Conductor77Cyclotomic).comp
        (Int.castRingHom ℚ) = Int.castRingHom Conductor77Cyclotomic := by
      ext n
      simp
    simpa only [aeval_def, eval₂_map, hcomp] using
      periodInvariantU77_isRoot_invariantA
  exact (minpoly.eq_of_irreducible_of_monic
    invariantA_irreducible_over_Q hrootQ
    (invariantA_monic.map (Int.castRingHom ℚ))).symm

/-- The A-component invariant itself generates the concrete conductor-77
Gaussian-period field. -/
theorem periodInvariantU77_generates_periodField :
    ℚ⟮periodInvariantU77⟯ = conductor77PeriodField := by
  have hrootQ : (aeval periodInvariantU77)
      (invariantA.map (Int.castRingHom ℚ)) = 0 := by
    have hcomp : (algebraMap ℚ Conductor77Cyclotomic).comp
        (Int.castRingHom ℚ) = Int.castRingHom Conductor77Cyclotomic := by
      ext n
      simp
    simpa only [aeval_def, eval₂_map, hcomp] using
      periodInvariantU77_isRoot_invariantA
  have hminpoly : invariantA.map (Int.castRingHom ℚ) =
      minpoly ℚ periodInvariantU77 :=
    minpoly.eq_of_irreducible_of_monic invariantA_irreducible_over_Q
      hrootQ (invariantA_monic.map (Int.castRingHom ℚ))
  have huFin : Module.finrank ℚ ℚ⟮periodInvariantU77⟯ = 6 := by
    have hi : IsIntegral ℚ periodInvariantU77 :=
      IsIntegral.of_finite ℚ periodInvariantU77
    rw [IntermediateField.adjoin.finrank hi, ← hminpoly]
    norm_num [invariantA]
    compute_degree <;> norm_num
  have huMem : periodInvariantU77 ∈ conductor77PeriodField := by
    change periodInvariantU77 ∈ ℚ⟮periodEta77⟯
    apply (IntermediateField.mem_adjoin_simple_iff ℚ periodInvariantU77).2
    refine ⟨periodN77.map (Int.castRingHom ℚ), C 13, ?_⟩
    simp only [periodInvariantU77, aeval_def, eval₂_map,
      eval₂_C]
    have hcomp : (algebraMap ℚ Conductor77Cyclotomic).comp
        (Int.castRingHom ℚ) = Int.castRingHom Conductor77Cyclotomic := by
      ext n
      simp
    rw [hcomp]
    norm_num
  have hle : ℚ⟮periodInvariantU77⟯ ≤ conductor77PeriodField := by
    exact IntermediateField.adjoin_simple_le_iff.mpr huMem
  apply IntermediateField.eq_of_le_of_finrank_eq hle
  rw [huFin, conductor77PeriodField_finrank]

end
end Biunimodular.F11
