/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorConductor77Certificates
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic.NormNum.Prime
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Polynomial
namespace Biunimodular.F11
noncomputable section
def conductor77PeriodPolynomial : ℤ[X] := X + X^6 + X^13 + X^15 + X^36 + X^41 + X^62 + X^64 + X^71 + X^76
def phi77 : ℤ[X] := 1 - X + X^7 - X^8 + X^11 - X^12 + X^14 - X^15 + X^18 - X^19 + X^21 - X^23 + X^25 - X^26 + X^28 - X^30 + X^32 - X^34 + X^35 - X^37 + X^39 - X^41 + X^42 - X^45 + X^46 - X^48 + X^49 - X^52 + X^53 - X^59 + X^60
theorem phi77_eq_cyclotomic : phi77 = cyclotomic 77 ℤ := by
  apply (eq_cyclotomic_iff (R := ℤ) (by norm_num : 0 < 77) phi77).2
  have hproper : Nat.properDivisors 77 = {1, 7, 11} := by native_decide
  rw [hproper]
  simp only [Finset.prod_insert (by decide : 1 ∉ ({7, 11} : Finset ℕ)),
    Finset.prod_insert (by decide : 7 ∉ ({11} : Finset ℕ)),
    Finset.prod_singleton]
  let : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  rw [cyclotomic_one, cyclotomic_prime ℤ 7, cyclotomic_prime ℤ 11]
  simp only [Finset.sum_range_succ]
  simp only [Finset.sum_range_zero]
  simp only [phi77]
  ring

private def r0 : ℤ[X] := 1
private def r1 : ℤ[X] := X^3 - X^8 + X^14 - X^20 - X^22 + X^25 - X^27 - X^29 - X^34 + X^36 - X^43 + X^47 - X^48 - X^50 - X^55 - X^57 + X^58
private def r2 : ℤ[X] := 7 + X^7 - 2*X^9 + X^11 + X^14 - 2*X^16 + X^18 - X^19 - X^20 + X^21 + X^22 - 2*X^23 + X^25 - X^27 + X^28 + X^29 - X^30 - X^31 + X^32 - 2*X^33 - X^34 + X^35 + X^36 - 2*X^37 - X^38 + X^39 - X^41 + X^43 - 3*X^44 - X^45 + X^46 + X^47 - X^48 + X^50 - X^52 + X^57 - X^58 - X^59
private def r3 : ℤ[X] := -5 + 7*X^3 + 2*X^4 - 2*X^7 - 7*X^8 + 7*X^14 + 2*X^15 - 2*X^18 + 2*X^19 - 9*X^20 - 2*X^21 - 12*X^22 + 9*X^25 + 2*X^26 - 9*X^27 - 2*X^28 - 9*X^29 + 2*X^30 - 2*X^31 - 2*X^32 - 3*X^33 - 9*X^34 - 2*X^35 + 9*X^36 + 2*X^37 - 2*X^38 - 2*X^39 + 2*X^41 - 2*X^42 - 9*X^43 - 3*X^44 - 2*X^45 - 2*X^46 + 9*X^47 - 7*X^48 - 2*X^49 - 9*X^50 + 2*X^52 - 12*X^55 - 2*X^56 - 9*X^57 + 9*X^58
private def r4 : ℤ[X] := 60 - 5*X^3 + 5*X^4 + 7*X^7 + 5*X^8 - 24*X^9 + 12*X^11 + 7*X^14 + 5*X^15 - 24*X^16 + 7*X^18 - 7*X^19 - 12*X^20 + 7*X^21 + 11*X^22 - 24*X^23 + 12*X^25 + 5*X^26 - 12*X^27 + 7*X^28 + 12*X^29 - 7*X^30 - 17*X^31 + 7*X^32 - 25*X^33 - 12*X^34 + 7*X^35 + 12*X^36 - 19*X^37 - 17*X^38 + 7*X^39 - 7*X^41 - 5*X^42 + 12*X^43 - 37*X^44 - 17*X^45 + 7*X^46 + 12*X^47 - 7*X^48 - 5*X^49 + 12*X^50 - 7*X^52 - X^55 - 5*X^56 + 12*X^57 - 12*X^58 - 12*X^59
private def r5 : ℤ[X] := -74 + 60*X^3 + 30*X^4 - 29*X^7 - 60*X^8 - 2*X^9 + X^11 + 61*X^14 + 30*X^15 - 2*X^16 - 29*X^18 + 29*X^19 - 91*X^20 - 29*X^21 - 134*X^22 - 2*X^23 + 91*X^25 + 30*X^26 - 91*X^27 - 29*X^28 - 89*X^29 + 29*X^30 - 31*X^31 - 29*X^32 - 60*X^33 - 91*X^34 - 29*X^35 + 91*X^36 + 28*X^37 - 31*X^38 - 29*X^39 + 29*X^41 - 30*X^42 - 89*X^43 - 61*X^44 - 31*X^45 - 29*X^46 + 91*X^47 - 61*X^48 - 30*X^49 - 89*X^50 + 29*X^52 - 135*X^55 - 30*X^56 - 89*X^57 + 89*X^58 - X^59
private def r6 : ℤ[X] := 567 - 74*X^3 + 90*X^4 + 45*X^7 + 74*X^8 - 270*X^9 + 135*X^11 + 61*X^14 + 90*X^15 - 270*X^16 + 45*X^18 - 45*X^19 - 151*X^20 + 45*X^21 + 114*X^22 - 270*X^23 + 151*X^25 + 90*X^26 - 151*X^27 + 45*X^28 + 119*X^29 - 45*X^30 - 225*X^31 + 45*X^32 - 288*X^33 - 151*X^34 + 45*X^35 + 151*X^36 - 180*X^37 - 225*X^38 + 45*X^39 - 45*X^41 - 90*X^42 + 119*X^43 - 423*X^44 - 225*X^45 + 45*X^46 + 151*X^47 - 61*X^48 - 90*X^49 + 119*X^50 - 45*X^52 - 21*X^55 - 90*X^56 + 119*X^57 - 119*X^58 - 135*X^59
private def q0 : ℤ[X] := X + X^2 + X^6 + X^7 + X^8 + X^9 + 2*X^10 + 2*X^11 + X^12 + X^13 + X^14 + X^15 + X^16
private def q1 : ℤ[X] := -7 - 7*X - 7*X^2 - 7*X^3 - 6*X^4 - 6*X^5 - 6*X^6 + 2*X^9 + 2*X^10 + 7*X^11 + 7*X^12 + 7*X^13 + 6*X^14 + 6*X^15 + 7*X^16 + 7*X^17 + 2*X^18 + 3*X^19 + 3*X^20 + 2*X^21 + 2*X^22 - X^23 - X^24 - X^25 - 3*X^26 - 4*X^27 - 4*X^28 - 4*X^29 - 5*X^30 - 5*X^31 - 4*X^32 - 2*X^33 - 2*X^35 - 2*X^36 + X^37 + X^38 + 2*X^39 + 2*X^42 + 2*X^43 + X^44 + X^45 + 2*X^46 + 2*X^47 + X^48 - X^49 - X^50 - X^51 - X^52 - 3*X^53 - 2*X^54 - 2*X^55 - 2*X^56 - 2*X^57 - 3*X^58 - 3*X^59 - X^60 - 3*X^61 - 2*X^62 - 3*X^63 - 3*X^64 - 3*X^65 - 3*X^66 - 2*X^67 - X^68 - X^70 - X^71 + X^74
private def q2 : ℤ[X] := 5 + 12*X + 12*X^2 + 5*X^3 + 3*X^4 + 3*X^5 + 10*X^6 + 7*X^7 + 8*X^8 + 8*X^9 + 13*X^10 + 10*X^11 + 4*X^12 + 5*X^13 + 3*X^14 + X^15 + X^16 - 5*X^17 - 3*X^19 - X^20 + 2*X^21 + 6*X^22 + 6*X^23 + 4*X^24 + X^25 + 5*X^26 + 6*X^27 + 6*X^28 + X^29 + X^30 + 2*X^31 + 4*X^32 + 2*X^33 - 2*X^34 - X^35 + X^36 + X^37 - X^38 - 3*X^39 - 3*X^40 - 2*X^41 - 5*X^42 - 4*X^43 - 4*X^44 - 3*X^45 - 4*X^46 - 2*X^47 - X^48 - 3*X^50 - 3*X^51 - 3*X^52 - 2*X^53 - 5*X^54 - 5*X^55 - 3*X^56 - X^57 - X^58 - 3*X^59 - 4*X^60 - X^64 - X^65 - X^66 - X^67 - 2*X^68 - 3*X^69 - 2*X^70 - X^71 - X^72 - X^73 - 2*X^74 - X^75
private def q3 : ℤ[X] := -60 - 65*X - 65*X^2 - 60*X^3 - 58*X^4 - 56*X^5 - 61*X^6 - 8*X^7 - 10*X^8 + 14*X^9 + 11*X^10 + 57*X^11 + 60*X^12 + 58*X^13 + 46*X^14 + 48*X^15 + 55*X^16 + 60*X^17 + 19*X^18 + 28*X^19 + 30*X^20 + 26*X^21 + 28*X^22 + 2*X^23 - 3*X^25 - 19*X^26 - 28*X^27 - 33*X^28 - 37*X^29 - 49*X^30 - 47*X^31 - 35*X^32 - 15*X^33 + X^34 - 15*X^35 - 17*X^36 + 9*X^37 + 9*X^38 + 16*X^39 - 4*X^40 - 6*X^41 + 10*X^42 + 10*X^43 + 3*X^44 + 3*X^45 + 12*X^46 + 10*X^47 + 3*X^48 - 13*X^49 - 11*X^50 - 16*X^51 - 18*X^52 - 39*X^53 - 30*X^54 - 32*X^55 - 32*X^56 - 32*X^57 - 34*X^58 - 32*X^59 - 16*X^60 - 32*X^61 - 21*X^62 - 28*X^63 - 30*X^64 - 35*X^65 - 35*X^66 - 23*X^67 - 12*X^68 - 5*X^69 - 14*X^70 - 14*X^71 - 2*X^72 + 9*X^74
private def q4 : ℤ[X] := 74 + 134*X + 134*X^2 + 74*X^3 + 39*X^4 + 44*X^5 + 104*X^6 + 59*X^7 + 66*X^8 + 68*X^9 + 109*X^10 + 69*X^11 + 16*X^12 + 23*X^13 - 2*X^14 - 21*X^15 - 26*X^16 - 74*X^17 - 4*X^18 - 40*X^19 - 11*X^20 + 31*X^21 + 84*X^22 + 93*X^23 + 64*X^24 + 27*X^25 + 80*X^26 + 92*X^27 + 86*X^28 + 16*X^29 + 15*X^30 + 32*X^31 + 57*X^32 + 38*X^33 - 15*X^34 + 2*X^35 + 21*X^36 + 12*X^37 - 12*X^38 - 41*X^39 - 46*X^40 - 39*X^41 - 80*X^42 - 68*X^43 - 63*X^44 - 51*X^45 - 63*X^46 - 44*X^47 - 27*X^48 - 10*X^49 - 41*X^50 - 47*X^51 - 52*X^52 - 41*X^53 - 77*X^54 - 82*X^55 - 58*X^56 - 34*X^57 - 23*X^58 - 42*X^59 - 59*X^60 - 6*X^61 - X^62 + 4*X^63 - 13*X^64 - 19*X^65 - 19*X^66 - 18*X^67 - 25*X^68 - 42*X^69 - 30*X^70 - 18*X^71 - 17*X^72 - 12*X^73 - 24*X^74 - 12*X^75
private def q5 : ℤ[X] := -567 - 641*X - 641*X^2 - 567*X^3 - 597*X^4 - 567*X^5 - 641*X^6 - 119*X^7 - 148*X^8 + 122*X^9 + 76*X^10 + 538*X^11 + 583*X^12 + 554*X^13 + 404*X^14 + 432*X^15 + 492*X^16 + 567*X^17 + 195*X^18 + 269*X^19 + 314*X^20 + 315*X^21 + 349*X^22 + 94*X^23 + 62*X^24 + X^25 - 132*X^26 - 221*X^27 - 296*X^28 - 361*X^29 - 496*X^30 - 465*X^31 - 315*X^32 - 107*X^33 + 26*X^34 - 123*X^35 - 151*X^36 + 104*X^37 + 102*X^38 + 147*X^39 - 76*X^40 - 105*X^41 + 29*X^42 + 30*X^43 - 30*X^44 - 29*X^45 + 60*X^46 + 45*X^47 - 14*X^48 - 163*X^49 - 136*X^50 - 211*X^51 - 241*X^52 - 465*X^53 - 391*X^54 - 421*X^55 - 406*X^56 - 404*X^57 - 389*X^58 - 361*X^59 - 212*X^60 - 345*X^61 - 225*X^62 - 285*X^63 - 316*X^64 - 391*X^65 - 391*X^66 - 256*X^67 - 137*X^68 - 78*X^69 - 167*X^70 - 166*X^71 - 31*X^72 - X^73 + 88*X^74 - X^75
private theorem periodStep0 : conductor77PeriodPolynomial * r0 = phi77 * q0 + r1 := by
  simp only [conductor77PeriodPolynomial, r0, r1, phi77, q0]
  ring
private theorem periodStep1 : conductor77PeriodPolynomial * r1 = phi77 * q1 + r2 := by
  simp only [conductor77PeriodPolynomial, r1, r2, phi77, q1]
  ring
private theorem periodStep2 : conductor77PeriodPolynomial * r2 = phi77 * q2 + r3 := by
  simp only [conductor77PeriodPolynomial, r2, r3, phi77, q2]
  ring
private theorem periodStep3 : conductor77PeriodPolynomial * r3 = phi77 * q3 + r4 := by
  simp only [conductor77PeriodPolynomial, r3, r4, phi77, q3]
  ring
private theorem periodStep4 : conductor77PeriodPolynomial * r4 = phi77 * q4 + r5 := by
  simp only [conductor77PeriodPolynomial, r4, r5, phi77, q4]
  ring
private theorem periodStep5 : conductor77PeriodPolynomial * r5 = phi77 * q5 + r6 := by
  simp only [conductor77PeriodPolynomial, r5, r6, phi77, q5]
  ring

private theorem period_remainders_linear :
    -83 * r0 - 106 * r1 + 106 * r2 + 20 * r3 -
      20 * r4 - r5 + r6 = 0 := by
  simp only [r0, r1, r2, r3, r4, r5, r6]
  ring

/-- Every primitive conductor-77 root gives a Gaussian period satisfying
the explicit sextic `C`. The six polynomial reductions above are exact
certificates for this relation. -/
theorem conductor77_period_sextic_relation {R : Type*} [CommRing R]
    (z : R)
    (hz : Polynomial.eval₂ (Int.castRingHom R) z (cyclotomic 77 ℤ) = 0) :
    Polynomial.eval₂ (Int.castRingHom R)
      (Polynomial.eval₂ (Int.castRingHom R) z conductor77PeriodPolynomial)
      periodC77 = 0 := by
  let E : ℤ[X] →+* R := Polynomial.eval₂RingHom (Int.castRingHom R) z
  have hphi : E phi77 = 0 := by
    change Polynomial.eval₂ (Int.castRingHom R) z phi77 = 0
    rw [phi77_eq_cyclotomic]
    exact hz
  have step_eval (a b q : ℤ[X])
      (h : conductor77PeriodPolynomial * a = phi77 * q + b) :
      E conductor77PeriodPolynomial * E a = E b := by
    have h' := congrArg E h
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add] using h'
  have hs0 := step_eval r0 r1 q0 periodStep0
  have hs1 := step_eval r1 r2 q1 periodStep1
  have hs2 := step_eval r2 r3 q2 periodStep2
  have hs3 := step_eval r3 r4 q3 periodStep3
  have hs4 := step_eval r4 r5 q4 periodStep4
  have hs5 := step_eval r5 r6 q5 periodStep5
  have hp0 : (E conductor77PeriodPolynomial) ^ 0 = E r0 := by
    simp [r0]
  have power_step (n : ℕ) (a b : ℤ[X])
      (ha : (E conductor77PeriodPolynomial) ^ n = E a)
      (hab : E conductor77PeriodPolynomial * E a = E b) :
      (E conductor77PeriodPolynomial) ^ (n + 1) = E b := by
    calc
      (E conductor77PeriodPolynomial) ^ (n + 1) =
          (E conductor77PeriodPolynomial) ^ n * E conductor77PeriodPolynomial :=
        pow_succ _ _
      _ = E conductor77PeriodPolynomial * E a := by rw [ha, mul_comm]
      _ = E b := hab
  have hp1 := power_step 0 r0 r1 hp0 hs0
  have hp2 := power_step 1 r1 r2 hp1 hs1
  have hp3 := power_step 2 r2 r3 hp2 hs2
  have hp4 := power_step 3 r3 r4 hp3 hs3
  have hp5 := power_step 4 r4 r5 hp4 hs4
  have hp6 := power_step 5 r5 r6 hp5 hs5
  have hlin : -83 * E r0 - 106 * E r1 + 106 * E r2 +
      20 * E r3 - 20 * E r4 - E r5 + E r6 = 0 := by
    have h := congrArg E period_remainders_linear
    simpa only [map_add, map_sub, map_mul, map_neg, map_zero,
      map_ofNat, map_intCast] using h
  have hpower : -83 * (E conductor77PeriodPolynomial) ^ 0 -
      106 * (E conductor77PeriodPolynomial) ^ 1 +
      106 * (E conductor77PeriodPolynomial) ^ 2 +
      20 * (E conductor77PeriodPolynomial) ^ 3 -
      20 * (E conductor77PeriodPolynomial) ^ 4 -
      (E conductor77PeriodPolynomial) ^ 5 +
      (E conductor77PeriodPolynomial) ^ 6 = 0 := by
    rw [hp0, hp1, hp2, hp3, hp4, hp5, hp6]
    exact hlin
  change Polynomial.eval₂ (Int.castRingHom R) (E conductor77PeriodPolynomial)
      periodC77 = 0
  simp only [periodC77, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat] at *
  linear_combination hpower
end
end Biunimodular.F11
