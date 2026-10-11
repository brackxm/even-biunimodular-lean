/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodRealization

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11
open Polynomial
noncomputable section

/-- The six Gaussian periods as reduced exponent polynomials. -/
def conductor77PeriodOrbitPolynomials : List ℤ[X] :=
  [
    (1) * X + (1) * X^6 + (1) * X^13 + (1) * X^15 + (1) * X^36 + (1) * X^41 + (1) * X^62 + (1) * X^64 + (1) * X^71 + (1) * X^76,
    (1) * X^3 + (1) * X^18 + (1) * X^31 + (1) * X^32 + (1) * X^38 + (1) * X^39 + (1) * X^45 + (1) * X^46 + (1) * X^59 + (1) * X^74,
    (1) * X^9 + (1) * X^16 + (1) * X^19 + (1) * X^23 + (1) * X^37 + (1) * X^40 + (1) * X^54 + (1) * X^58 + (1) * X^61 + (1) * X^68,
    (1) * X^8 + (1) * X^20 + (1) * X^27 + (1) * X^29 + (1) * X^34 + (1) * X^43 + (1) * X^48 + (1) * X^50 + (1) * X^57 + (1) * X^69,
    (1) * X^4 + (1) * X^10 + (1) * X^17 + (1) * X^24 + (1) * X^25 + (1) * X^52 + (1) * X^53 + (1) * X^60 + (1) * X^67 + (1) * X^73,
    (1) * X^2 + (1) * X^5 + (1) * X^12 + (1) * X^26 + (1) * X^30 + (1) * X^47 + (1) * X^51 + (1) * X^65 + (1) * X^72 + (1) * X^75]

private def conductor77PeriodPairQuotients : List ℤ[X] :=
  [
    (1) * X + (1) * X^2 + (1) * X^3 + (1) * X^4 + (1) * X^5 + (2) * X^6 + (2) * X^7 + (2) * X^8 + (2) * X^9 + (2) * X^10 + (2) * X^11 + (1) * X^12 + (1) * X^13 + (1) * X^14 + (1) * X^15 + (1) * X^16,
    (1) * X^3 + (2) * X^4 + (2) * X^5 + (2) * X^6 + (2) * X^7 + (2) * X^8 + (2) * X^9 + (2) * X^10 + (2) * X^11 + (2) * X^12 + (2) * X^13 + (1) * X^14,
    (1) * X^2 + (1) * X^3 + (1) * X^4 + (2) * X^5 + (2) * X^6 + (2) * X^7 + (2) * X^8 + (2) * X^9 + (2) * X^10 + (2) * X^11 + (2) * X^12 + (1) * X^13 + (1) * X^14 + (1) * X^15,
    (1) * X + (1) * X^2 + (1) * X^3 + (1) * X^4 + (1) * X^5 + (2) * X^6 + (2) * X^7 + (2) * X^8 + (2) * X^9 + (2) * X^10 + (2) * X^11 + (1) * X^12 + (1) * X^13 + (1) * X^14 + (1) * X^15 + (1) * X^16,
    (1) * X^3 + (2) * X^4 + (2) * X^5 + (2) * X^6 + (2) * X^7 + (2) * X^8 + (2) * X^9 + (2) * X^10 + (2) * X^11 + (2) * X^12 + (2) * X^13 + (1) * X^14,
    (1) * X^2 + (1) * X^3 + (1) * X^4 + (2) * X^5 + (2) * X^6 + (2) * X^7 + (2) * X^8 + (2) * X^9 + (2) * X^10 + (2) * X^11 + (2) * X^12 + (1) * X^13 + (1) * X^14 + (1) * X^15]

/-- Exact certificates for the cubic-period pair identities. -/
theorem conductor77PeriodPair_polynomial_identity (m : Fin 6) :
    conductor77PeriodOrbitPolynomials[m.1]! +
      conductor77PeriodOrbitPolynomials[(m.1 + 3) % 6]! +
      X ^ ((22 * 3 ^ m.1) % 77) + X ^ ((77 - (22 * 3 ^ m.1) % 77) % 77) =
      phi77 * conductor77PeriodPairQuotients[m.1]! := by
  fin_cases m <;> norm_num [conductor77PeriodOrbitPolynomials,
    conductor77PeriodPairQuotients, phi77] <;> ring

def conductor77QuadraticPeriodPolynomial : ℤ[X] :=
  2 * (conductor77PeriodOrbitPolynomials[0]! + conductor77PeriodOrbitPolynomials[2]! +
    conductor77PeriodOrbitPolynomials[4]!) - 1

private def conductor77QuadraticPeriodQuotient : ℤ[X] :=
  (-76) + (-80) * X + (-76) * X^2 + (-76) * X^3 + (-80) * X^4 + (-72) * X^5 + (-76) * X^6 + (8) * X^7 + (16) * X^8 + (8) * X^9 + (20) * X^10 + (108) * X^11 + (108) * X^12 + (112) * X^13 + (120) * X^14 + (124) * X^15 + (132) * X^16 + (136) * X^17 + (56) * X^18 + (64) * X^19 + (88) * X^20 + (76) * X^21 + (76) * X^22 + (88) * X^23 + (80) * X^24 + (88) * X^25 + (96) * X^26 + (76) * X^27 + (84) * X^28 + (96) * X^29 + (80) * X^30 + (68) * X^31 + (68) * X^32 + (52) * X^33 + (56) * X^34 + (48) * X^35 + (12) * X^36 + (-4) * X^37 + (12) * X^38 + (-8) * X^39 + (-20) * X^40 + (-20) * X^41 + (-8) * X^42 + (-4) * X^43 + (4) * X^44 + (-20) * X^45 + (16) * X^47 + (8) * X^48 + (-12) * X^49 + (12) * X^50 + (8) * X^51 + (4) * X^52 + (-12) * X^53 + (-20) * X^54 + (-12) * X^55 + (8) * X^56 + (-8) * X^57 + (36) * X^59 + (44) * X^60 + (40) * X^61 + (52) * X^62 + (56) * X^63 + (68) * X^64 + (92) * X^65 + (80) * X^66 + (72) * X^67 + (92) * X^68 + (92) * X^69 + (80) * X^70 + (88) * X^71 + (76) * X^72 + (76) * X^73 + (92) * X^74 + (76) * X^75 + (60) * X^76 + (64) * X^77 + (64) * X^78 + (56) * X^79 + (52) * X^80 + (44) * X^81 + (40) * X^82 + (44) * X^83 + (36) * X^84 + (20) * X^85 + (24) * X^86 + (20) * X^87 + (12) * X^88 + (12) * X^89 + (4) * X^90 + (4) * X^91 + (4) * X^92

/-- The quadratic period difference squares to 77 in the cyclotomic field. -/
theorem conductor77QuadraticPeriod_polynomial_identity :
    conductor77QuadraticPeriodPolynomial ^ 2 - 77 =
      phi77 * conductor77QuadraticPeriodQuotient := by
  simp only [conductor77QuadraticPeriodPolynomial, conductor77PeriodOrbitPolynomials,
    conductor77QuadraticPeriodQuotient, phi77]
  norm_num
  ring

private def conductor77CubicPeriodQuotient : ℤ[X] :=
  (1) + (-1) * X + (-2) * X^2 + (-1) * X^3 + (-1) * X^4 + (-1) * X^5 + (-3) * X^6 + (-6) * X^7 + (-3) * X^8 + (-4) * X^9 + (-2) * X^10 + (-3) * X^11 + (-2) * X^12 + (2) * X^13 + (-1) * X^14 + (5) * X^15 + (4) * X^16 + (9) * X^17 + (13) * X^18 + (9) * X^19 + (16) * X^20 + (12) * X^21 + (23) * X^22 + (25) * X^23 + (23) * X^24 + (27) * X^25 + (20) * X^26 + (30) * X^27 + (27) * X^28 + (30) * X^29 + (30) * X^30 + (26) * X^31 + (31) * X^32 + (19) * X^33 + (27) * X^34 + (24) * X^35 + (31) * X^36 + (31) * X^37 + (25) * X^38 + (29) * X^39 + (24) * X^40 + (37) * X^41 + (33) * X^42 + (42) * X^43 + (41) * X^44 + (39) * X^45 + (46) * X^46 + (36) * X^47 + (52) * X^48 + (47) * X^49 + (61) * X^50 + (62) * X^51 + (55) * X^52 + (63) * X^53 + (50) * X^54 + (72) * X^55 + (65) * X^56 + (75) * X^57 + (75) * X^58 + (66) * X^59 + (75) * X^60 + (58) * X^61 + (71) * X^62 + (64) * X^63 + (76) * X^64 + (76) * X^65 + (62) * X^66 + (67) * X^67 + (51) * X^68 + (70) * X^69 + (62) * X^70 + (76) * X^71 + (74) * X^72 + (70) * X^73 + (78) * X^74 + (59) * X^75 + (81) * X^76 + (72) * X^77 + (97) * X^78 + (98) * X^79 + (87) * X^80 + (96) * X^81 + (74) * X^82 + (105) * X^83 + (97) * X^84 + (112) * X^85 + (113) * X^86 + (98) * X^87 + (109) * X^88 + (79) * X^89 + (100) * X^90 + (93) * X^91 + (104) * X^92 + (105) * X^93 + (80) * X^94 + (86) * X^95 + (65) * X^96 + (83) * X^97 + (77) * X^98 + (83) * X^99 + (83) * X^100 + (69) * X^101 + (75) * X^102 + (57) * X^103 + (72) * X^104 + (67) * X^105 + (79) * X^106 + (79) * X^107 + (67) * X^108 + (72) * X^109 + (57) * X^110 + (75) * X^111 + (68) * X^112 + (77) * X^113 + (77) * X^114 + (67) * X^115 + (74) * X^116 + (56) * X^117 + (68) * X^118 + (62) * X^119 + (69) * X^120 + (69) * X^121 + (55) * X^122 + (58) * X^123 + (43) * X^124 + (52) * X^125 + (47) * X^126 + (49) * X^127 + (49) * X^128 + (40) * X^129 + (42) * X^130 + (30) * X^131 + (36) * X^132 + (32) * X^133 + (38) * X^134 + (38) * X^135 + (31) * X^136 + (32) * X^137 + (23) * X^138 + (32) * X^139 + (29) * X^140 + (33) * X^141 + (33) * X^142 + (28) * X^143 + (31) * X^144 + (22) * X^145 + (28) * X^146 + (26) * X^147 + (28) * X^148 + (28) * X^149 + (19) * X^150 + (21) * X^151 + (15) * X^152 + (18) * X^153 + (17) * X^154 + (14) * X^155 + (14) * X^156 + (8) * X^157 + (9) * X^158 + (6) * X^159 + (6) * X^160 + (6) * X^161 + (4) * X^162 + (4) * X^163 + (1) * X^164 + (1) * X^165 + (1) * X^166 + (1) * X^167 + (1) * X^168

/-- The period pair generates a root of the real conductor-7 cubic. -/
theorem conductor77CubicPeriod_polynomial_identity :
    let b := conductor77PeriodOrbitPolynomials[0]! + conductor77PeriodOrbitPolynomials[3]!
    b ^ 3 - b ^ 2 - 2 * b + 1 = phi77 * conductor77CubicPeriodQuotient := by
  simp only [conductor77PeriodOrbitPolynomials, conductor77CubicPeriodQuotient, phi77]
  norm_num
  ring

/-- One of the six Gaussian periods, evaluated in a cyclotomic algebra. -/
def conductor77PeriodOrbitValue {R : Type*} [CommRing R] (z : R) (m : Fin 6) : R :=
  Polynomial.eval₂ (Int.castRingHom R) z conductor77PeriodOrbitPolynomials[m.1]!

private def conductor77PeriodSumQuotient : ℤ[X] :=
  -1 + X^2 + 2*X^3 + 3*X^4 + 4*X^5 + 5*X^6 + 6*X^7 + 6*X^8 +
    6*X^9 + 6*X^10 + 6*X^11 + 5*X^12 + 4*X^13 + 3*X^14 + 2*X^15 + X^16

/-- The six period cosets have total sum one modulo the conductor-77 relation. -/
theorem conductor77PeriodSum_polynomial_identity :
    conductor77PeriodOrbitPolynomials[0]! + conductor77PeriodOrbitPolynomials[1]! +
      conductor77PeriodOrbitPolynomials[2]! + conductor77PeriodOrbitPolynomials[3]! +
      conductor77PeriodOrbitPolynomials[4]! + conductor77PeriodOrbitPolynomials[5]! - 1 =
      phi77 * conductor77PeriodSumQuotient := by
  simp only [conductor77PeriodOrbitPolynomials, conductor77PeriodSumQuotient, phi77]
  norm_num
  ring

/-- The sum of all six evaluated Gaussian periods is one. -/
theorem conductor77PeriodSum_identity {R : Type*} [CommRing R]
    (z : R) (hz : Polynomial.eval₂ (Int.castRingHom R) z (cyclotomic 77 ℤ) = 0) :
    conductor77PeriodOrbitValue z 0 + conductor77PeriodOrbitValue z 1 +
      conductor77PeriodOrbitValue z 2 + conductor77PeriodOrbitValue z 3 +
      conductor77PeriodOrbitValue z 4 + conductor77PeriodOrbitValue z 5 = 1 := by
  let E := Polynomial.eval₂RingHom (Int.castRingHom R) z
  have hphi : E phi77 = 0 := by
    change Polynomial.eval₂ (Int.castRingHom R) z phi77 = 0
    rw [phi77_eq_cyclotomic]
    exact hz
  have h := congrArg E conductor77PeriodSum_polynomial_identity
  simp only [map_sub, map_add, map_one, map_mul, hphi, zero_mul] at h
  apply sub_eq_zero.mp
  simpa [E, conductor77PeriodOrbitValue] using h

/-- The period pair is the negative of the corresponding real conductor-7
cyclotomic coordinate. -/
theorem conductor77PeriodPair_identity {R : Type*} [CommRing R]
    (z : R) (hz : Polynomial.eval₂ (Int.castRingHom R) z (cyclotomic 77 ℤ) = 0)
    (m : Fin 6) :
    conductor77PeriodOrbitValue z m +
      conductor77PeriodOrbitValue z ⟨(m.1 + 3) % 6, Nat.mod_lt _ (by decide)⟩ =
      -(z ^ ((22 * 3 ^ m.1) % 77) + z ^ ((77 - (22 * 3 ^ m.1) % 77) % 77)) := by
  let E := Polynomial.eval₂RingHom (Int.castRingHom R) z
  have hphi : E phi77 = 0 := by
    change Polynomial.eval₂ (Int.castRingHom R) z phi77 = 0
    rw [phi77_eq_cyclotomic]
    exact hz
  have h := congrArg E (conductor77PeriodPair_polynomial_identity m)
  simp only [map_add, map_mul, map_pow, hphi, zero_mul] at h
  have hvalue : conductor77PeriodOrbitValue z m +
      conductor77PeriodOrbitValue z ⟨(m.1 + 3) % 6, Nat.mod_lt _ (by decide)⟩ +
      z ^ ((22 * 3 ^ m.1) % 77) + z ^ ((77 - (22 * 3 ^ m.1) % 77) % 77) = 0 := by
    simpa [E, conductor77PeriodOrbitValue] using h
  linear_combination hvalue

/-- The difference of the even and odd period halves is a square root of 77. -/
theorem conductor77QuadraticPeriod_square {R : Type*} [CommRing R]
    (z : R) (hz : Polynomial.eval₂ (Int.castRingHom R) z (cyclotomic 77 ℤ) = 0) :
    (2 * (conductor77PeriodOrbitValue z 0 + conductor77PeriodOrbitValue z 2 +
      conductor77PeriodOrbitValue z 4) - 1) ^ 2 = 77 := by
  let E := Polynomial.eval₂RingHom (Int.castRingHom R) z
  have hphi : E phi77 = 0 := by
    change Polynomial.eval₂ (Int.castRingHom R) z phi77 = 0
    rw [phi77_eq_cyclotomic]
    exact hz
  have h := congrArg E conductor77QuadraticPeriod_polynomial_identity
  simp only [map_sub, map_pow, map_ofNat, map_mul, hphi, zero_mul] at h
  apply sub_eq_zero.mp
  simpa [E, conductor77QuadraticPeriodPolynomial, conductor77PeriodOrbitValue] using h

/-- The sum of opposite periods satisfies the real conductor-7 cubic. -/
theorem conductor77CubicPeriod_relation {R : Type*} [CommRing R]
    (z : R) (hz : Polynomial.eval₂ (Int.castRingHom R) z (cyclotomic 77 ℤ) = 0) :
    let b := conductor77PeriodOrbitValue z 0 + conductor77PeriodOrbitValue z 3
    b ^ 3 - b ^ 2 - 2 * b + 1 = 0 := by
  let E := Polynomial.eval₂RingHom (Int.castRingHom R) z
  have hphi : E phi77 = 0 := by
    change Polynomial.eval₂ (Int.castRingHom R) z phi77 = 0
    rw [phi77_eq_cyclotomic]
    exact hz
  have h := congrArg E conductor77CubicPeriod_polynomial_identity
  simp only [map_sub, map_add, map_pow, map_mul, map_one, map_ofNat,
    hphi, zero_mul] at h
  simpa [E, conductor77PeriodOrbitValue] using h

end
end Biunimodular.F11
