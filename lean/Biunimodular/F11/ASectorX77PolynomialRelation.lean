/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorX77LinearRelation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-- The explicit conductor-77 expression is annihilated by the monic
A-coordinate polynomial. -/
theorem aSectorX77_G30_relation {R : Type*} [CommRing R]
    (z : R)
    (hz : eval₂ (Int.castRingHom R) z (cyclotomic 77 ℤ) = 0) :
    eval₂ (Int.castRingHom R)
      (eval₂ (Int.castRingHom R) z aSectorXPoly77) aSectorG30 = 0 := by
  let E : ℤ[X] →+* R := eval₂RingHom (Int.castRingHom R) z
  let t : R := E aSectorXRed
  have hphi : E phi77 = 0 := by
    change eval₂ (Int.castRingHom R) z phi77 = 0
    rw [phi77_eq_cyclotomic]
    exact hz
  have hxRed : E aSectorXPoly77 = t := by
    have h := congrArg E aSectorXPoly77_reduction
    simpa only [map_add, map_mul, hphi, zero_mul, zero_add, t] using h
  have hp0 : t ^ 0 = E aSectorXR0 := by simp [aSectorXR0]
  have hp1 : t ^ 1 = E aSectorXR1 := by simp [t, aSectorXR1]
  have power_step (n : ℕ) (a b : ℤ[X])
      (ha : t ^ n = E a)
      (hab : t * E a = E b) : t ^ (n + 1) = E b := by
    calc
      t ^ (n + 1) = t ^ n * t := pow_succ _ _
      _ = t * E a := by rw [ha, mul_comm]
      _ = E b := hab
  have hs1 : t * E aSectorXR1 = E aSectorXR2 := by
    have h := congrArg E aSectorXStep1
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp2 := power_step 1 aSectorXR1 aSectorXR2 hp1 hs1
  have hs2 : t * E aSectorXR2 = E aSectorXR3 := by
    have h := congrArg E aSectorXStep2
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp3 := power_step 2 aSectorXR2 aSectorXR3 hp2 hs2
  have hs3 : t * E aSectorXR3 = E aSectorXR4 := by
    have h := congrArg E aSectorXStep3
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp4 := power_step 3 aSectorXR3 aSectorXR4 hp3 hs3
  have hs4 : t * E aSectorXR4 = E aSectorXR5 := by
    have h := congrArg E aSectorXStep4
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp5 := power_step 4 aSectorXR4 aSectorXR5 hp4 hs4
  have hs5 : t * E aSectorXR5 = E aSectorXR6 := by
    have h := congrArg E aSectorXStep5
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp6 := power_step 5 aSectorXR5 aSectorXR6 hp5 hs5
  have hs6 : t * E aSectorXR6 = E aSectorXR7 := by
    have h := congrArg E aSectorXStep6
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp7 := power_step 6 aSectorXR6 aSectorXR7 hp6 hs6
  have hs7 : t * E aSectorXR7 = E aSectorXR8 := by
    have h := congrArg E aSectorXStep7
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp8 := power_step 7 aSectorXR7 aSectorXR8 hp7 hs7
  have hs8 : t * E aSectorXR8 = E aSectorXR9 := by
    have h := congrArg E aSectorXStep8
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp9 := power_step 8 aSectorXR8 aSectorXR9 hp8 hs8
  have hs9 : t * E aSectorXR9 = E aSectorXR10 := by
    have h := congrArg E aSectorXStep9
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp10 := power_step 9 aSectorXR9 aSectorXR10 hp9 hs9
  have hs10 : t * E aSectorXR10 = E aSectorXR11 := by
    have h := congrArg E aSectorXStep10
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp11 := power_step 10 aSectorXR10 aSectorXR11 hp10 hs10
  have hs11 : t * E aSectorXR11 = E aSectorXR12 := by
    have h := congrArg E aSectorXStep11
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp12 := power_step 11 aSectorXR11 aSectorXR12 hp11 hs11
  have hs12 : t * E aSectorXR12 = E aSectorXR13 := by
    have h := congrArg E aSectorXStep12
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp13 := power_step 12 aSectorXR12 aSectorXR13 hp12 hs12
  have hs13 : t * E aSectorXR13 = E aSectorXR14 := by
    have h := congrArg E aSectorXStep13
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp14 := power_step 13 aSectorXR13 aSectorXR14 hp13 hs13
  have hs14 : t * E aSectorXR14 = E aSectorXR15 := by
    have h := congrArg E aSectorXStep14
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp15 := power_step 14 aSectorXR14 aSectorXR15 hp14 hs14
  have hs15 : t * E aSectorXR15 = E aSectorXR16 := by
    have h := congrArg E aSectorXStep15
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp16 := power_step 15 aSectorXR15 aSectorXR16 hp15 hs15
  have hs16 : t * E aSectorXR16 = E aSectorXR17 := by
    have h := congrArg E aSectorXStep16
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp17 := power_step 16 aSectorXR16 aSectorXR17 hp16 hs16
  have hs17 : t * E aSectorXR17 = E aSectorXR18 := by
    have h := congrArg E aSectorXStep17
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp18 := power_step 17 aSectorXR17 aSectorXR18 hp17 hs17
  have hs18 : t * E aSectorXR18 = E aSectorXR19 := by
    have h := congrArg E aSectorXStep18
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp19 := power_step 18 aSectorXR18 aSectorXR19 hp18 hs18
  have hs19 : t * E aSectorXR19 = E aSectorXR20 := by
    have h := congrArg E aSectorXStep19
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp20 := power_step 19 aSectorXR19 aSectorXR20 hp19 hs19
  have hs20 : t * E aSectorXR20 = E aSectorXR21 := by
    have h := congrArg E aSectorXStep20
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp21 := power_step 20 aSectorXR20 aSectorXR21 hp20 hs20
  have hs21 : t * E aSectorXR21 = E aSectorXR22 := by
    have h := congrArg E aSectorXStep21
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp22 := power_step 21 aSectorXR21 aSectorXR22 hp21 hs21
  have hs22 : t * E aSectorXR22 = E aSectorXR23 := by
    have h := congrArg E aSectorXStep22
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp23 := power_step 22 aSectorXR22 aSectorXR23 hp22 hs22
  have hs23 : t * E aSectorXR23 = E aSectorXR24 := by
    have h := congrArg E aSectorXStep23
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp24 := power_step 23 aSectorXR23 aSectorXR24 hp23 hs23
  have hs24 : t * E aSectorXR24 = E aSectorXR25 := by
    have h := congrArg E aSectorXStep24
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp25 := power_step 24 aSectorXR24 aSectorXR25 hp24 hs24
  have hs25 : t * E aSectorXR25 = E aSectorXR26 := by
    have h := congrArg E aSectorXStep25
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp26 := power_step 25 aSectorXR25 aSectorXR26 hp25 hs25
  have hs26 : t * E aSectorXR26 = E aSectorXR27 := by
    have h := congrArg E aSectorXStep26
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp27 := power_step 26 aSectorXR26 aSectorXR27 hp26 hs26
  have hs27 : t * E aSectorXR27 = E aSectorXR28 := by
    have h := congrArg E aSectorXStep27
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp28 := power_step 27 aSectorXR27 aSectorXR28 hp27 hs27
  have hs28 : t * E aSectorXR28 = E aSectorXR29 := by
    have h := congrArg E aSectorXStep28
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp29 := power_step 28 aSectorXR28 aSectorXR29 hp28 hs28
  have hs29 : t * E aSectorXR29 = E aSectorXR30 := by
    have h := congrArg E aSectorXStep29
    simpa only [map_mul, map_add, hphi, zero_mul, zero_add, t] using h
  have hp30 := power_step 29 aSectorXR29 aSectorXR30 hp29 hs29
  have hlinEval :
      -456153866030714364121126903 * E aSectorXR0
      - 32954219911505547835456793594 * E aSectorXR1
      + 83528158299559974015947521205 * E aSectorXR2
      + 1316315013975085942280916680381 * E aSectorXR3
      - 5828394446256998667721626184074 * E aSectorXR4
      - 3840698481089467590597304360291 * E aSectorXR5
      + 68266611991062799243367417279916 * E aSectorXR6
      - 157299625302500222981526337520193 * E aSectorXR7
      + 119291494077820597119400618426622 * E aSectorXR8
      + 89714624882821009072497623516389 * E aSectorXR9
      - 252755680873644008457161163519505 * E aSectorXR10
      + 199314066267368103535534738244249 * E aSectorXR11
      - 43617079462286217767567738891071 * E aSectorXR12
      - 40161170956744531780094443253511 * E aSectorXR13
      + 36316559791548833974912728696164 * E aSectorXR14
      - 12138569497725711799922058991018 * E aSectorXR15
      + 977562455936223920891761501484 * E aSectorXR16
      + 626515722982729950680870481999 * E aSectorXR17
      - 233393128793190084245498290704 * E aSectorXR18
      + 32180113517667895948142129386 * E aSectorXR19
      - 942383865956941122285175220 * E aSectorXR20
      - 197888708481008060437814431 * E aSectorXR21
      + 12857530584069173836477721 * E aSectorXR22
      + 322210699153065066313739 * E aSectorXR23
      + 2159659762203647843370 * E aSectorXR24
      + 4329785713916463185 * E aSectorXR25
      + 3709595988698677 * E aSectorXR26
      + 1513968321019 * E aSectorXR27
      + 306613923 * E aSectorXR28
      + 29106 * E aSectorXR29
      + E aSectorXR30 = 0 := by
    have h := congrArg E aSectorX77_linear_relation
    simpa only [map_add, map_sub, map_mul, map_neg, map_zero,
      map_ofNat, map_intCast] using h
  have hpower :
      -456153866030714364121126903 * t ^ 0
      - 32954219911505547835456793594 * t ^ 1
      + 83528158299559974015947521205 * t ^ 2
      + 1316315013975085942280916680381 * t ^ 3
      - 5828394446256998667721626184074 * t ^ 4
      - 3840698481089467590597304360291 * t ^ 5
      + 68266611991062799243367417279916 * t ^ 6
      - 157299625302500222981526337520193 * t ^ 7
      + 119291494077820597119400618426622 * t ^ 8
      + 89714624882821009072497623516389 * t ^ 9
      - 252755680873644008457161163519505 * t ^ 10
      + 199314066267368103535534738244249 * t ^ 11
      - 43617079462286217767567738891071 * t ^ 12
      - 40161170956744531780094443253511 * t ^ 13
      + 36316559791548833974912728696164 * t ^ 14
      - 12138569497725711799922058991018 * t ^ 15
      + 977562455936223920891761501484 * t ^ 16
      + 626515722982729950680870481999 * t ^ 17
      - 233393128793190084245498290704 * t ^ 18
      + 32180113517667895948142129386 * t ^ 19
      - 942383865956941122285175220 * t ^ 20
      - 197888708481008060437814431 * t ^ 21
      + 12857530584069173836477721 * t ^ 22
      + 322210699153065066313739 * t ^ 23
      + 2159659762203647843370 * t ^ 24
      + 4329785713916463185 * t ^ 25
      + 3709595988698677 * t ^ 26
      + 1513968321019 * t ^ 27
      + 306613923 * t ^ 28
      + 29106 * t ^ 29
      + t ^ 30 = 0 := by
    rw [hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28, hp29, hp30]
    exact hlinEval
  have hG : eval₂ (Int.castRingHom R) t aSectorG30 = 0 := by
    simp only [aSectorG30, eval₂_add, eval₂_sub, eval₂_mul,
      eval₂_pow, eval₂_X, eval₂_ofNat, eval₂_neg]
    linear_combination hpower
  change eval₂ (Int.castRingHom R) (E aSectorXPoly77) aSectorG30 = 0
  rw [hxRed]
  exact hG

end
end Biunimodular.F11
