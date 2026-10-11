/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.IntervalCases
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.NormDet
import Biunimodular.F11.InvariantPolynomialData
import Biunimodular.F11.InvariantFiniteFieldIrreducibility
import Biunimodular.F11.FiniteFieldIrreducibilityCriterion

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-!
# Exact modular certificates for the B-sector Frobenius cycle types

The certificates below replay binary modular exponentiation through explicit
low-degree remainder identities.
No checked identity has the huge degree of `r^37` or `r^211`.
-/

private theorem dvd_square_remainder_next
    {R : Type*} [CommRing R] {f r a b : R} {e : ℕ}
    (hprev : f ∣ r ^ e - a)
    (hred : f ∣ a ^ 2 - b) :
    f ∣ r ^ (e * 2) - b := by
  rcases hprev with ⟨q, hq⟩
  rcases hred with ⟨t, ht⟩
  refine ⟨q * (r ^ e + a) + t, ?_⟩
  rw [pow_mul]
  linear_combination (r ^ e + a) * hq + ht

private theorem dvd_mul_remainder_next
    {R : Type*} [CommRing R] {f r a b c : R} {e d : ℕ}
    (ha : f ∣ r ^ e - a)
    (hb : f ∣ r ^ d - b)
    (hred : f ∣ a * b - c) :
    f ∣ r ^ (e + d) - c := by
  rcases ha with ⟨qa, hqa⟩
  rcases hb with ⟨qb, hqb⟩
  rcases hred with ⟨qc, hqc⟩
  refine ⟨qa * r ^ d + a * qb + qc, ?_⟩
  rw [pow_add]
  linear_combination (r ^ d) * hqa + a * hqb + hqc

private theorem dvd_comp_sub_comp
    {R : Type*} [CommRing R] {f a b : R[X]} (r : R[X])
    (h : f ∣ a - b) : f ∣ r.comp a - r.comp b := by
  apply h.trans
  simpa [Polynomial.comp, Polynomial.eval_map] using
    (Polynomial.sub_dvd_eval_sub a b (r.map C))

private theorem zmod_pow_eq_comp (p : ℕ) [Fact p.Prime]
    (r : (ZMod p)[X]) : r ^ p = r.comp (X ^ p) := by
  rw [← Polynomial.map_frobenius_expand p, Polynomial.expand_eq_comp_X_pow]
  ext n
  simp

private theorem dvd_frobenius_remainder_next
    {p : ℕ} [Fact p.Prime] {f a r s : (ZMod p)[X]}
    (hbase : f ∣ X ^ p - a)
    (hsmall : f ∣ r.comp a - s) :
    f ∣ r ^ p - s := by
  rw [zmod_pow_eq_comp]
  convert dvd_add (dvd_comp_sub_comp r hbase) hsmall using 1
  all_goals ring

private theorem irreducible_of_frobenius_iter_certificate_B
    {p n : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
    (hfmonic : f.Monic)
    (hdeg : f.natDegree = n)
    (hn : 0 < n)
    (hfull : f ∣ frobeniusIter p n - X)
    (hproper : ∀ d : ℕ, d ∣ n → 0 < d → d < n →
      IsCoprime f (X ^ p ^ d - X)) :
    Irreducible f := by
  apply irreducible_of_frobenius_certificate
      (p := p) (n := n) (f := f)
  · exact hfmonic
  · exact hdeg
  · exact hn
  · rw [← frobeniusIter_eq_X_pow p n]
    exact hfull
  · exact hproper

def B37lin : (ZMod 37)[X] := X + 11

def B37seven : (ZMod 37)[X] :=
  X^7 + 16*X^6 + 9*X^5 + 33*X^4 + 14*X^3 + 25*X^2 + 8*X + 21

theorem invariantB_mod37_factor :
    invariantB.map (Int.castRingHom (ZMod 37)) = 10 * B37lin * B37seven := by
  norm_num [invariantB, B37lin, B37seven]
  all_goals reduce_mod_char
  all_goals ring_nf
  all_goals reduce_mod_char

def B37r1 : (ZMod 37)[X] :=
  18 * X ^ 6 - 8 * X ^ 5 - 5 * X ^ 4 - 18 * X ^ 3 + 9 * X ^ 2 + 3 * X + 9

def B37r2 : (ZMod 37)[X] :=
  - 5 * X ^ 6 - 5 * X ^ 5 + 4 * X ^ 4 - X ^ 3 + 7 * X ^ 2 - 3 * X - 8

def B37r3 : (ZMod 37)[X] :=
  5 * X ^ 6 + 6 * X ^ 5 - 4 * X ^ 4 - 9 * X ^ 3 + 13 * X ^ 2 - 5 * X + 8

def B37r4 : (ZMod 37)[X] :=
  12 * X ^ 6 + 13 * X ^ 4 + 11 * X ^ 3 + 17 * X ^ 2 + 8 * X + 10

def B37r5 : (ZMod 37)[X] :=
  - 6 * X ^ 6 + 17 * X ^ 5 - 9 * X ^ 4 + 8 * X ^ 3 + 2 * X ^ 2 - 7 * X + 7

def B37r6 : (ZMod 37)[X] :=
  13 * X ^ 6 - 10 * X ^ 5 + X ^ 4 + 9 * X ^ 3 - 11 * X ^ 2 + 3 * X - 5

def B37r7 : (ZMod 37)[X] :=
  X

theorem B37seven_frob_step1 : B37seven ∣ X ^ 37 - B37r1 := by
  have h1 : B37seven ∣ X ^ 1 - X := by simp
  let s2 : (ZMod 37)[X] := X ^ 2
  let q2 : (ZMod 37)[X] := 0
  have hred2 : B37seven ∣ X ^ 2 - s2 := by
    refine ⟨q2, ?_⟩
    simp only [s2, q2, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h2 : B37seven ∣ X ^ 2 - s2 :=
    dvd_square_remainder_next (e := 1) h1 hred2
  let s4 : (ZMod 37)[X] := X ^ 4
  let q4 : (ZMod 37)[X] := 0
  have hred4 : B37seven ∣ s2 ^ 2 - s4 := by
    refine ⟨q4, ?_⟩
    simp only [s4, q4, s2, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4 : B37seven ∣ X ^ 4 - s4 :=
    dvd_square_remainder_next (e := 2) h2 hred4
  let s8 : (ZMod 37)[X] := - 12 * X ^ 6 - 4 * X ^ 4 + 14 * X ^ 3 - 15 * X ^ 2 - 4 * X + 3
  let q8 : (ZMod 37)[X] := X - 16
  have hred8 : B37seven ∣ s4 ^ 2 - s8 := by
    refine ⟨q8, ?_⟩
    simp only [s8, q8, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h8 : B37seven ∣ X ^ 8 - s8 :=
    dvd_square_remainder_next (e := 4) h4 hred8
  let s16 : (ZMod 37)[X] := - 18 * X ^ 6 - 18 * X ^ 5 + 4 * X ^ 4 + 10 * X ^ 3 - 2 * X ^ 2 + 12 * X + 13
  let q16 : (ZMod 37)[X] := - 4 * X ^ 5 - 10 * X ^ 4 - 4 * X ^ 3 - 13 * X ^ 2 + 7 * X - 9
  have hred16 : B37seven ∣ s8 ^ 2 - s16 := by
    refine ⟨q16, ?_⟩
    simp only [s16, q16, s8, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h16 : B37seven ∣ X ^ 16 - s16 :=
    dvd_square_remainder_next (e := 8) h8 hred16
  let s32 : (ZMod 37)[X] := - 6 * X ^ 5 - 17 * X ^ 4 - 14 * X ^ 3 + 10 * X ^ 2 + 7 * X + 10
  let q32 : (ZMod 37)[X] := - 9 * X ^ 5 + 15 * X ^ 4 - 16 * X ^ 3 - 12 * X ^ 2 - 9 * X - 3
  have hred32 : B37seven ∣ s16 ^ 2 - s32 := by
    refine ⟨q32, ?_⟩
    simp only [s32, q32, s16, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h32 : B37seven ∣ X ^ 32 - s32 :=
    dvd_square_remainder_next (e := 16) h16 hred32
  let s36 : (ZMod 37)[X] := - 11 * X ^ 6 - 10 * X ^ 5 + 4 * X ^ 4 + 2 * X ^ 3 + 13 * X ^ 2 - 7 * X - 11
  let q36 : (ZMod 37)[X] := - 6 * X ^ 2 + 5 * X - 3
  have hred36 : B37seven ∣ s32 * s4 - s36 := by
    refine ⟨q36, ?_⟩
    simp only [s36, q36, s4, s32, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h36 : B37seven ∣ X ^ 36 - s36 :=
    dvd_mul_remainder_next (e := 32) (d := 4) h32 h4 hred36
  let s37 : (ZMod 37)[X] := 18 * X ^ 6 - 8 * X ^ 5 - 5 * X ^ 4 - 18 * X ^ 3 + 9 * X ^ 2 + 3 * X + 9
  let q37 : (ZMod 37)[X] := - 11
  have hred37 : B37seven ∣ s36 * X - s37 := by
    refine ⟨q37, ?_⟩
    simp only [s37, q37, s36, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h37 : B37seven ∣ X ^ 37 - s37 :=
    dvd_mul_remainder_next (e := 36) (d := 1) h36 h1 hred37
  simpa [s37, B37r1] using h37

theorem B37seven_frob_step2 : B37seven ∣ B37r1 ^ 37 - B37r2 := by
  have h1 : B37seven ∣ B37r1 ^ 1 - B37r1 := by simp
  let s2 : (ZMod 37)[X] := 13 * X ^ 6 + 10 * X ^ 5 - 9 * X ^ 3 - 12 * X ^ 2 - 11 * X + 4
  let q2 : (ZMod 37)[X] := - 9 * X ^ 5 + 4 * X ^ 4 + 12 * X ^ 3 - 18 * X ^ 2 - 3 * X + 16
  have hred2 : B37seven ∣ B37r1 ^ 2 - s2 := by
    refine ⟨q2, ?_⟩
    simp only [s2, q2, B37seven, B37r1]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h2 : B37seven ∣ B37r1 ^ 2 - s2 :=
    dvd_square_remainder_next (e := 1) h1 hred2
  let s4 : (ZMod 37)[X] := 4 * X ^ 6 - 9 * X ^ 5 + 3 * X ^ 4 - X ^ 3 - 5 * X ^ 2 - 18 * X + 4
  let q4 : (ZMod 37)[X] := - 16 * X ^ 5 - 2 * X ^ 4 + 17 * X ^ 3 + 3 * X ^ 2 + 4 * X - 10
  have hred4 : B37seven ∣ s2 ^ 2 - s4 := by
    refine ⟨q4, ?_⟩
    simp only [s4, q4, s2, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4 : B37seven ∣ B37r1 ^ 4 - s4 :=
    dvd_square_remainder_next (e := 2) h2 hred4
  let s8 : (ZMod 37)[X] := 6 * X ^ 6 + 10 * X ^ 5 + 17 * X ^ 3 + 7 * X ^ 2 - 10 * X - 16
  let q8 : (ZMod 37)[X] := 16 * X ^ 5 + 5 * X ^ 4 - 8 * X ^ 3 + 11 * X ^ 2 + 12 * X - 2
  have hred8 : B37seven ∣ s4 ^ 2 - s8 := by
    refine ⟨q8, ?_⟩
    simp only [s8, q8, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h8 : B37seven ∣ B37r1 ^ 8 - s8 :=
    dvd_square_remainder_next (e := 4) h4 hred8
  let s16 : (ZMod 37)[X] := 5 * X ^ 6 - 9 * X ^ 5 + 9 * X ^ 4 - 5 * X ^ 3 + 13 * X ^ 2 + X - 18
  let q16 : (ZMod 37)[X] := - X ^ 5 - 12 * X ^ 4 + 5 * X ^ 3 + 6 * X ^ 2 - 10 * X + 6
  have hred16 : B37seven ∣ s8 ^ 2 - s16 := by
    refine ⟨q16, ?_⟩
    simp only [s16, q16, s8, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h16 : B37seven ∣ B37r1 ^ 16 - s16 :=
    dvd_square_remainder_next (e := 8) h8 hred16
  let s32 : (ZMod 37)[X] := 5 * X ^ 6 + 6 * X ^ 5 - 11 * X ^ 4 + 17 * X ^ 3 + 11 * X ^ 2 - 7 * X - 15
  let q32 : (ZMod 37)[X] := - 12 * X ^ 5 - 9 * X ^ 4 + 16 * X ^ 3 + 9 * X ^ 2 - 3 * X - 5
  have hred32 : B37seven ∣ s16 ^ 2 - s32 := by
    refine ⟨q32, ?_⟩
    simp only [s32, q32, s16, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h32 : B37seven ∣ B37r1 ^ 32 - s32 :=
    dvd_square_remainder_next (e := 16) h16 hred32
  let s36 : (ZMod 37)[X] := - 8 * X ^ 6 + 13 * X ^ 5 - 16 * X ^ 4 - 16 * X ^ 3 - 11 * X ^ 2 + 2 * X - 7
  let q36 : (ZMod 37)[X] := - 17 * X ^ 5 - 8 * X ^ 4 + 13 * X ^ 3 + 13 * X ^ 2 + 4 * X + 1
  have hred36 : B37seven ∣ s32 * s4 - s36 := by
    refine ⟨q36, ?_⟩
    simp only [s36, q36, s32, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h36 : B37seven ∣ B37r1 ^ 36 - s36 :=
    dvd_mul_remainder_next (e := 32) (d := 4) h32 h4 hred36
  let s37 : (ZMod 37)[X] := - 5 * X ^ 6 - 5 * X ^ 5 + 4 * X ^ 4 - X ^ 3 + 7 * X ^ 2 - 3 * X - 8
  let q37 : (ZMod 37)[X] := 4 * X ^ 5 + 12 * X ^ 4 + 12 * X ^ 3 + 5 * X ^ 2 - 11 * X + 15
  have hred37 : B37seven ∣ s36 * B37r1 - s37 := by
    refine ⟨q37, ?_⟩
    simp only [s37, q37, s36, B37seven, B37r1]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h37 : B37seven ∣ B37r1 ^ 37 - s37 :=
    dvd_mul_remainder_next (e := 36) (d := 1) h36 h1 hred37
  simpa [s37, B37r2] using h37

theorem B37seven_frob_step3 : B37seven ∣ B37r2 ^ 37 - B37r3 := by
  have h1 : B37seven ∣ B37r2 ^ 1 - B37r2 := by simp
  let s2 : (ZMod 37)[X] := - 7 * X ^ 6 + 13 * X ^ 5 - 2 * X ^ 4 + 17 * X ^ 3 - 11 * X ^ 2 + 18 * X - 6
  let q2 : (ZMod 37)[X] := - 12 * X ^ 5 - 17 * X ^ 4 - 5 * X ^ 3 + 7 * X ^ 2 - 11 * X - 9
  have hred2 : B37seven ∣ B37r2 ^ 2 - s2 := by
    refine ⟨q2, ?_⟩
    simp only [s2, q2, B37seven, B37r2]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h2 : B37seven ∣ B37r2 ^ 2 - s2 :=
    dvd_square_remainder_next (e := 1) h1 hred2
  let s4 : (ZMod 37)[X] := - 14 * X ^ 6 + 15 * X ^ 5 - 14 * X ^ 4 - 10 * X ^ 3 - 10 * X ^ 2 + 10 * X + 9
  let q4 : (ZMod 37)[X] := 12 * X ^ 5 - 4 * X ^ 4 + 5 * X ^ 3 + 10 * X ^ 2 - 11 * X - 4
  have hred4 : B37seven ∣ s2 ^ 2 - s4 := by
    refine ⟨q4, ?_⟩
    simp only [s4, q4, s2, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4 : B37seven ∣ B37r2 ^ 4 - s4 :=
    dvd_square_remainder_next (e := 2) h2 hred4
  let s8 : (ZMod 37)[X] := 7 * X ^ 6 - 16 * X ^ 5 + 8 * X ^ 4 - 9 * X ^ 3 - 14 * X ^ 2 - 3 * X + 12
  let q8 : (ZMod 37)[X] := 11 * X ^ 5 - 4 * X ^ 4 - 10 * X ^ 3 - 11 * X ^ 2 + 13 * X - 2
  have hred8 : B37seven ∣ s4 ^ 2 - s8 := by
    refine ⟨q8, ?_⟩
    simp only [s8, q8, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h8 : B37seven ∣ B37r2 ^ 8 - s8 :=
    dvd_square_remainder_next (e := 4) h4 hred8
  let s16 : (ZMod 37)[X] := 2 * X ^ 6 - 15 * X ^ 5 - 16 * X ^ 4 - 10 * X ^ 3 + 12 * X ^ 2 + 14 * X - 6
  let q16 : (ZMod 37)[X] := 12 * X ^ 5 - 9 * X ^ 4 - 3 * X ^ 3 + 17 * X ^ 2 + 3 * X - 14
  have hred16 : B37seven ∣ s8 ^ 2 - s16 := by
    refine ⟨q16, ?_⟩
    simp only [s16, q16, s8, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h16 : B37seven ∣ B37r2 ^ 16 - s16 :=
    dvd_square_remainder_next (e := 8) h8 hred16
  let s32 : (ZMod 37)[X] := 15 * X ^ 6 - 16 * X ^ 5 + 12 * X ^ 4 + 13 * X ^ 3 + 4 * X ^ 2 - 7 * X + 6
  let q32 : (ZMod 37)[X] := 4 * X ^ 5 - 13 * X ^ 4 + 18 * X ^ 2 - 14 * X + 12
  have hred32 : B37seven ∣ s16 ^ 2 - s32 := by
    refine ⟨q32, ?_⟩
    simp only [s32, q32, s16, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h32 : B37seven ∣ B37r2 ^ 32 - s32 :=
    dvd_square_remainder_next (e := 16) h16 hred32
  let s36 : (ZMod 37)[X] := - 2 * X ^ 6 - 17 * X ^ 5 - 2 * X ^ 4 - 13 * X ^ 3 - 13 * X ^ 2 - 6 * X - 2
  let q36 : (ZMod 37)[X] := 12 * X ^ 5 - 2 * X ^ 4 + 9 * X ^ 3 - 6 * X ^ 2 + 5 * X + 15
  have hred36 : B37seven ∣ s32 * s4 - s36 := by
    refine ⟨q36, ?_⟩
    simp only [s36, q36, s32, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h36 : B37seven ∣ B37r2 ^ 36 - s36 :=
    dvd_mul_remainder_next (e := 32) (d := 4) h32 h4 hred36
  let s37 : (ZMod 37)[X] := 5 * X ^ 6 + 6 * X ^ 5 - 4 * X ^ 4 - 9 * X ^ 3 + 13 * X ^ 2 - 5 * X + 8
  let q37 : (ZMod 37)[X] := 10 * X ^ 5 + 9 * X ^ 4 + X ^ 3 - 11 * X ^ 2 + 3 * X + 18
  have hred37 : B37seven ∣ s36 * B37r2 - s37 := by
    refine ⟨q37, ?_⟩
    simp only [s37, q37, s36, B37seven, B37r2]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h37 : B37seven ∣ B37r2 ^ 37 - s37 :=
    dvd_mul_remainder_next (e := 36) (d := 1) h36 h1 hred37
  simpa [s37, B37r3] using h37

theorem B37seven_frob_step4 : B37seven ∣ B37r3 ^ 37 - B37r4 := by
  have h1 : B37seven ∣ B37r3 ^ 1 - B37r3 := by simp
  let s2 : (ZMod 37)[X] := 17 * X ^ 6 - 16 * X ^ 5 - 2 * X ^ 4 + 10 * X ^ 3 + 10 * X ^ 2 + 6 * X + 13
  let q2 : (ZMod 37)[X] := - 12 * X ^ 5 - 7 * X ^ 4 - 6 * X ^ 3 + 10 * X ^ 2 - 2 * X + 13
  have hred2 : B37seven ∣ B37r3 ^ 2 - s2 := by
    refine ⟨q2, ?_⟩
    simp only [s2, q2, B37seven, B37r3]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h2 : B37seven ∣ B37r3 ^ 2 - s2 :=
    dvd_square_remainder_next (e := 1) h1 hred2
  let s4 : (ZMod 37)[X] := X ^ 6 - 9 * X ^ 5 - 15 * X ^ 4 - 3 * X ^ 3 - 16 * X ^ 2 - 12 * X - 7
  let q4 : (ZMod 37)[X] := - 7 * X ^ 5 + 12 * X ^ 4 - 15 * X ^ 3 - 10 * X ^ 2 - 16 * X - 11
  have hred4 : B37seven ∣ s2 ^ 2 - s4 := by
    refine ⟨q4, ?_⟩
    simp only [s4, q4, s2, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4 : B37seven ∣ B37r3 ^ 4 - s4 :=
    dvd_square_remainder_next (e := 2) h2 hred4
  let s8 : (ZMod 37)[X] := - 9 * X ^ 6 - 6 * X ^ 5 - 16 * X ^ 4 + 3 * X ^ 3 + X ^ 2 + 2 * X - 17
  let q8 : (ZMod 37)[X] := X ^ 5 + 3 * X ^ 4 - 6 * X ^ 3 + 4 * X ^ 2 + 13 * X - 18
  have hred8 : B37seven ∣ s4 ^ 2 - s8 := by
    refine ⟨q8, ?_⟩
    simp only [s8, q8, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h8 : B37seven ∣ B37r3 ^ 8 - s8 :=
    dvd_square_remainder_next (e := 4) h4 hred8
  let s16 : (ZMod 37)[X] := 12 * X ^ 6 - 16 * X ^ 5 - 14 * X ^ 4 - 13 * X ^ 3 - 13 * X ^ 2 - 14 * X - 8
  let q16 : (ZMod 37)[X] := 7 * X ^ 5 - 4 * X ^ 4 - 8 * X ^ 3 - 3 * X ^ 2 - 14 * X - 7
  have hred16 : B37seven ∣ s8 ^ 2 - s16 := by
    refine ⟨q16, ?_⟩
    simp only [s16, q16, s8, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h16 : B37seven ∣ B37r3 ^ 16 - s16 :=
    dvd_square_remainder_next (e := 8) h8 hred16
  let s32 : (ZMod 37)[X] := - 15 * X ^ 6 + 5 * X ^ 5 - 15 * X ^ 4 - 10 * X ^ 3 - 17 * X ^ 2 - 8 * X - 1
  let q32 : (ZMod 37)[X] := - 4 * X ^ 5 + 13 * X ^ 4 + 7 * X ^ 3 + 2 * X ^ 2 + 17 * X - 11
  have hred32 : B37seven ∣ s16 ^ 2 - s32 := by
    refine ⟨q32, ?_⟩
    simp only [s32, q32, s16, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h32 : B37seven ∣ B37r3 ^ 32 - s32 :=
    dvd_square_remainder_next (e := 16) h16 hred32
  let s36 : (ZMod 37)[X] := - 17 * X ^ 6 - 13 * X ^ 5 - 14 * X ^ 4 - 8 * X ^ 3 + 8 * X ^ 2 - 8 * X - 2
  let q36 : (ZMod 37)[X] := - 15 * X ^ 5 + 10 * X ^ 4 - 8 * X ^ 3 - X ^ 2 + 10 * X + 11
  have hred36 : B37seven ∣ s32 * s4 - s36 := by
    refine ⟨q36, ?_⟩
    simp only [s36, q36, s32, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h36 : B37seven ∣ B37r3 ^ 36 - s36 :=
    dvd_mul_remainder_next (e := 32) (d := 4) h32 h4 hred36
  let s37 : (ZMod 37)[X] := 12 * X ^ 6 + 13 * X ^ 4 + 11 * X ^ 3 + 17 * X ^ 2 + 8 * X + 10
  let q37 : (ZMod 37)[X] := - 11 * X ^ 5 + 9 * X ^ 4 - 14 * X ^ 3 - 5 * X ^ 2 + 7 * X - 3
  have hred37 : B37seven ∣ s36 * B37r3 - s37 := by
    refine ⟨q37, ?_⟩
    simp only [s37, q37, s36, B37seven, B37r3]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h37 : B37seven ∣ B37r3 ^ 37 - s37 :=
    dvd_mul_remainder_next (e := 36) (d := 1) h36 h1 hred37
  simpa [s37, B37r4] using h37

theorem B37seven_frob_step5 : B37seven ∣ B37r4 ^ 37 - B37r5 := by
  have h1 : B37seven ∣ B37r4 ^ 1 - B37r4 := by simp
  let s2 : (ZMod 37)[X] := - 14 * X ^ 6 - 8 * X ^ 5 + 10 * X ^ 4 + 6 * X ^ 3 - 3 * X ^ 2 + 14 * X + 2
  let q2 : (ZMod 37)[X] := - 4 * X ^ 5 - 10 * X ^ 4 - 10 * X ^ 3 + 17 * X ^ 2 + 4 * X + 17
  have hred2 : B37seven ∣ B37r4 ^ 2 - s2 := by
    refine ⟨q2, ?_⟩
    simp only [s2, q2, B37seven, B37r4]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h2 : B37seven ∣ B37r4 ^ 2 - s2 :=
    dvd_square_remainder_next (e := 1) h1 hred2
  let s4 : (ZMod 37)[X] := 7 * X ^ 6 - 14 * X ^ 5 + 16 * X ^ 4 - 5 * X ^ 3 - 13 * X ^ 2 + 12 * X + 5
  let q4 : (ZMod 37)[X] := 11 * X ^ 5 + 11 * X ^ 4 - 10 * X ^ 3 - X ^ 2 + 10 * X + 7
  have hred4 : B37seven ∣ s2 ^ 2 - s4 := by
    refine ⟨q4, ?_⟩
    simp only [s4, q4, s2, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4 : B37seven ∣ B37r4 ^ 4 - s4 :=
    dvd_square_remainder_next (e := 2) h2 hred4
  let s8 : (ZMod 37)[X] := 5 * X ^ 6 - 12 * X ^ 5 - 5 * X ^ 4 - X ^ 3 - 16 * X ^ 2 + 10 * X + 6
  let q8 : (ZMod 37)[X] := 12 * X ^ 5 - 18 * X ^ 4 + 8 * X ^ 3 + 8 * X ^ 2 - 4 * X + 15
  have hred8 : B37seven ∣ s4 ^ 2 - s8 := by
    refine ⟨q8, ?_⟩
    simp only [s8, q8, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h8 : B37seven ∣ B37r4 ^ 8 - s8 :=
    dvd_square_remainder_next (e := 4) h4 hred8
  let s16 : (ZMod 37)[X] := - 14 * X ^ 6 - X ^ 5 - 13 * X ^ 4 - 16 * X ^ 3 - 15 * X ^ 2 - 6 * X - 15
  let q16 : (ZMod 37)[X] := - 12 * X ^ 5 - 2 * X ^ 4 + 12 * X ^ 3 - X ^ 2 - 6 * X + 13
  have hred16 : B37seven ∣ s8 ^ 2 - s16 := by
    refine ⟨q16, ?_⟩
    simp only [s16, q16, s8, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h16 : B37seven ∣ B37r4 ^ 16 - s16 :=
    dvd_square_remainder_next (e := 8) h8 hred16
  let s32 : (ZMod 37)[X] := 7 * X ^ 6 - 2 * X ^ 5 + 8 * X ^ 4 - 10 * X ^ 3 + 14 * X ^ 2 + 6 * X - 10
  let q32 : (ZMod 37)[X] := 11 * X ^ 5 + 7 * X ^ 3 - X ^ 2 + 13 * X - 17
  have hred32 : B37seven ∣ s16 ^ 2 - s32 := by
    refine ⟨q32, ?_⟩
    simp only [s32, q32, s16, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h32 : B37seven ∣ B37r4 ^ 32 - s32 :=
    dvd_square_remainder_next (e := 16) h16 hred32
  let s36 : (ZMod 37)[X] := - 12 * X ^ 6 + 17 * X ^ 5 - 14 * X ^ 4 - 18 * X ^ 3 + 4 * X ^ 2 - 6 * X - 1
  let q36 : (ZMod 37)[X] := 12 * X ^ 5 - 8 * X ^ 4 - 6 * X ^ 3 + 4 * X ^ 2 + X + 10
  have hred36 : B37seven ∣ s32 * s4 - s36 := by
    refine ⟨q36, ?_⟩
    simp only [s36, q36, s32, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h36 : B37seven ∣ B37r4 ^ 36 - s36 :=
    dvd_mul_remainder_next (e := 32) (d := 4) h32 h4 hred36
  let s37 : (ZMod 37)[X] := - 6 * X ^ 6 + 17 * X ^ 5 - 9 * X ^ 4 + 8 * X ^ 3 + 2 * X ^ 2 - 7 * X + 7
  let q37 : (ZMod 37)[X] := 4 * X ^ 5 - 8 * X ^ 4 - 10 * X ^ 3 + 10 * X ^ 2 - 13 * X + 8
  have hred37 : B37seven ∣ s36 * B37r4 - s37 := by
    refine ⟨q37, ?_⟩
    simp only [s37, q37, s36, B37seven, B37r4]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h37 : B37seven ∣ B37r4 ^ 37 - s37 :=
    dvd_mul_remainder_next (e := 36) (d := 1) h36 h1 hred37
  simpa [s37, B37r5] using h37

theorem B37seven_frob_step6 : B37seven ∣ B37r5 ^ 37 - B37r6 := by
  have h1 : B37seven ∣ B37r5 ^ 1 - B37r5 := by simp
  let s2 : (ZMod 37)[X] := - 13 * X ^ 6 + 6 * X ^ 5 - 4 * X ^ 4 + 16 * X ^ 3 - 12 * X ^ 2 + 9 * X - 16
  let q2 : (ZMod 37)[X] := - X ^ 5 - 3 * X ^ 4 + 10 * X ^ 3 + 16 * X ^ 2 - 15 * X - 11
  have hred2 : B37seven ∣ B37r5 ^ 2 - s2 := by
    refine ⟨q2, ?_⟩
    simp only [s2, q2, B37seven, B37r5]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h2 : B37seven ∣ B37r5 ^ 2 - s2 :=
    dvd_square_remainder_next (e := 1) h1 hred2
  let s4 : (ZMod 37)[X] := 6 * X ^ 6 + 18 * X ^ 5 + 14 * X ^ 4 - 12 * X ^ 3 + 18 * X ^ 2 + 2 * X + 1
  let q4 : (ZMod 37)[X] := - 16 * X ^ 5 - 11 * X ^ 4 + 16 * X ^ 3 + 18 * X ^ 2 + 9 * X - 9
  have hred4 : B37seven ∣ s2 ^ 2 - s4 := by
    refine ⟨q4, ?_⟩
    simp only [s4, q4, s2, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4 : B37seven ∣ B37r5 ^ 4 - s4 :=
    dvd_square_remainder_next (e := 2) h2 hred4
  let s8 : (ZMod 37)[X] := 9 * X ^ 6 + 6 * X ^ 5 + 17 * X ^ 4 + 11 * X ^ 3 - 17 * X ^ 2 - 9 * X + 9
  let q8 : (ZMod 37)[X] := - X ^ 5 + 10 * X ^ 4 + 8 * X ^ 3 - 10 * X ^ 2 + 11 * X - 18
  have hred8 : B37seven ∣ s4 ^ 2 - s8 := by
    refine ⟨q8, ?_⟩
    simp only [s8, q8, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h8 : B37seven ∣ B37r5 ^ 8 - s8 :=
    dvd_square_remainder_next (e := 4) h4 hred8
  let s16 : (ZMod 37)[X] := - X ^ 6 + 2 * X ^ 5 - 15 * X ^ 4 + 18 * X ^ 3 - X ^ 2 + 13 * X + 14
  let q16 : (ZMod 37)[X] := 7 * X ^ 5 - 4 * X ^ 4 + 10 * X ^ 3 + 10 * X ^ 2 + 10 * X + 12
  have hred16 : B37seven ∣ s8 ^ 2 - s16 := by
    refine ⟨q16, ?_⟩
    simp only [s16, q16, s8, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h16 : B37seven ∣ B37r5 ^ 16 - s16 :=
    dvd_square_remainder_next (e := 8) h8 hred16
  let s32 : (ZMod 37)[X] := 11 * X ^ 6 + 10 * X ^ 5 + 11 * X ^ 4 - 8 * X ^ 3 - 4 * X ^ 2 - 7 * X + 14
  let q32 : (ZMod 37)[X] := X ^ 5 + 17 * X ^ 4 + 12 * X ^ 3 + 7 * X ^ 2 - 15 * X - 16
  have hred32 : B37seven ∣ s16 ^ 2 - s32 := by
    refine ⟨q32, ?_⟩
    simp only [s32, q32, s16, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h32 : B37seven ∣ B37r5 ^ 32 - s32 :=
    dvd_square_remainder_next (e := 16) h16 hred32
  let s36 : (ZMod 37)[X] := - 2 * X ^ 6 + 16 * X ^ 5 + 7 * X ^ 4 - X ^ 2 - 15 * X + 9
  let q36 : (ZMod 37)[X] := - 8 * X ^ 5 + 16 * X ^ 4 - 6 * X ^ 3 + 4 * X ^ 2 + 8 * X + 2
  have hred36 : B37seven ∣ s32 * s4 - s36 := by
    refine ⟨q36, ?_⟩
    simp only [s36, q36, s32, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h36 : B37seven ∣ B37r5 ^ 36 - s36 :=
    dvd_mul_remainder_next (e := 32) (d := 4) h32 h4 hred36
  let s37 : (ZMod 37)[X] := 13 * X ^ 6 - 10 * X ^ 5 + X ^ 4 + 9 * X ^ 3 - 11 * X ^ 2 + 3 * X - 5
  let q37 : (ZMod 37)[X] := 12 * X ^ 5 + 11 * X ^ 4 + X ^ 3 + 3 * X ^ 2 - 3 * X + 5
  have hred37 : B37seven ∣ s36 * B37r5 - s37 := by
    refine ⟨q37, ?_⟩
    simp only [s37, q37, s36, B37seven, B37r5]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h37 : B37seven ∣ B37r5 ^ 37 - s37 :=
    dvd_mul_remainder_next (e := 36) (d := 1) h36 h1 hred37
  simpa [s37, B37r6] using h37

theorem B37seven_frob_step7 : B37seven ∣ B37r6 ^ 37 - B37r7 := by
  have h1 : B37seven ∣ B37r6 ^ 1 - B37r6 := by simp
  let s2 : (ZMod 37)[X] := 4 * X ^ 6 - 5 * X ^ 5 - 2 * X ^ 4 - 3 * X ^ 3 - 10 * X ^ 2 + X - 18
  let q2 : (ZMod 37)[X] := - 16 * X ^ 5 - 4 * X ^ 4 + X ^ 3 - 15 * X ^ 2 + 11 * X - 5
  have hred2 : B37seven ∣ B37r6 ^ 2 - s2 := by
    refine ⟨q2, ?_⟩
    simp only [s2, q2, B37seven, B37r6]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h2 : B37seven ∣ B37r6 ^ 2 - s2 :=
    dvd_square_remainder_next (e := 1) h1 hred2
  let s4 : (ZMod 37)[X] := - 4 * X ^ 6 - X ^ 5 - 5 * X ^ 4 - 6 * X ^ 3 - 11 * X ^ 2 + 6 * X - 8
  let q4 : (ZMod 37)[X] := 16 * X ^ 5 + 13 * X ^ 3 - 17 * X + 7
  have hred4 : B37seven ∣ s2 ^ 2 - s4 := by
    refine ⟨q4, ?_⟩
    simp only [s4, q4, s2, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4 : B37seven ∣ B37r6 ^ 4 - s4 :=
    dvd_square_remainder_next (e := 2) h2 hred4
  let s8 : (ZMod 37)[X] := - 6 * X ^ 6 + 18 * X ^ 5 + 2 * X ^ 3 + 17 * X ^ 2 + 14 * X - 18
  let q8 : (ZMod 37)[X] := 16 * X ^ 5 + 11 * X ^ 4 + 17 * X ^ 3 + 10 * X ^ 2 + 2 * X + 18
  have hred8 : B37seven ∣ s4 ^ 2 - s8 := by
    refine ⟨q8, ?_⟩
    simp only [s8, q8, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h8 : B37seven ∣ B37r6 ^ 8 - s8 :=
    dvd_square_remainder_next (e := 4) h4 hred8
  let s16 : (ZMod 37)[X] := 14 * X ^ 6 - 17 * X ^ 5 + 8 * X ^ 4 + 16 * X ^ 3 + 6 * X ^ 2 + 17 * X + 7
  let q16 : (ZMod 37)[X] := - X ^ 5 - 15 * X ^ 4 + 18 * X ^ 3 + 4 * X ^ 2 + 3 * X + 1
  have hred16 : B37seven ∣ s8 ^ 2 - s16 := by
    refine ⟨q16, ?_⟩
    simp only [s16, q16, s8, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h16 : B37seven ∣ B37r6 ^ 16 - s16 :=
    dvd_square_remainder_next (e := 8) h8 hred16
  let s32 : (ZMod 37)[X] := 14 * X ^ 6 + 3 * X ^ 5 + 12 * X ^ 4 + 12 * X ^ 3 - 18 * X ^ 2 + 16 * X + 3
  let q32 : (ZMod 37)[X] := 11 * X ^ 5 + 14 * X ^ 4 + 5 * X ^ 3 + 14 * X ^ 2 - 13 * X + 11
  have hred32 : B37seven ∣ s16 ^ 2 - s32 := by
    refine ⟨q32, ?_⟩
    simp only [s32, q32, s16, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h32 : B37seven ∣ B37r6 ^ 32 - s32 :=
    dvd_square_remainder_next (e := 16) h16 hred32
  let s36 : (ZMod 37)[X] := 15 * X ^ 6 - 6 * X ^ 5 - 2 * X ^ 4 + 16 * X ^ 3 + 3 * X - 17
  let q36 : (ZMod 37)[X] := 18 * X ^ 5 - 18 * X ^ 4 + 5 * X ^ 3 - 5 * X ^ 2 - 17 * X + 12
  have hred36 : B37seven ∣ s32 * s4 - s36 := by
    refine ⟨q36, ?_⟩
    simp only [s36, q36, s32, s4, B37seven]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h36 : B37seven ∣ B37r6 ^ 36 - s36 :=
    dvd_mul_remainder_next (e := 32) (d := 4) h32 h4 hred36
  let s37 : (ZMod 37)[X] := X
  let q37 : (ZMod 37)[X] := 10 * X ^ 5 - 18 * X ^ 4 - 12 * X ^ 3 + 11 * X ^ 2 + 5 * X - 3
  have hred37 : B37seven ∣ s36 * B37r6 - s37 := by
    refine ⟨q37, ?_⟩
    simp only [s37, q37, s36, B37seven, B37r6]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h37 : B37seven ∣ B37r6 ^ 37 - s37 :=
    dvd_mul_remainder_next (e := 36) (d := 1) h36 h1 hred37
  simpa [s37, B37r7] using h37

/-- Rabin/Frobenius certificate for the degree-seven factor modulo 37. -/
theorem B37seven_irreducible : Irreducible B37seven := by
  let : Fact (Nat.Prime 37) := ⟨by norm_num⟩
  let low : (ZMod 37)[X] :=
    16*X^6 + 9*X^5 + 33*X^4 + 14*X^3 + 25*X^2 + 8*X + 21
  have hform : B37seven = X^7 + low := by
    simp only [B37seven, low]
    ring
  have hlow : low.degree < 7 := by
    simp only [low]
    compute_degree; norm_num
  have hm : B37seven.Monic := by
    rw [hform]
    exact monic_X_pow_add hlow
  have hdeg : B37seven.natDegree = 7 := by
    rw [hform, natDegree_add_eq_left_of_degree_lt]
    · simp
    · simpa using hlow
  have hi1 : B37seven ∣ frobeniusIter 37 1 - B37r1 := by
    simpa [frobeniusIter] using B37seven_frob_step1
  have hi2 : B37seven ∣ frobeniusIter 37 2 - B37r2 :=
    frobeniusIter_dvd_next (p := 37) (e := 1) hi1 B37seven_frob_step2
  have hi3 : B37seven ∣ frobeniusIter 37 3 - B37r3 :=
    frobeniusIter_dvd_next (p := 37) (e := 2) hi2 B37seven_frob_step3
  have hi4 : B37seven ∣ frobeniusIter 37 4 - B37r4 :=
    frobeniusIter_dvd_next (p := 37) (e := 3) hi3 B37seven_frob_step4
  have hi5 : B37seven ∣ frobeniusIter 37 5 - B37r5 :=
    frobeniusIter_dvd_next (p := 37) (e := 4) hi4 B37seven_frob_step5
  have hi6 : B37seven ∣ frobeniusIter 37 6 - B37r6 :=
    frobeniusIter_dvd_next (p := 37) (e := 5) hi5 B37seven_frob_step6
  have hi7 : B37seven ∣ frobeniusIter 37 7 - B37r7 :=
    frobeniusIter_dvd_next (p := 37) (e := 6) hi6 B37seven_frob_step7
  have hfull : B37seven ∣ frobeniusIter 37 7 - X := by
    simpa [B37r7] using hi7
  have hcsmall : IsCoprime B37seven (B37r1 - X) := by
    refine ⟨7 * X ^ 5 - 2 * X ^ 4 + 14 * X ^ 3 + 4 * X ^ 2 + 7 * X + 3,
      14 * X ^ 6 - 4 * X ^ 5 + 14 * X ^ 4 + 9 * X ^ 3 + 15 * X ^ 2 + 4 * X - 11, ?_⟩
    simp only [B37seven, B37r1]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h1num : B37seven ∣ X ^ 37 ^ 1 - B37r1 := by
    rw [← frobeniusIter_eq_X_pow 37 1]
    exact hi1
  have hc1 : IsCoprime B37seven (X ^ 37 ^ 1 - X) := by
    apply isCoprime_of_dvd_sub hcsmall
    convert h1num using 1
    all_goals ring
  apply irreducible_of_frobenius_iter_certificate_B
      (p := 37) (n := 7) (f := B37seven)
  · exact hm
  · exact hdeg
  · norm_num
  · exact hfull
  · intro d hd hdpos hdlt
    have : d = 1 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hd with h | h
      · exact h
      · omega
    subst d
    exact hc1

def B211lin1 : (ZMod 211)[X] := X + 50

def B211lin2 : (ZMod 211)[X] := X + 133

def B211lin3 : (ZMod 211)[X] := X + 147

def B211five : (ZMod 211)[X] :=
  X^5 + 43*X^4 + 46*X^3 + 86*X^2 + 10*X + 128

theorem invariantB_mod211_factor :
    invariantB.map (Int.castRingHom (ZMod 211)) =
      55 * B211lin1 * B211lin2 * B211lin3 * B211five := by
  norm_num [invariantB, B211lin1, B211lin2, B211lin3, B211five]
  all_goals reduce_mod_char
  all_goals ring_nf
  all_goals reduce_mod_char

def B211r1 : (ZMod 211)[X] :=
  - 23 * X ^ 4 + 57 * X ^ 3 + 47 * X ^ 2 + 100 * X + 58

def B211r2 : (ZMod 211)[X] :=
  46 * X ^ 4 + 62 * X ^ 3 + 66 * X ^ 2 - 50 * X + 86

def B211r3 : (ZMod 211)[X] :=
  50 * X ^ 4 + 32 * X ^ 3 - 70 * X ^ 2 - 77 * X + 1

def B211r4 : (ZMod 211)[X] :=
  - 73 * X ^ 4 + 60 * X ^ 3 - 43 * X ^ 2 + 26 * X + 23

def B211r5 : (ZMod 211)[X] :=
  X

theorem B211five_frob_step1 : B211five ∣ X ^ 211 - B211r1 := by
  have h1 : B211five ∣ X ^ 1 - X := by simp
  let s2 : (ZMod 211)[X] := X ^ 2
  let q2 : (ZMod 211)[X] := 0
  have hred2 : B211five ∣ X ^ 2 - s2 := by
    refine ⟨q2, ?_⟩
    simp only [s2, q2, B211five]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h2 : B211five ∣ X ^ 2 - s2 :=
    dvd_square_remainder_next (e := 1) h1 hred2
  let s4 : (ZMod 211)[X] := X ^ 4
  let q4 : (ZMod 211)[X] := 0
  have hred4 : B211five ∣ s2 ^ 2 - s4 := by
    refine ⟨q4, ?_⟩
    simp only [s4, q4, s2, B211five]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h4 : B211five ∣ X ^ 4 - s4 :=
    dvd_square_remainder_next (e := 2) h2 hred4
  let s8 : (ZMod 211)[X] := - 88 * X ^ 4 + 30 * X ^ 3 - 3 * X ^ 2 - 15 * X + 12
  let q8 : (ZMod 211)[X] := X ^ 3 - 43 * X ^ 2 - 96 * X - 99
  have hred8 : B211five ∣ s4 ^ 2 - s8 := by
    refine ⟨q8, ?_⟩
    simp only [s8, q8, s4, B211five]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h8 : B211five ∣ X ^ 8 - s8 :=
    dvd_square_remainder_next (e := 4) h4 hred8
  let s16 : (ZMod 211)[X] := 75 * X ^ 4 + 35 * X ^ 3 - 60 * X ^ 2 - 26 * X + 87
  let q16 : (ZMod 211)[X] := - 63 * X ^ 3 - 39 * X ^ 2 + 95 * X + 101
  have hred16 : B211five ∣ s8 ^ 2 - s16 := by
    refine ⟨q16, ?_⟩
    simp only [s16, q16, s8, B211five]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h16 : B211five ∣ X ^ 16 - s16 :=
    dvd_square_remainder_next (e := 8) h8 hred16
  let s32 : (ZMod 211)[X] := 41 * X ^ 4 + 8 * X ^ 3 - 104 * X ^ 2 + 103 * X + 69
  let q32 : (ZMod 211)[X] := - 72 * X ^ 3 - 94 * X ^ 2 + X + 52
  have hred32 : B211five ∣ s16 ^ 2 - s32 := by
    refine ⟨q32, ?_⟩
    simp only [s32, q32, s16, B211five]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h32 : B211five ∣ X ^ 32 - s32 :=
    dvd_square_remainder_next (e := 16) h16 hred32
  let s64 : (ZMod 211)[X] := - 38 * X ^ 4 + 70 * X ^ 3 - 104 * X ^ 2 - 64 * X + 78
  let q64 : (ZMod 211)[X] := - 7 * X ^ 3 - 98 * X ^ 2 + 81 * X - 31
  have hred64 : B211five ∣ s32 ^ 2 - s64 := by
    refine ⟨q64, ?_⟩
    simp only [s64, q64, s32, B211five]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h64 : B211five ∣ X ^ 64 - s64 :=
    dvd_square_remainder_next (e := 32) h32 hred64
  let s128 : (ZMod 211)[X] := 5 * X ^ 4 - 31 * X ^ 3 - 68 * X ^ 2 + 17 * X - 103
  let q128 : (ZMod 211)[X] := - 33 * X ^ 3 - 103 * X ^ 2 - 28 * X - 72
  have hred128 : B211five ∣ s64 ^ 2 - s128 := by
    refine ⟨q128, ?_⟩
    simp only [s128, q128, s64, B211five]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h128 : B211five ∣ X ^ 128 - s128 :=
    dvd_square_remainder_next (e := 64) h64 hred128
  let s192 : (ZMod 211)[X] := 81 * X ^ 4 + 77 * X ^ 3 - 57 * X ^ 2 + 60 * X - 8
  let q192 : (ZMod 211)[X] := 21 * X ^ 3 - 8 * X ^ 2 - 95 * X - 66
  have hred192 : B211five ∣ s128 * s64 - s192 := by
    refine ⟨q192, ?_⟩
    simp only [s192, q192, s128, s64, B211five]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h192 : B211five ∣ X ^ 192 - s192 :=
    dvd_mul_remainder_next (e := 128) (d := 64) h128 h64 hred192
  let s208 : (ZMod 211)[X] := 14 * X ^ 4 + 60 * X ^ 3 - 36 * X ^ 2 + 89 * X - 62
  let q208 : (ZMod 211)[X] := - 44 * X ^ 3 - 48 * X ^ 2 - 31 * X - 61
  have hred208 : B211five ∣ s192 * s16 - s208 := by
    refine ⟨q208, ?_⟩
    simp only [s208, q208, s192, s16, B211five]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h208 : B211five ∣ X ^ 208 - s208 :=
    dvd_mul_remainder_next (e := 192) (d := 16) h192 h16 hred208
  let s210 : (ZMod 211)[X] := 49 * X ^ 4 - 26 * X ^ 3 - 10 * X ^ 2 + 41 * X - 43
  let q210 : (ZMod 211)[X] := 14 * X + 91
  have hred210 : B211five ∣ s208 * s2 - s210 := by
    refine ⟨q210, ?_⟩
    simp only [s210, q210, s208, s2, B211five]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h210 : B211five ∣ X ^ 210 - s210 :=
    dvd_mul_remainder_next (e := 208) (d := 2) h208 h2 hred210
  let s211 : (ZMod 211)[X] := - 23 * X ^ 4 + 57 * X ^ 3 + 47 * X ^ 2 + 100 * X + 58
  let q211 : (ZMod 211)[X] := 49
  have hred211 : B211five ∣ s210 * X - s211 := by
    refine ⟨q211, ?_⟩
    simp only [s211, q211, s210, B211five]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h211 : B211five ∣ X ^ 211 - s211 :=
    dvd_mul_remainder_next (e := 210) (d := 1) h210 h1 hred211
  simpa [s211, B211r1] using h211

/- The later Frobenius steps use the first step as `X^211 mod B211five`, then
   verify a small composition remainder. -/

theorem B211five_frob_step2 : B211five ∣ B211r1 ^ 211 - B211r2 := by
  let : Fact (Nat.Prime 211) := ⟨by norm_num⟩
  apply dvd_frobenius_remainder_next (a := B211r1)
  · exact B211five_frob_step1
  · let q : (ZMod 211)[X] :=
      X ^ 11 + 48 * X ^ 10 - 85 * X ^ 9 + 93 * X ^ 8 + 57 * X ^ 7 +
        48 * X ^ 6 - 36 * X ^ 5 - 6 * X ^ 4 + 78 * X ^ 3 + 60 * X ^ 2 -
        36 * X - 5
    refine ⟨q, ?_⟩
    simp only [q, B211five, B211r1, B211r2, add_comp, neg_comp,
      mul_comp, pow_comp, X_comp, ofNat_comp]
    reduce_mod_char
    ring_nf
    reduce_mod_char

theorem B211five_frob_step3 : B211five ∣ B211r2 ^ 211 - B211r3 := by
  let : Fact (Nat.Prime 211) := ⟨by norm_num⟩
  apply dvd_frobenius_remainder_next (a := B211r1)
  · exact B211five_frob_step1
  · let q : (ZMod 211)[X] :=
      - 2 * X ^ 11 - 96 * X ^ 10 - 41 * X ^ 9 + 25 * X ^ 8 - 67 * X ^ 7 -
        17 * X ^ 6 - 35 * X ^ 5 - 85 * X ^ 4 - 20 * X ^ 3 + 12 * X ^ 2 -
        9 * X - 2
    refine ⟨q, ?_⟩
    simp only [q, B211five, B211r1, B211r2, B211r3, add_comp, sub_comp,
      mul_comp, pow_comp, X_comp, ofNat_comp]
    reduce_mod_char
    ring_nf
    reduce_mod_char

theorem B211five_frob_step4 : B211five ∣ B211r3 ^ 211 - B211r4 := by
  let : Fact (Nat.Prime 211) := ⟨by norm_num⟩
  apply dvd_frobenius_remainder_next (a := B211r1)
  · exact B211five_frob_step1
  · let q : (ZMod 211)[X] :=
      7 * X ^ 11 - 86 * X ^ 10 + 38 * X ^ 9 + 18 * X ^ 8 + 84 * X ^ 7 +
        31 * X ^ 6 + 97 * X ^ 5 + 20 * X ^ 4 - 85 * X ^ 3 - 62 * X ^ 2 +
        51 * X + 12
    refine ⟨q, ?_⟩
    simp only [q, B211five, B211r1, B211r3, B211r4, add_comp, sub_comp,
      mul_comp, pow_comp, X_comp, ofNat_comp, one_comp]
    reduce_mod_char
    ring_nf
    reduce_mod_char

theorem B211five_frob_step5 : B211five ∣ B211r4 ^ 211 - B211r5 := by
  let : Fact (Nat.Prime 211) := ⟨by norm_num⟩
  apply dvd_frobenius_remainder_next (a := B211r1)
  · exact B211five_frob_step1
  · let q : (ZMod 211)[X] :=
      - 6 * X ^ 11 - 77 * X ^ 10 + 88 * X ^ 9 + 75 * X ^ 8 - 74 * X ^ 7 -
        62 * X ^ 6 - 26 * X ^ 5 + 71 * X ^ 4 + 27 * X ^ 3 - 10 * X ^ 2 -
        6 * X - 5
    refine ⟨q, ?_⟩
    simp only [q, B211five, B211r1, B211r4, B211r5, add_comp, sub_comp,
      neg_comp, mul_comp, pow_comp, X_comp, ofNat_comp]
    reduce_mod_char
    ring_nf
    reduce_mod_char

/-- Rabin/Frobenius certificate for the degree-five factor modulo 211. -/
theorem B211five_irreducible : Irreducible B211five := by
  let : Fact (Nat.Prime 211) := ⟨by norm_num⟩
  let low : (ZMod 211)[X] := 43*X^4 + 46*X^3 + 86*X^2 + 10*X + 128
  have hform : B211five = X^5 + low := by
    simp only [B211five, low]
    ring
  have hlow : low.degree < 5 := by
    simp only [low]
    compute_degree; norm_num
  have hm : B211five.Monic := by
    rw [hform]
    exact monic_X_pow_add hlow
  have hdeg : B211five.natDegree = 5 := by
    rw [hform, natDegree_add_eq_left_of_degree_lt]
    · simp
    · simpa using hlow
  have hi1 : B211five ∣ frobeniusIter 211 1 - B211r1 := by
    simpa [frobeniusIter] using B211five_frob_step1
  have hi2 : B211five ∣ frobeniusIter 211 2 - B211r2 :=
    frobeniusIter_dvd_next (p := 211) (e := 1) hi1 B211five_frob_step2
  have hi3 : B211five ∣ frobeniusIter 211 3 - B211r3 :=
    frobeniusIter_dvd_next (p := 211) (e := 2) hi2 B211five_frob_step3
  have hi4 : B211five ∣ frobeniusIter 211 4 - B211r4 :=
    frobeniusIter_dvd_next (p := 211) (e := 3) hi3 B211five_frob_step4
  have hi5 : B211five ∣ frobeniusIter 211 5 - B211r5 :=
    frobeniusIter_dvd_next (p := 211) (e := 4) hi4 B211five_frob_step5
  have hfull : B211five ∣ frobeniusIter 211 5 - X := by
    simpa [B211r5] using hi5
  have hcsmall : IsCoprime B211five (B211r1 - X) := by
    refine ⟨64 * X ^ 3 - 38 * X ^ 2 + 88 * X - 19,
      67 * X ^ 4 + 18 * X ^ 3 + 68 * X ^ 2 - 60 * X - 49, ?_⟩
    simp only [B211five, B211r1]
    reduce_mod_char
    ring_nf
    reduce_mod_char
  have h1num : B211five ∣ X ^ 211 ^ 1 - B211r1 := by
    rw [← frobeniusIter_eq_X_pow 211 1]
    exact hi1
  have hc1 : IsCoprime B211five (X ^ 211 ^ 1 - X) := by
    apply isCoprime_of_dvd_sub hcsmall
    convert h1num using 1
    all_goals ring
  apply irreducible_of_frobenius_iter_certificate_B
      (p := 211) (n := 5) (f := B211five)
  · exact hm
  · exact hdeg
  · norm_num
  · exact hfull
  · intro d hd hdpos hdlt
    have : d = 1 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with h | h
      · exact h
      · omega
    subst d
    exact hc1

/-- The three linear roots modulo 211 are pairwise distinct. -/
theorem B211_linear_roots_distinct :
    (50 : ZMod 211) ≠ 133 ∧ (50 : ZMod 211) ≠ 147 ∧
      (133 : ZMod 211) ≠ 147 := by
  native_decide

/-- The modulo-5 factor is irreducible, re-exported here as the 8-cycle
certificate. -/
theorem B_mod5_cycle8 : Irreducible invariantB5 :=
  invariantB5_irreducible

/-- Exact discriminant of the degree-eight B-sector polynomial. -/
def invariantBDiscriminant : ℤ :=
  4499377662617672557853141155803904218497371782887185543954618106918365458531704497799484108177772483166774132385138081792

/-- The discriminant is `6308533` times an exact square. -/
def invariantBDiscSquareRoot : ℤ :=
  844524074536466297129247983837497504533280189906805587968

theorem invariantB_discriminant_value :
    invariantB.discr = invariantBDiscriminant := by
  have hdeg : invariantB.natDegree = 8 := by
    norm_num [invariantB]
    compute_degree <;> norm_num
  have hdegExplicit :
      (279841*X^8 - 9805544*X^7 + 210448304*X^6 -
        1535826944*X^5 + 6984915200*X^4 - 8382980096*X^3 +
        3230461952*X^2 - 376668160*X + 7929856 : ℤ[X]).natDegree = 8 := by
    simpa only [invariantB] using hdeg
  let e : Fin (invariantB.natDegree - 1 + invariantB.natDegree) ≃ Fin 15 :=
    finCongr (by rw [hdeg])
  rw [Polynomial.discr, ← Matrix.det_reindex_self e]
  have hmat : invariantB.sylvesterDeriv.reindex e e =
      !![7929856, 0, 0, 0, 0, 0, 0, -376668160, 0, 0, 0, 0, 0, 0, 0;
         -376668160, 7929856, 0, 0, 0, 0, 0, 6460923904, -376668160, 0, 0, 0, 0, 0, 0;
         3230461952, -376668160, 7929856, 0, 0, 0, 0, -25148940288, 6460923904, -376668160, 0, 0, 0, 0, 0;
         -8382980096, 3230461952, -376668160, 7929856, 0, 0, 0, 27939660800, -25148940288, 6460923904, -376668160, 0, 0, 0, 0;
         6984915200, -8382980096, 3230461952, -376668160, 7929856, 0, 0, -7679134720, 27939660800, -25148940288, 6460923904, -376668160, 0, 0, 0;
         -1535826944, 6984915200, -8382980096, 3230461952, -376668160, 7929856, 0, 1262689824, -7679134720, 27939660800, -25148940288, 6460923904, -376668160, 0, 0;
         210448304, -1535826944, 6984915200, -8382980096, 3230461952, -376668160, 7929856, -68638808, 1262689824, -7679134720, 27939660800, -25148940288, 6460923904, -376668160, 0;
         -9805544, 210448304, -1535826944, 6984915200, -8382980096, 3230461952, -376668160, 2238728, -68638808, 1262689824, -7679134720, 27939660800, -25148940288, 6460923904, -376668160;
         279841, -9805544, 210448304, -1535826944, 6984915200, -8382980096, 3230461952, 0, 2238728, -68638808, 1262689824, -7679134720, 27939660800, -25148940288, 6460923904;
         0, 279841, -9805544, 210448304, -1535826944, 6984915200, -8382980096, 0, 0, 2238728, -68638808, 1262689824, -7679134720, 27939660800, -25148940288;
         0, 0, 279841, -9805544, 210448304, -1535826944, 6984915200, 0, 0, 0, 2238728, -68638808, 1262689824, -7679134720, 27939660800;
         0, 0, 0, 279841, -9805544, 210448304, -1535826944, 0, 0, 0, 0, 2238728, -68638808, 1262689824, -7679134720;
         0, 0, 0, 0, 279841, -9805544, 210448304, 0, 0, 0, 0, 0, 2238728, -68638808, 1262689824;
         0, 0, 0, 0, 0, 279841, -9805544, 0, 0, 0, 0, 0, 0, 2238728, -68638808;
         0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 8] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [e, Polynomial.sylvesterDeriv, Polynomial.sylvester, hdeg,
        Polynomial.coeff_derivative, Fin.addCases, Matrix.reindex_apply,
        finCongr_symm, Matrix.submatrix_apply, finCongr_apply,
        Fin.cast_mk, Matrix.of_apply] <;>
      norm_num [invariantB, hdegExplicit, Polynomial.coeff_X, Polynomial.coeff_X_pow]
  rw [hmat]
  simp only [norm_det]
  norm_num [hdeg, invariantBDiscriminant]

theorem invariantB_discriminant_square_decomposition :
    invariantBDiscriminant =
      6308533 * invariantBDiscSquareRoot * invariantBDiscSquareRoot := by
  native_decide

/-- The discriminant is not a square: modulo 5 it is 2, while no square in
`ZMod 5` is 2. -/
theorem invariantB_discriminant_not_square :
    ¬ ∃ z : ℤ, z * z = invariantBDiscriminant := by
  intro h
  rcases h with ⟨z, hz⟩
  have hz5 : (z : ZMod 5) * (z : ZMod 5) = 2 := by
    have hcast := congrArg (fun t : ℤ => (t : ZMod 5)) hz
    norm_num [invariantBDiscriminant] at hcast ⊢
    exact hcast
  have hnosq : ∀ a : ZMod 5, a * a ≠ 2 := by
    native_decide
  exact hnosq (z : ZMod 5) hz5

end

end Biunimodular.F11
