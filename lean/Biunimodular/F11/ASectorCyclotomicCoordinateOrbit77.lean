/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorGaloisGenerator77

set_option autoImplicit false

namespace Biunimodular.F11

noncomputable section

local instance : IsCyclotomicExtension {77} ℚ Conductor77Cyclotomic :=
  CyclotomicField.isCyclotomicExtension 77 ℚ

private theorem aSectorX77Pair_inv
    (z : Conductor77Cyclotomic) (hz : z ^ 77 = 1) :
    aSectorX77Pair z⁻¹ = aSectorX77Pair z := by
  have hp (k : ℕ) (hk : k ≤ 77) :
      (z⁻¹) ^ k = z ^ (77 - k) := by
    rw [inv_pow]
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_add, Nat.sub_add_cancel hk]
    exact hz
  unfold aSectorX77Pair
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hk : (3 * (n + 1)) % 77 ≤ 77 :=
    Nat.le_of_lt (Nat.mod_lt _ (by norm_num))
  have hkc : 77 - ((3 * (n + 1)) % 77) ≤ 77 := Nat.sub_le _ _
  rw [hp _ hk, hp _ hkc, Nat.sub_sub_self hk]
  ring

/-- The the `X_e=P(ζ₇₇^e+ζ₇₇^{-e})`, using the inverse of `3`
modulo `77` because `aSectorX77Pair` is based at exponent `3`. -/
def aSectorX77AtExponent (e : ℕ) : Conductor77Cyclotomic :=
  aSectorX77Pair (zeta77 ^ (26 * e))

private theorem zeta77_pow77 : zeta77 ^ 77 = 1 :=
  (IsCyclotomicExtension.zeta_spec 77 ℚ
    Conductor77Cyclotomic).pow_eq_one

/-- The exponent-`3` member is the explicit coordinate used in the
degree-thirty maximal-real field theorem. -/
theorem aSectorX77AtExponent_three :
    aSectorX77AtExponent 3 = aSectorX77 := by
  have hz : zeta77 ^ (26 * 3) = zeta77 := by
    norm_num
    rw [show 78 = 77 + 1 by norm_num, pow_add, zeta77_pow77]
    simp
  simp [aSectorX77AtExponent, aSectorX77, hz]

theorem aSectorX77AtExponent_eq_of_mod {e f : ℕ}
    (h : (26 * e) % 77 = (26 * f) % 77) :
    aSectorX77AtExponent e = aSectorX77AtExponent f := by
  unfold aSectorX77AtExponent
  congr 1
  calc
    zeta77 ^ (26 * e) = zeta77 ^ ((26 * e) % 77) :=
      pow_eq_pow_mod _ zeta77_pow77
    _ = zeta77 ^ ((26 * f) % 77) := by rw [h]
    _ = zeta77 ^ (26 * f) :=
      (pow_eq_pow_mod _ zeta77_pow77).symm

theorem aSectorX77AtExponent_eq_of_neg_mod {e f : ℕ}
    (h : (26 * e) % 77 + (26 * f) % 77 = 77) :
    aSectorX77AtExponent e = aSectorX77AtExponent f := by
  have hz : (zeta77 ^ (26 * e)) =
      (zeta77 ^ (26 * f))⁻¹ := by
    have he : zeta77 ^ (26 * e) = zeta77 ^ ((26 * e) % 77) :=
      pow_eq_pow_mod _ zeta77_pow77
    have hf : zeta77 ^ (26 * f) = zeta77 ^ ((26 * f) % 77) :=
      pow_eq_pow_mod _ zeta77_pow77
    rw [he, hf]
    symm
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_add, h]
    exact zeta77_pow77
  unfold aSectorX77AtExponent
  rw [hz]
  exact aSectorX77Pair_inv _ (by
    calc
      (zeta77 ^ (26 * f)) ^ 77 = zeta77 ^ ((26 * f) * 77) := by
        simp only [← pow_mul]
      _ = zeta77 ^ (77 * (26 * f)) := by congr 1; omega
      _ = (zeta77 ^ 77) ^ (26 * f) := by rw [pow_mul]
      _ = 1 := by rw [zeta77_pow77, one_pow])

/-- Congruent or opposite conductor-77 exponents give the same real
cyclotomic coordinate. -/
theorem aSectorX77AtExponent_eq_of_signed_mod {e f : ℕ}
    (h : (26 * e) % 77 = (26 * f) % 77 ∨
      (26 * e) % 77 + (26 * f) % 77 = 77) :
    aSectorX77AtExponent e = aSectorX77AtExponent f := by
  rcases h with h | h
  · exact aSectorX77AtExponent_eq_of_mod h
  · exact aSectorX77AtExponent_eq_of_neg_mod h

/-- The actual conductor-77 Galois map multiplies the coordinate exponent
by `62`. -/
theorem conductor77Sigma62_aSectorX77AtExponent (e : ℕ) :
    conductor77Sigma62 (aSectorX77AtExponent e) =
      aSectorX77AtExponent (62 * e) := by
  have hmap (z : Conductor77Cyclotomic) :
      conductor77Sigma62 (aSectorX77Pair z) =
        aSectorX77Pair (conductor77Sigma62 z) := by
    simp [aSectorX77Pair, map_sum, map_add, map_mul, map_pow,
      map_intCast, map_ofNat]
  unfold aSectorX77AtExponent
  rw [hmap, map_pow, conductor77Sigma62_zeta]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

/-- The signed modular congruences behind the three displayed coordinate
rows.  These are finite arithmetic statements, independent of field equality
decision procedures. -/
theorem aSectorPhaseExponents_signed_coordinate_relation :
    ∀ row ∈ aSectorPhaseExponents,
      List.Forall₂
        (fun e f =>
          (26 * e) % 77 = (26 * f) % 77 ∨
            (26 * e) % 77 + (26 * f) % 77 = 77)
        (row.map (62 * ·)) (dilateASectorExponentRow11 row) := by
  have h : aSectorPhaseExponents.Forall (fun row =>
      List.Forall₂
        (fun e f =>
          (26 * e) % 77 = (26 * f) % 77 ∨
            (26 * e) % 77 + (26 * f) % 77 = 77)
        (row.map (62 * ·)) (dilateASectorExponentRow11 row)) := by
    native_decide
  exact List.forall_iff_forall_mem.mp h

/-- The actual cyclotomic coordinate values in every recorded A row rotate
under exponent-62 Galois exactly as they do under physical dilation. -/
theorem aSectorCyclotomicCoordinateRows_galois_dilation :
    ∀ row ∈ aSectorPhaseExponents,
      (row.map aSectorX77AtExponent).map conductor77Sigma62 =
        (dilateASectorExponentRow11 row).map aSectorX77AtExponent := by
  intro row hr
  have hrel := aSectorPhaseExponents_signed_coordinate_relation row hr
  have hmap {es fs : List ℕ}
      (h : List.Forall₂
        (fun e f =>
          (26 * e) % 77 = (26 * f) % 77 ∨
            (26 * e) % 77 + (26 * f) % 77 = 77) es fs) :
      es.map aSectorX77AtExponent =
        fs.map aSectorX77AtExponent := by
    induction h with
    | nil => rfl
    | @cons e f es fs hef htail ih =>
        simp only [List.map_cons]
        exact congrArg₂ List.cons
          (aSectorX77AtExponent_eq_of_signed_mod hef) ih
  calc
    (row.map aSectorX77AtExponent).map conductor77Sigma62 =
        (row.map (62 * ·)).map aSectorX77AtExponent := by
      simp [List.map_map, conductor77Sigma62_aSectorX77AtExponent]
    _ = (dilateASectorExponentRow11 row).map
        aSectorX77AtExponent := hmap hrel

end
end Biunimodular.F11
