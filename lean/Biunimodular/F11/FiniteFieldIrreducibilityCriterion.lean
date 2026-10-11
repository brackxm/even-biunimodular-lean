/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Biunimodular.F11

open Polynomial

/-- If an explicit monic polynomial over `ZMod p` divides the full Frobenius
polynomial in its degree and is coprime to every proper Frobenius divisor,
then it is irreducible.  The explicit Frobenius and coprimality certificates supply the proof. -/
theorem irreducible_of_frobenius_certificate
    {p n : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
    (hfmonic : f.Monic)
    (hdeg : f.natDegree = n)
    (hn : 0 < n)
    (hfull : f ∣ X ^ p ^ n - X)
    (hproper : ∀ d : ℕ, d ∣ n → 0 < d → d < n →
      IsCoprime f (X ^ p ^ d - X)) :
    Irreducible f := by
  have hf0 : f ≠ 0 := hfmonic.ne_zero
  have hfnu : ¬ IsUnit f := by
    intro hu
    have hz : f.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    omega
  obtain ⟨g, hgirr, hgdiv⟩ :=
    WfDvdMonoid.exists_irreducible_factor hfnu hf0
  suffices hgdeg : g.natDegree = n by
    exact (associated_of_dvd_of_natDegree_le hgdiv hf0 (by omega)).irreducible hgirr
  have hgfull : g ∣ X ^ p ^ n - X := hgdiv.trans hfull
  have hgfullCard : g ∣ X ^ Nat.card (ZMod p) ^ n - X := by
    simpa [Nat.card_zmod] using hgfull
  have hdvd : g.natDegree ∣ n :=
    hgirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X (n := n) hgfullCard
  have hgpos : 0 < g.natDegree := hgirr.natDegree_pos
  have hgle : g.natDegree ≤ n := by
    have := natDegree_le_of_dvd hgdiv hf0
    omega
  by_contra hne
  have hglt : g.natDegree < n := lt_of_le_of_ne hgle hne
  have hcop := hproper g.natDegree hdvd hgpos hglt
  have hgfrob : g ∣ X ^ p ^ g.natDegree - X := by
    simpa [Nat.card_zmod] using
      ((hgirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X
        (n := g.natDegree)).mp dvd_rfl)
  have hgg : IsCoprime g g := hcop.mono hgdiv hgfrob
  exact hgirr.not_isUnit (isCoprime_self.mp hgg)

/-- Chain one exact Frobenius remainder certificate. -/
theorem frobenius_dvd_next
    {p e : ℕ} {f r s : (ZMod p)[X]}
    (hprev : f ∣ X ^ p ^ e - r)
    (hstep : f ∣ r ^ p - s) :
    f ∣ X ^ p ^ (e + 1) - s := by
  have hp : f ∣ (X ^ p ^ e) ^ p - r ^ p :=
    hprev.trans (sub_dvd_pow_sub_pow (X ^ p ^ e) r p)
  have hsum : f ∣ ((X ^ p ^ e) ^ p - r ^ p) + (r ^ p - s) :=
    dvd_add hp hstep
  simpa [Nat.pow_succ, pow_mul] using hsum

/-- Iterated Frobenius power written recursively, so intermediate proof terms
never have to normalize the large natural exponent `p^n`. -/
noncomputable def frobeniusIter (p : ℕ) : ℕ → (ZMod p)[X]
  | 0 => X
  | n + 1 => frobeniusIter p n ^ p

/-- The recursive Frobenius iterator is the usual power `X^(p^n)`. -/
theorem frobeniusIter_eq_X_pow (p n : ℕ) :
    frobeniusIter p n = (X : (ZMod p)[X]) ^ p ^ n := by
  induction n with
  | zero => simp [frobeniusIter]
  | succ n ih =>
      rw [frobeniusIter, ih, ← pow_mul, Nat.pow_succ]

/-- Chain one Frobenius remainder certificate without first converting the
iterated polynomial power to the large exponent `X^(p^n)`. -/
theorem frobeniusIter_dvd_next
    {p e : ℕ} {f r s : (ZMod p)[X]}
    (hprev : f ∣ frobeniusIter p e - r)
    (hstep : f ∣ r ^ p - s) :
    f ∣ frobeniusIter p (e + 1) - s := by
  change f ∣ (frobeniusIter p e) ^ p - s
  have hp : f ∣ (frobeniusIter p e) ^ p - r ^ p :=
    hprev.trans (sub_dvd_pow_sub_pow (frobeniusIter p e) r p)
  have hsum : f ∣ ((frobeniusIter p e) ^ p - r ^ p) + (r ^ p - s) :=
    dvd_add hp hstep
  convert hsum using 1
  all_goals ring

/-- Replacing the second argument of an `IsCoprime` certificate by a
congruent polynomial modulo the first preserves coprimality. -/
theorem isCoprime_of_dvd_sub
    {R : Type*} [CommRing R] {f a b : R}
    (hsmall : IsCoprime f b)
    (hrel : f ∣ a - b) :
    IsCoprime f a := by
  rcases hrel with ⟨q, hq⟩
  rcases hsmall with ⟨s, t, hst⟩
  refine ⟨s - t * q, t, ?_⟩
  have ha : a = b + f * q := by
    calc
      a = (a - b) + b := by ring
      _ = b + f * q := by rw [hq]; ring
  rw [ha]
  calc
    (s - t * q) * f + t * (b + f * q) = s * f + t * b := by ring
    _ = 1 := hst

end Biunimodular.F11
