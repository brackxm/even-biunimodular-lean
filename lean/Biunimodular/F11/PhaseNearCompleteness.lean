/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.FinitePhaseNativeScan
public meta import Biunimodular.F11.ProofTactics
public meta import Biunimodular.F11.FinitePhaseNativeScan

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

/-- For each of the 160 signed phase centers, the corresponding entry in the
sorted table of 80 signed imaginary roots. -/
def candidateSignedRootQ : Array (Fin 80) := #[
  ⟨35,by decide⟩,⟨44,by decide⟩,⟨35,by decide⟩,⟨44,by decide⟩,
  ⟨26,by decide⟩,⟨53,by decide⟩,⟨26,by decide⟩,⟨53,by decide⟩,
  ⟨20,by decide⟩,⟨59,by decide⟩,⟨20,by decide⟩,⟨59,by decide⟩,
  ⟨11,by decide⟩,⟨68,by decide⟩,⟨11,by decide⟩,⟨68,by decide⟩,
  ⟨0,by decide⟩,⟨79,by decide⟩,⟨0,by decide⟩,⟨79,by decide⟩,
  ⟨36,by decide⟩,⟨43,by decide⟩,⟨36,by decide⟩,⟨43,by decide⟩,
  ⟨34,by decide⟩,⟨45,by decide⟩,⟨34,by decide⟩,⟨45,by decide⟩,
  ⟨31,by decide⟩,⟨48,by decide⟩,⟨31,by decide⟩,⟨48,by decide⟩,
  ⟨30,by decide⟩,⟨49,by decide⟩,⟨30,by decide⟩,⟨49,by decide⟩,
  ⟨29,by decide⟩,⟨50,by decide⟩,⟨29,by decide⟩,⟨50,by decide⟩,
  ⟨23,by decide⟩,⟨56,by decide⟩,⟨23,by decide⟩,⟨56,by decide⟩,
  ⟨22,by decide⟩,⟨57,by decide⟩,⟨22,by decide⟩,⟨57,by decide⟩,
  ⟨21,by decide⟩,⟨58,by decide⟩,⟨21,by decide⟩,⟨58,by decide⟩,
  ⟨19,by decide⟩,⟨60,by decide⟩,⟨19,by decide⟩,⟨60,by decide⟩,
  ⟨17,by decide⟩,⟨62,by decide⟩,⟨17,by decide⟩,⟨62,by decide⟩,
  ⟨14,by decide⟩,⟨65,by decide⟩,⟨14,by decide⟩,⟨65,by decide⟩,
  ⟨8,by decide⟩,⟨71,by decide⟩,⟨8,by decide⟩,⟨71,by decide⟩,
  ⟨5,by decide⟩,⟨74,by decide⟩,⟨5,by decide⟩,⟨74,by decide⟩,
  ⟨4,by decide⟩,⟨75,by decide⟩,⟨4,by decide⟩,⟨75,by decide⟩,
  ⟨2,by decide⟩,⟨77,by decide⟩,⟨2,by decide⟩,⟨77,by decide⟩,
  ⟨39,by decide⟩,⟨40,by decide⟩,⟨39,by decide⟩,⟨40,by decide⟩,
  ⟨38,by decide⟩,⟨41,by decide⟩,⟨38,by decide⟩,⟨41,by decide⟩,
  ⟨37,by decide⟩,⟨42,by decide⟩,⟨37,by decide⟩,⟨42,by decide⟩,
  ⟨33,by decide⟩,⟨46,by decide⟩,⟨33,by decide⟩,⟨46,by decide⟩,
  ⟨32,by decide⟩,⟨47,by decide⟩,⟨32,by decide⟩,⟨47,by decide⟩,
  ⟨28,by decide⟩,⟨51,by decide⟩,⟨28,by decide⟩,⟨51,by decide⟩,
  ⟨27,by decide⟩,⟨52,by decide⟩,⟨27,by decide⟩,⟨52,by decide⟩,
  ⟨25,by decide⟩,⟨54,by decide⟩,⟨25,by decide⟩,⟨54,by decide⟩,
  ⟨24,by decide⟩,⟨55,by decide⟩,⟨24,by decide⟩,⟨55,by decide⟩,
  ⟨18,by decide⟩,⟨61,by decide⟩,⟨18,by decide⟩,⟨61,by decide⟩,
  ⟨16,by decide⟩,⟨63,by decide⟩,⟨16,by decide⟩,⟨63,by decide⟩,
  ⟨15,by decide⟩,⟨64,by decide⟩,⟨15,by decide⟩,⟨64,by decide⟩,
  ⟨13,by decide⟩,⟨66,by decide⟩,⟨13,by decide⟩,⟨66,by decide⟩,
  ⟨12,by decide⟩,⟨67,by decide⟩,⟨12,by decide⟩,⟨67,by decide⟩,
  ⟨10,by decide⟩,⟨69,by decide⟩,⟨10,by decide⟩,⟨69,by decide⟩,
  ⟨9,by decide⟩,⟨70,by decide⟩,⟨9,by decide⟩,⟨70,by decide⟩,
  ⟨7,by decide⟩,⟨72,by decide⟩,⟨7,by decide⟩,⟨72,by decide⟩,
  ⟨6,by decide⟩,⟨73,by decide⟩,⟨6,by decide⟩,⟨73,by decide⟩,
  ⟨3,by decide⟩,⟨76,by decide⟩,⟨3,by decide⟩,⟨76,by decide⟩,
  ⟨1,by decide⟩,⟨78,by decide⟩,⟨1,by decide⟩,⟨78,by decide⟩]

theorem candidateSignedRootQ_size : candidateSignedRootQ.size = 160 := by native_decide

theorem candidateSignedRootQ_data_exact :
    ∀ idx : Fin 160,
      let q := candidateSignedRootQ[idx.1]!
      let r := signedRootCenters80[q.1]!
      r.im = (phaseCenters160[idx.1]!).im ∧
      r.reAbs = iabs (phaseCenters160[idx.1]!).re ∧
      ((phaseCenters160[idx.1]!).re < 0 → negCandidateIndex r = idx.1) ∧
      (0 ≤ (phaseCenters160[idx.1]!).re → posCandidateIndex r = idx.1) := by native_decide

theorem signedRoot_imaginary_min_gap :
    ∀ q : Fin 79,
      (signedRootCenters80[q.1 + 1]!).im - (signedRootCenters80[q.1]!).im ≥ 40710441417 := by native_decide

theorem signedRoot_imaginary_gap :
    ∀ q r : Fin 80, q < r →
      (signedRootCenters80[q.1]!).im + 40710441417 ≤
        (signedRootCenters80[r.1]!).im := by native_decide +revert

theorem signedRoot_reAbs_large :
    ∀ q : Fin 80, 10000000000 < (signedRootCenters80[q.1]!).reAbs := by
  native_decide

/-- Finite exact completeness assertion for the optimized lookup, replayed over
all 160 certified centers. -/
theorem phaseNear_candidate_table_complete :
    ∀ idx : Fin 160,
      let q := candidateSignedRootQ[idx.1]!
      let r := signedRootCenters80[q.1]!
      r.im = (phaseCenters160[idx.1]!).im := by native_decide

/-- The lookup after its numerator sign has already been normalized. -/
def phaseNearPositive (nr ni d : Int) : Option Nat :=
  let qs := signedRootBracket ni d
  match candidateFromSigned qs.1 nr ni d with
  | some i => some i
  | none => if qs.2 = qs.1 then none else candidateFromSigned qs.2 nr ni d

theorem phaseNear_eq_positive_normalized (nr ni det : Int) :
    phaseNear nr ni det =
      phaseNearPositive (if det < 0 then -nr else nr)
        (if det < 0 then -ni else ni) (iabs det) := by
  rfl

private lemma signedRootGo_bounds
    (n d : Int) (lo hi : Nat)
    (hlo : lo < 80) (hhi : hi < 80) (hlt : lo < hi)
    (hlow : (signedRootCenters80.toArray[lo]!).im * d ≤ n)
    (hhigh : n < (signedRootCenters80.toArray[hi]!).im * d) :
    let p := signedRootBracket.go n d signedRootCenters80.toArray lo hi
    p < 79 ∧
      (signedRootCenters80.toArray[p]!).im * d ≤ n ∧
      n < (signedRootCenters80.toArray[p + 1]!).im * d := by
  refine signedRootBracket.go.induct n d signedRootCenters80.toArray
    (motive := fun lo hi =>
    lo < 80 → hi < 80 → lo < hi →
      (signedRootCenters80.toArray[lo]!).im * d ≤ n →
      n < (signedRootCenters80.toArray[hi]!).im * d →
      let p := signedRootBracket.go n d signedRootCenters80.toArray lo hi
      p < 79 ∧
        (signedRootCenters80.toArray[p]!).im * d ≤ n ∧
        n < (signedRootCenters80.toArray[p + 1]!).im * d) ?_ ?_ ?_ lo hi
      hlo hhi hlt hlow hhigh
  · intro lo hi hsep mid hmid ih hlo hhi hlt hlow hhigh
    have hmidlo : lo < (lo + hi) / 2 := by omega
    have hmidhi : (lo + hi) / 2 < hi := by omega
    rw [signedRootBracket.go.eq_1, dite_eq_left hsep, ite_eq_left hmid]
    exact ih (by omega) hhi hmidhi hmid hhigh
  · intro lo hi hsep mid hmid ih hlo hhi hlt hlow hhigh
    have hmidlo : lo < (lo + hi) / 2 := by omega
    have hmidhi : (lo + hi) / 2 < hi := by omega
    change ¬ ((signedRootCenters80.toArray[(lo + hi) / 2]!).im * d ≤ n) at hmid
    have hmidHigh : n <
        (signedRootCenters80.toArray[(lo + hi) / 2]!).im * d := lt_of_not_ge hmid
    rw [signedRootBracket.go.eq_1, dite_eq_left hsep, ite_eq_right hmid]
    exact ih hlo (by omega) hmidlo hlow hmidHigh
  · intro lo hi hsep hlo hhi hlt hlow hhigh
    have hhiEq : hi = lo + 1 := by omega
    have hlo79 : lo < 79 := by omega
    subst hi
    rw [signedRootBracket.go.eq_1, dite_eq_right hsep]
    exact And.intro hlo79 (And.intro hlow hhigh)

private lemma nearScaled_bounds
    (n d center : Int) (hnear : nearScaled n d center = true) :
    center * d - 10000000000 * d < n ∧
      n < center * d + 10000000000 * d := by
  unfold nearScaled at hnear
  have h := of_decide_eq_true hnear
  simp only [phaseCenterScale] at h
  unfold iabs at h
  split at h <;> omega

private lemma nearScaled_neg_false_of_pos
    (n d center : Int) (hd : 0 < d) (hcenter : 10000000000 < center)
    (hpos : nearScaled n d center = true) :
    nearScaled n d (-center) = false := by
  apply Bool.eq_false_iff.mpr
  intro hneg
  have hposBounds := nearScaled_bounds n d center hpos
  have hnegBounds := nearScaled_bounds n d (-center) hneg
  have hsep : 0 < (center - 10000000000) * d :=
    mul_pos (sub_pos.mpr hcenter) hd
  nlinarith

private lemma signedRootBracket_contains_near_root
    (q : Fin 80) (n d : Int) (hd : 0 < d)
    (hnear : nearScaled n d (signedRootCenters80[q.1]!).im = true) :
    q = (signedRootBracket n d).1 ∨ q = (signedRootBracket n d).2 := by
  have hnearBounds := nearScaled_bounds n d
    (signedRootCenters80[q.1]!).im hnear
  unfold signedRootBracket
  dsimp only
  split
  next hbelow =>
    rw [List.getElem!_toArray] at hbelow
    left
    apply Fin.ext
    simp only
    by_contra hq0
    have hqpos : (⟨0, by decide⟩ : Fin 80) < q := by
      change 0 < q.1
      omega
    have hgap := signedRoot_imaginary_gap ⟨0, by decide⟩ q hqpos
    have hgapd := mul_le_mul_of_nonneg_right hgap (le_of_lt hd)
    dsimp only at hgap hgapd
    nlinarith [hgapd]
  next hnotBelow =>
    split
    next habove =>
      rw [List.getElem!_toArray] at habove
      left
      apply Fin.ext
      simp only
      by_contra hq79
      have hqlt : q < (⟨79, by decide⟩ : Fin 80) := by
        simp only [Fin.lt_def]
        omega
      have hgap := signedRoot_imaginary_gap q ⟨79, by decide⟩ hqlt
      have hgapd := mul_le_mul_of_nonneg_right hgap (le_of_lt hd)
      dsimp only at hgap hgapd
      nlinarith [hgapd]
    next hnotAbove =>
      let p := signedRootBracket.go n d signedRootCenters80.toArray 0 79
      have hp := signedRootGo_bounds n d 0 79 (by omega) (by omega) (by omega)
        (le_of_not_gt hnotBelow) (lt_of_not_ge hnotAbove)
      change q = ⟨Nat.min p 78, _⟩ ∨ q = ⟨Nat.min p 78 + 1, _⟩
      have hp79 : p < 79 := hp.1
      have hp78 : p ≤ 78 := by omega
      have hmin : p.min 78 = p := Nat.min_eq_left hp78
      simp only [hmin]
      have hnotLeft : ¬ q.1 < p := by
        intro hqp
        let pf : Fin 80 := ⟨p, by omega⟩
        have hqpf : q < pf := by
          change q.1 < p
          exact hqp
        have hgap := signedRoot_imaginary_gap q pf hqpf
        have hgapd := mul_le_mul_of_nonneg_right hgap (le_of_lt hd)
        have hpLow := hp.2.1
        simp only [List.getElem!_toArray] at hpLow
        dsimp only [pf] at hgap hgapd
        nlinarith [hgapd]
      have hnotRight : ¬ p + 1 < q.1 := by
        intro hpq
        let pf : Fin 80 := ⟨p + 1, by omega⟩
        have hpfq : pf < q := by
          change p + 1 < q.1
          exact hpq
        have hgap := signedRoot_imaginary_gap pf q hpfq
        have hgapd := mul_le_mul_of_nonneg_right hgap (le_of_lt hd)
        have hpHigh := hp.2.2
        simp only [List.getElem!_toArray] at hpHigh
        dsimp only [pf] at hgap hgapd
        nlinarith [hgapd]
      by_cases hqp : q.1 = p
      · left
        exact Fin.ext hqp
      · right
        apply Fin.ext
        simp only
        omega

private lemma candidateFromSigned_candidate
    (idx : Fin 160) (nr ni d : Int) (hd : 0 < d)
    (hre : nearScaled nr d (phaseCenters160[idx.1]!).re = true)
    (him : nearScaled ni d (phaseCenters160[idx.1]!).im = true) :
    candidateFromSigned (candidateSignedRootQ[idx.1]!) nr ni d = some idx.1 := by
  let q := candidateSignedRootQ[idx.1]!
  let r := signedRootCenters80[q.1]!
  have hdata := candidateSignedRootQ_data_exact idx
  dsimp only at hdata
  change r.im = (phaseCenters160[idx.1]!).im ∧
      r.reAbs = iabs (phaseCenters160[idx.1]!).re ∧
      ((phaseCenters160[idx.1]!).re < 0 → negCandidateIndex r = idx.1) ∧
      (0 ≤ (phaseCenters160[idx.1]!).re → posCandidateIndex r = idx.1) at hdata
  rcases hdata with ⟨himEq, hreAbs, hnegIdx, hposIdx⟩
  have hnearIm : nearScaled ni d r.im = true := by
    rw [himEq]
    exact him
  by_cases hneg : (phaseCenters160[idx.1]!).re < 0
  · have hreEq : -r.reAbs = (phaseCenters160[idx.1]!).re := by
      rw [hreAbs]
      unfold iabs
      split <;> omega
    have hnearRe : nearScaled nr d (-r.reAbs) = true := by
      rw [hreEq]
      exact hre
    have hidx := hnegIdx hneg
    change (if nearScaled ni d r.im then
        if nearScaled nr d (-r.reAbs) then some (negCandidateIndex r)
        else if nearScaled nr d r.reAbs then some (posCandidateIndex r) else none
      else none) = some idx.1
    rw [ite_eq_left hnearIm, ite_eq_left hnearRe, hidx]
  · have hnonneg : 0 ≤ (phaseCenters160[idx.1]!).re := le_of_not_gt hneg
    have hreEq : r.reAbs = (phaseCenters160[idx.1]!).re := by
      rw [hreAbs]
      unfold iabs
      split <;> omega
    have hnearRe : nearScaled nr d r.reAbs = true := by
      rw [hreEq]
      exact hre
    have hlarge := signedRoot_reAbs_large q
    have hnearNeg := nearScaled_neg_false_of_pos nr d r.reAbs hd hlarge hnearRe
    have hidx := hposIdx hnonneg
    change (if nearScaled ni d r.im then
        if nearScaled nr d (-r.reAbs) then some (negCandidateIndex r)
        else if nearScaled nr d r.reAbs then some (posCandidateIndex r) else none
      else none) = some idx.1
    rw [ite_eq_left hnearIm, ite_eq_right (by simpa using hnearNeg),
      ite_eq_left hnearRe, hidx]

theorem phaseNearPositive_isSome_of_candidate
    (idx : Fin 160) (nr ni d : Int) (hd : 0 < d)
    (hre : nearScaled nr d (phaseCenters160[idx.1]!).re = true)
    (him : nearScaled ni d (phaseCenters160[idx.1]!).im = true) :
    (phaseNearPositive nr ni d).isSome = true := by
  let q := candidateSignedRootQ[idx.1]!
  have hdata := candidateSignedRootQ_data_exact idx
  dsimp only at hdata
  have hnearQ : nearScaled ni d (signedRootCenters80[q.1]!).im = true := by
    rw [hdata.1]
    exact him
  have hbracket := signedRootBracket_contains_near_root q ni d hd hnearQ
  have hcand := candidateFromSigned_candidate idx nr ni d hd hre him
  let qs := signedRootBracket ni d
  change q = qs.1 ∨ q = qs.2 at hbracket
  change (match candidateFromSigned qs.1 nr ni d with
    | some i => some i
    | none => if qs.2 = qs.1 then none else candidateFromSigned qs.2 nr ni d).isSome = true
  rcases hbracket with hfirst | hsecond
  · have hcandFirst : candidateFromSigned qs.1 nr ni d = some idx.1 := by
      rw [← hfirst]
      exact hcand
    rw [hcandFirst]
    rfl
  · cases hfirstResult : candidateFromSigned qs.1 nr ni d with
    | some i => rfl
    | none =>
      have hne : qs.2 ≠ qs.1 := by
        intro heq
        have hcandFirst : candidateFromSigned qs.1 nr ni d = some idx.1 := by
          rw [← heq, ← hsecond]
          exact hcand
        rw [hfirstResult] at hcandFirst
        cases hcandFirst
      rw [ite_eq_right hne]
      have hcandSecond : candidateFromSigned qs.2 nr ni d = some idx.1 := by
        rw [← hsecond]
        exact hcand
      rw [hcandSecond]
      rfl

end Biunimodular.F11
