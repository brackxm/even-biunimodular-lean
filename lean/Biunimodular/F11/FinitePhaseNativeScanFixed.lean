/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.FixedPointPhaseCenterData
public import Biunimodular.F11.FinitePhaseScanDataReconstructed
public meta import Biunimodular.F11.ProofTactics
public meta import Biunimodular.F11.FixedPointPhaseCenterData
public meta import Biunimodular.F11.FinitePhaseScanDataReconstructed

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11
deriving instance Inhabited for PhaseCenter
deriving instance Inhabited for SignedRootCenter

def iabs (x : Int) : Int := if x < 0 then -x else x

def det3i (a b c d e f g h i : Int) : Int :=
  a * (e*i - f*h) - b * (d*i - f*g) + c * (d*h - e*g)

def det4i
    (a00 a01 a02 a03 a10 a11 a12 a13 a20 a21 a22 a23 a30 a31 a32 a33 : Int) : Int :=
  a00 * det3i a11 a12 a13 a21 a22 a23 a31 a32 a33
  - a01 * det3i a10 a12 a13 a20 a22 a23 a30 a32 a33
  + a02 * det3i a10 a11 a13 a20 a21 a23 a30 a31 a33
  - a03 * det3i a10 a11 a12 a20 a21 a22 a30 a31 a32

structure CenterTailSystem where
  det : Int
  ng : Int
  nh : Int
  nj : Int
  nk : Int
deriving Repr, DecidableEq

def centerTailSystem (ia ic ie : Nat) : CenterTailSystem :=
  let A := (phaseCenters160[ia]!).re; let B := (phaseCenters160[ia]!).im
  let C := (phaseCenters160[ic]!).re; let D := (phaseCenters160[ic]!).im
  let E := (phaseCenters160[ie]!).re; let F := (phaseCenters160[ie]!).im
  let S := phaseCenterScale
  let m00 := E-C; let m01 := F-D; let m02 := -E; let m03 := -F
  let m10 := A; let m11 := B; let m12 := C+E; let m13 := D+F
  let m20 := S+E; let m21 := F; let m22 := A+C; let m23 := B+D
  let m30 := A+C; let m31 := B+D; let m32 := S+A; let m33 := B
  let r0 := -((A-C)*S + A*C+B*D+C*E+D*F-A*E-B*F)
  let r1 := -(E*S + A*C+B*D + S*S/2)
  let r2 := -(A*E+B*F + S*S/2)
  let r3 := -(C*E+D*F + S*S/2)
  let Δ := det4i m00 m01 m02 m03 m10 m11 m12 m13 m20 m21 m22 m23 m30 m31 m32 m33
  let ng := det4i r0 m01 m02 m03 r1 m11 m12 m13 r2 m21 m22 m23 r3 m31 m32 m33
  let nh := det4i m00 r0 m02 m03 m10 r1 m12 m13 m20 r2 m22 m23 m30 r3 m32 m33
  let nj := det4i m00 m01 r0 m03 m10 m11 r1 m13 m20 m21 r2 m23 m30 m31 r3 m33
  let nk := det4i m00 m01 m02 r0 m10 m11 m12 r1 m20 m21 m22 r2 m30 m31 m32 r3
  ⟨Δ,ng,nh,nj,nk⟩

def centerDetThreshold : Int := phaseCenterScale^4 / 1000000

def exceptionalTriple (ia ic ie : Nat) : Bool :=
  exceptionalCandidateTriples.any fun t => match t with | (a,c,e) => a == ia && c == ic && e == ie

/-- Lower-bound bracket in the sorted list of 80 signed imaginary centers. -/
def signedRootBracket (n d : Int) : Fin 80 × Fin 80 :=
  let vals := signedRootCenters80.toArray
  let rec go (lo hi : Nat) : Nat :=
    if h : lo + 1 < hi then
      let mid := (lo + hi) / 2
      if (vals[mid]!).im * d ≤ n then go mid hi else go lo mid
    else lo
  if n < (vals[0]!).im * d then (⟨0,by decide⟩,⟨0,by decide⟩)
  else if (vals[79]!).im * d ≤ n then (⟨79,by decide⟩,⟨79,by decide⟩)
  else
    let q := Nat.min (go 0 79) 78
    have hq : q < 79 := lt_of_le_of_lt (Nat.min_le_right _ _) (by norm_num)
    (⟨q,by omega⟩,⟨q+1,by omega⟩)

def nearScaled (n d center : Int) : Bool :=
  decide ((10000 : Int) * iabs (n - center*d) < phaseCenterScale*d)

def negCandidateIndex (r : SignedRootCenter) : Nat := 4*r.rootIndex + (if r.imPositive then 1 else 0)
def posCandidateIndex (r : SignedRootCenter) : Nat := 4*r.rootIndex + (if r.imPositive then 3 else 2)

def candidateFromSigned (q : Fin 80) (nr ni d : Int) : Option Nat :=
  let r := signedRootCenters80[q.1]!
  if nearScaled ni d r.im then
    if nearScaled nr d (-r.reAbs) then some (negCandidateIndex r)
    else if nearScaled nr d r.reAbs then some (posCandidateIndex r)
    else none
  else none

def phaseNear (nr ni det : Int) : Option Nat :=
  let d := iabs det
  let nr' := if det < 0 then -nr else nr
  let ni' := if det < 0 then -ni else ni
  let qs := signedRootBracket ni' d
  match candidateFromSigned qs.1 nr' ni' d with
  | some i => some i
  | none => if qs.2 = qs.1 then none else candidateFromSigned qs.2 nr' ni' d

def scanCenterTriple (ia ic ie : Nat) : Option (Nat × Nat) :=
  if exceptionalTriple ia ic ie then none else
  let s := centerTailSystem ia ic ie
  if iabs s.det < centerDetThreshold then none else
  match phaseNear s.ng s.nh s.det, phaseNear s.nj s.nk s.det with
  | some ig, some ij => some (ig,ij)
  | _, _ => none

def scannedCandidateQuintuples : List (Nat × Nat × Nat × Nat × Nat) :=
  (List.range 160).flatMap fun ia =>
    (List.range 160).flatMap fun ic =>
      (List.range 160).filterMap fun ie =>
        match scanCenterTriple ia ic ie with
        | some (ig,ij) => some (ia,ic,ie,ig,ij)
        | none => none

theorem scannedCandidateQuintuples_eq_accepted :
    scannedCandidateQuintuples = acceptedCandidateQuintuples := by native_decide

theorem center_det_margin_all :
    ∀ ia ic ie : Fin 160,
      exceptionalTriple ia.1 ic.1 ie.1 = false →
      centerDetThreshold ≤ iabs (centerTailSystem ia.1 ic.1 ie.1).det := by native_decide

theorem signedRoot_center_matches :
    ∀ q : Fin 80,
      let r := signedRootCenters80[q.1]!
      negCandidateIndex r < 160 ∧ posCandidateIndex r < 160 ∧
      (phaseCenters160[negCandidateIndex r]!).im = r.im ∧
      (phaseCenters160[negCandidateIndex r]!).re = -r.reAbs ∧
      (phaseCenters160[posCandidateIndex r]!).im = r.im ∧
      (phaseCenters160[posCandidateIndex r]!).re = r.reAbs := by native_decide

lemma candidateFromSigned_sound
    {q : Fin 80} {nr ni d : Int} {idx : Nat}
    (h : candidateFromSigned q nr ni d = some idx) :
    idx < 160 ∧ nearScaled ni d (phaseCenters160[idx]!).im = true ∧
      nearScaled nr d (phaseCenters160[idx]!).re = true := by
  let r := signedRootCenters80[q.1]!
  have hm := signedRoot_center_matches q
  dsimp only at hm
  rcases hm with ⟨hneglt,hposlt,hnegim,hnegre,hposim,hposre⟩
  change (if nearScaled ni d r.im then
      if nearScaled nr d (-r.reAbs) then some (negCandidateIndex r)
      else if nearScaled nr d r.reAbs then some (posCandidateIndex r)
      else none
    else none) = some idx at h
  split at h
  next him =>
    split at h
    next hneg =>
      cases h
      constructor
      · exact hneglt
      constructor
      · rw [hnegim]
        exact him
      · rw [hnegre]
        exact hneg
    next hneg =>
      split at h
      next hpos =>
        cases h
        constructor
        · exact hposlt
        constructor
        · rw [hposim]
          exact him
        · rw [hposre]
          exact hpos
      next hpos => cases h
  next him => cases h

lemma phaseNear_sound
    {nr ni det : Int} {idx : Nat}
    (h : phaseNear nr ni det = some idx) :
    let d := iabs det
    let nr' := if det < 0 then -nr else nr
    let ni' := if det < 0 then -ni else ni
    idx < 160 ∧ nearScaled ni' d (phaseCenters160[idx]!).im = true ∧
      nearScaled nr' d (phaseCenters160[idx]!).re = true := by
  dsimp
  unfold phaseNear at h
  dsimp only at h
  let qs := signedRootBracket (if det < 0 then -ni else ni) (iabs det)
  generalize hfirst : candidateFromSigned qs.1 (if det < 0 then -nr else nr)
      (if det < 0 then -ni else ni) (iabs det) = first at h
  cases first with
  | some qidx =>
      cases h
      exact candidateFromSigned_sound hfirst
  | none =>
      by_cases heq : qs.2 = qs.1
      · rw [ite_eq_left heq] at h
        cases h
      · rw [ite_eq_right heq] at h
        exact candidateFromSigned_sound h

lemma scanCenterTriple_sound
    {ia ic ie ig ij : Nat}
    (h : scanCenterTriple ia ic ie = some (ig, ij)) :
    exceptionalTriple ia ic ie = false ∧
    centerDetThreshold ≤ iabs (centerTailSystem ia ic ie).det ∧
    ig < 160 ∧ ij < 160 ∧
    let s := centerTailSystem ia ic ie
    let d := iabs s.det
    let sg := if s.det < 0 then -s.ng else s.ng
    let sh := if s.det < 0 then -s.nh else s.nh
    let sj := if s.det < 0 then -s.nj else s.nj
    let sk := if s.det < 0 then -s.nk else s.nk
    nearScaled sh d (phaseCenters160[ig]!).im = true ∧
    nearScaled sg d (phaseCenters160[ig]!).re = true ∧
    nearScaled sk d (phaseCenters160[ij]!).im = true ∧
    nearScaled sj d (phaseCenters160[ij]!).re = true := by
  unfold scanCenterTriple at h
  split at h
  next hex => cases h
  next hex =>
    have hexf : exceptionalTriple ia ic ie = false := Bool.eq_false_of_not_eq_true hex
    let s := centerTailSystem ia ic ie
    change (if iabs s.det < centerDetThreshold then none else
      match phaseNear s.ng s.nh s.det, phaseNear s.nj s.nk s.det with
      | some gi, some ji => some (gi, ji)
      | _, _ => none) = some (ig, ij) at h
    split at h
    next hdet => cases h
    next hdet =>
      have hmargin : centerDetThreshold ≤ iabs (centerTailSystem ia ic ie).det := by
        simpa [s] using (le_of_not_gt hdet)
      generalize hg : phaseNear s.ng s.nh s.det = og at h
      generalize hj : phaseNear s.nj s.nk s.det = oj at h
      cases og with
      | none => cases h
      | some gi =>
          cases oj with
          | none => cases h
          | some ji =>
              cases h
              have hgs := phaseNear_sound hg
              have hjs := phaseNear_sound hj
              dsimp at hgs hjs
              exact ⟨hexf,hmargin,hgs.1,hjs.1,hgs.2.1,hgs.2.2,hjs.2.1,hjs.2.2⟩

/-- Any successful individual scan is one of the quintuples in the certified full scan. -/
theorem scan_result_is_accepted :
    ∀ ia ic ie : Fin 160,
      match scanCenterTriple ia.1 ic.1 ie.1 with
      | none => True
      | some (ig,ij) => (ia.1,ic.1,ie.1,ig,ij) ∈ acceptedCandidateQuintuples := by
  intro ia ic ie
  cases hscan : scanCenterTriple ia.1 ic.1 ie.1 with
  | none => trivial
  | some p =>
      rcases p with ⟨ig,ij⟩
      rw [← scannedCandidateQuintuples_eq_accepted]
      unfold scannedCandidateQuintuples
      apply List.mem_flatMap.mpr
      refine ⟨ia.1, by simp [ia.isLt], ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨ic.1, by simp [ic.isLt], ?_⟩
      apply List.mem_filterMap.mpr
      refine ⟨ie.1, by simp [ie.isLt], ?_⟩
      simp [hscan]

end Biunimodular.F11
