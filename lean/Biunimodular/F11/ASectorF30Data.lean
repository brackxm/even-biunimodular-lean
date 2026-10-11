/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.FiniteFieldIrreducibilityCriterion
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-- The monic degree-thirty A phase-coordinate polynomial modulo two. -/
def aSectorG30mod2 : (ZMod 2)[X] := 1 + X^2 + X^3 + X^5 + X^7 + X^9 + X^10 + X^11 + X^12 + X^13 + X^17 + X^21 + X^22 + X^23 + X^25 + X^26 + X^27 + X^28 + X^30
def g30low : (ZMod 2)[X] := 1 + X^2 + X^3 + X^5 + X^7 + X^9 + X^10 + X^11 + X^12 + X^13 + X^17 + X^21 + X^22 + X^23 + X^25 + X^26 + X^27 + X^28

theorem g30mod2_monic : aSectorG30mod2.Monic := by
  have hlow : g30low.degree < 30 := by
    simp only [g30low]
    compute_degree; norm_num
  rw [show aSectorG30mod2 = X^30 + g30low by
    simp only [aSectorG30mod2, g30low]; ring]
  exact monic_X_pow_add hlow

theorem g30mod2_natDegree : aSectorG30mod2.natDegree = 30 := by
  have hlow : g30low.degree < 30 := by
    simp only [g30low]
    compute_degree; norm_num
  rw [show aSectorG30mod2 = X^30 + g30low by
    simp only [aSectorG30mod2, g30low]; ring]
  rw [natDegree_add_eq_left_of_degree_lt]
  · simp
  · simpa using hlow

def g30r0 : (ZMod 2)[X] := X
def g30r1 : (ZMod 2)[X] := X^2
def g30r2 : (ZMod 2)[X] := X^4
def g30r3 : (ZMod 2)[X] := X^8
def g30r4 : (ZMod 2)[X] := X^16
def g30r5 : (ZMod 2)[X] := 1 + X^3 + X^4 + X^10 + X^14 + X^15 + X^17 + X^19 + X^21 + X^22 + X^24 + X^26 + X^29
def g30r6 : (ZMod 2)[X] := 1 + X + X^2 + X^4 + X^5 + X^6 + X^8 + X^9 + X^11 + X^12 + X^13 + X^15 + X^16 + X^17 + X^19 + X^20 + X^21 + X^22 + X^23 + X^27 + X^28
def g30r7 : (ZMod 2)[X] := X + X^4 + X^6 + X^7 + X^10 + X^11 + X^17 + X^19 + X^22 + X^23 + X^24 + X^25
def g30r8 : (ZMod 2)[X] := 1 + X^3 + X^5 + X^8 + X^10 + X^13 + X^14 + X^15 + X^19 + X^21 + X^24 + X^29
def g30r9 : (ZMod 2)[X] := 1 + X^2 + X^3 + X^4 + X^5 + X^6 + X^7 + X^8 + X^9 + X^11 + X^13 + X^14 + X^19 + X^24 + X^25 + X^26 + X^28 + X^29
def g30r10 : (ZMod 2)[X] := 1 + X + X^2 + X^4 + X^7 + X^10 + X^11 + X^14 + X^15 + X^16 + X^17 + X^18 + X^19 + X^22 + X^27 + X^28
def g30r11 : (ZMod 2)[X] := 1 + X + X^3 + X^5 + X^7 + X^9 + X^10 + X^12 + X^13 + X^15 + X^16 + X^17 + X^20 + X^22 + X^23 + X^25 + X^26 + X^29
def g30r12 : (ZMod 2)[X] := 1 + X + X^2 + X^3 + X^5 + X^6 + X^8 + X^10 + X^12 + X^14 + X^16 + X^17 + X^20 + X^25 + X^27 + X^28 + X^29
def g30r13 : (ZMod 2)[X] := X^3 + X^4 + X^8 + X^9 + X^13 + X^15 + X^16 + X^18 + X^20 + X^23 + X^25 + X^28
def g30r14 : (ZMod 2)[X] := X + X^2 + X^3 + X^8 + X^11 + X^12 + X^13 + X^15 + X^18 + X^19 + X^21 + X^22 + X^23 + X^29
def g30r15 : (ZMod 2)[X] := 1 + X^3 + X^5 + X^6 + X^9 + X^10 + X^11 + X^12 + X^13 + X^14 + X^18 + X^20 + X^23 + X^24 + X^25 + X^27 + X^28
def g30r16 : (ZMod 2)[X] := X^3 + X^5 + X^7 + X^12 + X^13 + X^15 + X^16 + X^17 + X^18 + X^20 + X^21 + X^22 + X^23 + X^27 + X^28 + X^29
def g30r17 : (ZMod 2)[X] := X + X^5 + X^6 + X^7 + X^8 + X^9 + X^11 + X^12 + X^13 + X^14 + X^15 + X^18 + X^19 + X^20 + X^24 + X^25 + X^28 + X^29
def g30r18 : (ZMod 2)[X] := 1 + X + X^2 + X^4 + X^6 + X^8 + X^9 + X^14 + X^19 + X^20 + X^23 + X^26
def g30r19 : (ZMod 2)[X] := 1 + X + X^2 + X^7 + X^8 + X^10 + X^11 + X^12 + X^13 + X^16 + X^19 + X^21 + X^23 + X^25 + X^27
def g30r20 : (ZMod 2)[X] := X^2 + X^4 + X^6 + X^7 + X^12 + X^16 + X^17 + X^18 + X^19 + X^21 + X^23 + X^24
def g30r21 : (ZMod 2)[X] := 1 + X + X^3 + X^6 + X^9 + X^11 + X^12 + X^14 + X^16 + X^18 + X^19 + X^23 + X^26
def g30r22 : (ZMod 2)[X] := X + X^5 + X^7 + X^10 + X^11 + X^13 + X^16 + X^17 + X^19 + X^21 + X^24 + X^25 + X^28 + X^29
def g30r23 : (ZMod 2)[X] := 1 + X^3 + X^7 + X^8 + X^9 + X^10 + X^13 + X^14 + X^16 + X^17 + X^23 + X^26 + X^27 + X^28
def g30r24 : (ZMod 2)[X] := X^2 + X^3 + X^6 + X^8 + X^10 + X^11 + X^13 + X^15 + X^20 + X^21 + X^22 + X^25 + X^26 + X^29
def g30r25 : (ZMod 2)[X] := X^3 + X^6 + X^9 + X^12 + X^15 + X^17 + X^18 + X^20 + X^21 + X^22 + X^23 + X^24 + X^25 + X^27 + X^28
def g30r26 : (ZMod 2)[X] := X + X^5 + X^6 + X^7 + X^10 + X^11 + X^14 + X^16 + X^17 + X^19 + X^21 + X^22
def g30r27 : (ZMod 2)[X] := X + X^2 + X^3 + X^4 + X^6 + X^7 + X^9 + X^10 + X^11 + X^14 + X^16 + X^20 + X^27 + X^29
def g30r28 : (ZMod 2)[X] := X^2 + X^3 + X^4 + X^7 + X^12 + X^14 + X^17 + X^20 + X^23 + X^24 + X^25 + X^28
def g30r29 : (ZMod 2)[X] := X^3 + X^4 + X^6 + X^7 + X^9 + X^10 + X^11 + X^13 + X^14 + X^15 + X^17 + X^18 + X^21 + X^26 + X^27 + X^29
def g30r30 : (ZMod 2)[X] := X
def g30q0 : (ZMod 2)[X] := 0
def g30q1 : (ZMod 2)[X] := 0
def g30q2 : (ZMod 2)[X] := 0
def g30q3 : (ZMod 2)[X] := 0
def g30q4 : (ZMod 2)[X] := 1 + X^2
def g30q5 : (ZMod 2)[X] := X + X^2 + X^3 + X^4 + X^5 + X^6 + X^7 + X^9 + X^12 + X^15 + X^16 + X^17 + X^18 + X^22 + X^23 + X^25 + X^26 + X^28
def g30q6 : (ZMod 2)[X] := 1 + X + X^4 + X^5 + X^6 + X^9 + X^10 + X^13 + X^15 + X^17 + X^18 + X^19 + X^22 + X^23 + X^26
def g30q7 : (ZMod 2)[X] := 1 + X^7 + X^10 + X^11 + X^17 + X^20
def g30q8 : (ZMod 2)[X] := X^2 + X^3 + X^5 + X^6 + X^7 + X^11 + X^13 + X^15 + X^16 + X^18 + X^19 + X^20 + X^23 + X^25 + X^26 + X^28
def g30q9 : (ZMod 2)[X] := X + X^2 + X^3 + X^6 + X^14 + X^16 + X^17 + X^18 + X^20 + X^21 + X^22 + X^24 + X^25 + X^28
def g30q10 : (ZMod 2)[X] := X + X^2 + X^4 + X^7 + X^10 + X^11 + X^12 + X^14 + X^15 + X^16 + X^17 + X^18 + X^19 + X^22 + X^23 + X^26
def g30q11 : (ZMod 2)[X] := X + X^4 + X^5 + X^8 + X^9 + X^10 + X^12 + X^14 + X^15 + X^16 + X^18 + X^20 + X^22 + X^23 + X^25 + X^26 + X^28
def g30q12 : (ZMod 2)[X] := 1 + X^5 + X^6 + X^8 + X^9 + X^16 + X^22 + X^25 + X^28
def g30q13 : (ZMod 2)[X] := X + X^2 + X^5 + X^9 + X^12 + X^13 + X^14 + X^15 + X^16 + X^20 + X^21 + X^23 + X^24 + X^26
def g30q14 : (ZMod 2)[X] := 1 + X^4 + X^6 + X^8 + X^10 + X^11 + X^12 + X^13 + X^16 + X^19 + X^20 + X^23 + X^25 + X^26 + X^28
def g30q15 : (ZMod 2)[X] := 1 + X^2 + X^4 + X^5 + X^7 + X^8 + X^10 + X^12 + X^14 + X^15 + X^16 + X^18 + X^19 + X^20 + X^22 + X^23 + X^26
def g30q16 : (ZMod 2)[X] := X + X^3 + X^4 + X^6 + X^9 + X^10 + X^11 + X^12 + X^13 + X^15 + X^17 + X^18 + X^20 + X^22 + X^25 + X^28
def g30q17 : (ZMod 2)[X] := 1 + X + X^2 + X^4 + X^6 + X^7 + X^8 + X^10 + X^13 + X^16 + X^18 + X^19 + X^21 + X^24 + X^25 + X^28
def g30q18 : (ZMod 2)[X] := X + X^3 + X^5 + X^8 + X^10 + X^11 + X^16 + X^17 + X^19 + X^20 + X^22
def g30q19 : (ZMod 2)[X] := 1 + X^2 + X^3 + X^4 + X^5 + X^6 + X^7 + X^8 + X^9 + X^10 + X^13 + X^14 + X^17 + X^18 + X^19 + X^20 + X^21 + X^22 + X^24
def g30q20 : (ZMod 2)[X] := 1 + X + X^2 + X^3 + X^4 + X^5 + X^11 + X^12 + X^14 + X^15 + X^18
def g30q21 : (ZMod 2)[X] := 1 + X + X^4 + X^6 + X^7 + X^11 + X^16 + X^17 + X^19 + X^20 + X^22
def g30q22 : (ZMod 2)[X] := 1 + X^5 + X^7 + X^9 + X^10 + X^12 + X^13 + X^16 + X^18 + X^19 + X^21 + X^24 + X^25 + X^28
def g30q23 : (ZMod 2)[X] := 1 + X^5 + X^9 + X^10 + X^11 + X^15 + X^18 + X^20 + X^23 + X^26
def g30q24 : (ZMod 2)[X] := X^3 + X^4 + X^5 + X^11 + X^13 + X^15 + X^18 + X^20 + X^22 + X^23 + X^25 + X^26 + X^28
def g30q25 : (ZMod 2)[X] := X + X^3 + X^4 + X^6 + X^8 + X^11 + X^12 + X^15 + X^16 + X^18 + X^19 + X^20 + X^22 + X^23 + X^26
def g30q26 : (ZMod 2)[X] := X + X^7 + X^8 + X^10 + X^11 + X^14
def g30q27 : (ZMod 2)[X] := X^3 + X^5 + X^8 + X^10 + X^11 + X^12 + X^15 + X^16 + X^20 + X^21 + X^22 + X^23 + X^24 + X^25 + X^26 + X^28
def g30q28 : (ZMod 2)[X] := X^3 + X^5 + X^6 + X^10 + X^12 + X^14 + X^18 + X^20 + X^21 + X^23 + X^24 + X^26
def g30q29 : (ZMod 2)[X] := X + X^3 + X^4 + X^5 + X^9 + X^10 + X^11 + X^13 + X^14 + X^15 + X^16 + X^17 + X^19 + X^21 + X^23 + X^24 + X^25 + X^26 + X^28


end
end Biunimodular.F11
