/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorF30Data

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

theorem g30step0 : aSectorG30mod2 ∣ g30r0^2 - g30r1 := by
  refine ⟨g30q0, ?_⟩
  simp only [aSectorG30mod2, g30r0, g30r1, g30q0]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step1 : aSectorG30mod2 ∣ g30r1^2 - g30r2 := by
  refine ⟨g30q1, ?_⟩
  simp only [aSectorG30mod2, g30r1, g30r2, g30q1]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step2 : aSectorG30mod2 ∣ g30r2^2 - g30r3 := by
  refine ⟨g30q2, ?_⟩
  simp only [aSectorG30mod2, g30r2, g30r3, g30q2]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step3 : aSectorG30mod2 ∣ g30r3^2 - g30r4 := by
  refine ⟨g30q3, ?_⟩
  simp only [aSectorG30mod2, g30r3, g30r4, g30q3]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step4 : aSectorG30mod2 ∣ g30r4^2 - g30r5 := by
  refine ⟨g30q4, ?_⟩
  simp only [aSectorG30mod2, g30r4, g30r5, g30q4]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step5 : aSectorG30mod2 ∣ g30r5^2 - g30r6 := by
  refine ⟨g30q5, ?_⟩
  simp only [aSectorG30mod2, g30r5, g30r6, g30q5]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step6 : aSectorG30mod2 ∣ g30r6^2 - g30r7 := by
  refine ⟨g30q6, ?_⟩
  simp only [aSectorG30mod2, g30r6, g30r7, g30q6]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step7 : aSectorG30mod2 ∣ g30r7^2 - g30r8 := by
  refine ⟨g30q7, ?_⟩
  simp only [aSectorG30mod2, g30r7, g30r8, g30q7]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step8 : aSectorG30mod2 ∣ g30r8^2 - g30r9 := by
  refine ⟨g30q8, ?_⟩
  simp only [aSectorG30mod2, g30r8, g30r9, g30q8]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step9 : aSectorG30mod2 ∣ g30r9^2 - g30r10 := by
  refine ⟨g30q9, ?_⟩
  simp only [aSectorG30mod2, g30r9, g30r10, g30q9]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem g30Frob0 : aSectorG30mod2 ∣ frobeniusIter 2 0 - g30r0 := by
  simp [g30r0, frobeniusIter]
theorem g30Frob1 : aSectorG30mod2 ∣ frobeniusIter 2 1 - g30r1 :=
  frobeniusIter_dvd_next g30Frob0 g30step0
theorem g30Frob2 : aSectorG30mod2 ∣ frobeniusIter 2 2 - g30r2 :=
  frobeniusIter_dvd_next g30Frob1 g30step1
theorem g30Frob3 : aSectorG30mod2 ∣ frobeniusIter 2 3 - g30r3 :=
  frobeniusIter_dvd_next g30Frob2 g30step2
theorem g30Frob4 : aSectorG30mod2 ∣ frobeniusIter 2 4 - g30r4 :=
  frobeniusIter_dvd_next g30Frob3 g30step3
theorem g30Frob5 : aSectorG30mod2 ∣ frobeniusIter 2 5 - g30r5 :=
  frobeniusIter_dvd_next g30Frob4 g30step4
theorem g30Frob6 : aSectorG30mod2 ∣ frobeniusIter 2 6 - g30r6 :=
  frobeniusIter_dvd_next g30Frob5 g30step5
theorem g30Frob7 : aSectorG30mod2 ∣ frobeniusIter 2 7 - g30r7 :=
  frobeniusIter_dvd_next g30Frob6 g30step6
theorem g30Frob8 : aSectorG30mod2 ∣ frobeniusIter 2 8 - g30r8 :=
  frobeniusIter_dvd_next g30Frob7 g30step7
theorem g30Frob9 : aSectorG30mod2 ∣ frobeniusIter 2 9 - g30r9 :=
  frobeniusIter_dvd_next g30Frob8 g30step8
theorem g30Frob10 : aSectorG30mod2 ∣ frobeniusIter 2 10 - g30r10 :=
  frobeniusIter_dvd_next g30Frob9 g30step9

end
end Biunimodular.F11
