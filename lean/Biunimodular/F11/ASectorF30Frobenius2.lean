/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorF30Frobenius1

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

theorem g30step10 : aSectorG30mod2 ∣ g30r10^2 - g30r11 := by
  refine ⟨g30q10, ?_⟩
  simp only [aSectorG30mod2, g30r10, g30r11, g30q10]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step11 : aSectorG30mod2 ∣ g30r11^2 - g30r12 := by
  refine ⟨g30q11, ?_⟩
  simp only [aSectorG30mod2, g30r11, g30r12, g30q11]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step12 : aSectorG30mod2 ∣ g30r12^2 - g30r13 := by
  refine ⟨g30q12, ?_⟩
  simp only [aSectorG30mod2, g30r12, g30r13, g30q12]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step13 : aSectorG30mod2 ∣ g30r13^2 - g30r14 := by
  refine ⟨g30q13, ?_⟩
  simp only [aSectorG30mod2, g30r13, g30r14, g30q13]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step14 : aSectorG30mod2 ∣ g30r14^2 - g30r15 := by
  refine ⟨g30q14, ?_⟩
  simp only [aSectorG30mod2, g30r14, g30r15, g30q14]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step15 : aSectorG30mod2 ∣ g30r15^2 - g30r16 := by
  refine ⟨g30q15, ?_⟩
  simp only [aSectorG30mod2, g30r15, g30r16, g30q15]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step16 : aSectorG30mod2 ∣ g30r16^2 - g30r17 := by
  refine ⟨g30q16, ?_⟩
  simp only [aSectorG30mod2, g30r16, g30r17, g30q16]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step17 : aSectorG30mod2 ∣ g30r17^2 - g30r18 := by
  refine ⟨g30q17, ?_⟩
  simp only [aSectorG30mod2, g30r17, g30r18, g30q17]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step18 : aSectorG30mod2 ∣ g30r18^2 - g30r19 := by
  refine ⟨g30q18, ?_⟩
  simp only [aSectorG30mod2, g30r18, g30r19, g30q18]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step19 : aSectorG30mod2 ∣ g30r19^2 - g30r20 := by
  refine ⟨g30q19, ?_⟩
  simp only [aSectorG30mod2, g30r19, g30r20, g30q19]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem g30Frob11 : aSectorG30mod2 ∣ frobeniusIter 2 11 - g30r11 :=
  frobeniusIter_dvd_next g30Frob10 g30step10
theorem g30Frob12 : aSectorG30mod2 ∣ frobeniusIter 2 12 - g30r12 :=
  frobeniusIter_dvd_next g30Frob11 g30step11
theorem g30Frob13 : aSectorG30mod2 ∣ frobeniusIter 2 13 - g30r13 :=
  frobeniusIter_dvd_next g30Frob12 g30step12
theorem g30Frob14 : aSectorG30mod2 ∣ frobeniusIter 2 14 - g30r14 :=
  frobeniusIter_dvd_next g30Frob13 g30step13
theorem g30Frob15 : aSectorG30mod2 ∣ frobeniusIter 2 15 - g30r15 :=
  frobeniusIter_dvd_next g30Frob14 g30step14
theorem g30Frob16 : aSectorG30mod2 ∣ frobeniusIter 2 16 - g30r16 :=
  frobeniusIter_dvd_next g30Frob15 g30step15
theorem g30Frob17 : aSectorG30mod2 ∣ frobeniusIter 2 17 - g30r17 :=
  frobeniusIter_dvd_next g30Frob16 g30step16
theorem g30Frob18 : aSectorG30mod2 ∣ frobeniusIter 2 18 - g30r18 :=
  frobeniusIter_dvd_next g30Frob17 g30step17
theorem g30Frob19 : aSectorG30mod2 ∣ frobeniusIter 2 19 - g30r19 :=
  frobeniusIter_dvd_next g30Frob18 g30step18
theorem g30Frob20 : aSectorG30mod2 ∣ frobeniusIter 2 20 - g30r20 :=
  frobeniusIter_dvd_next g30Frob19 g30step19

end
end Biunimodular.F11
