/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorF30Frobenius2

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

theorem g30step20 : aSectorG30mod2 ∣ g30r20^2 - g30r21 := by
  refine ⟨g30q20, ?_⟩
  simp only [aSectorG30mod2, g30r20, g30r21, g30q20]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step21 : aSectorG30mod2 ∣ g30r21^2 - g30r22 := by
  refine ⟨g30q21, ?_⟩
  simp only [aSectorG30mod2, g30r21, g30r22, g30q21]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step22 : aSectorG30mod2 ∣ g30r22^2 - g30r23 := by
  refine ⟨g30q22, ?_⟩
  simp only [aSectorG30mod2, g30r22, g30r23, g30q22]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step23 : aSectorG30mod2 ∣ g30r23^2 - g30r24 := by
  refine ⟨g30q23, ?_⟩
  simp only [aSectorG30mod2, g30r23, g30r24, g30q23]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step24 : aSectorG30mod2 ∣ g30r24^2 - g30r25 := by
  refine ⟨g30q24, ?_⟩
  simp only [aSectorG30mod2, g30r24, g30r25, g30q24]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step25 : aSectorG30mod2 ∣ g30r25^2 - g30r26 := by
  refine ⟨g30q25, ?_⟩
  simp only [aSectorG30mod2, g30r25, g30r26, g30q25]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step26 : aSectorG30mod2 ∣ g30r26^2 - g30r27 := by
  refine ⟨g30q26, ?_⟩
  simp only [aSectorG30mod2, g30r26, g30r27, g30q26]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step27 : aSectorG30mod2 ∣ g30r27^2 - g30r28 := by
  refine ⟨g30q27, ?_⟩
  simp only [aSectorG30mod2, g30r27, g30r28, g30q27]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step28 : aSectorG30mod2 ∣ g30r28^2 - g30r29 := by
  refine ⟨g30q28, ?_⟩
  simp only [aSectorG30mod2, g30r28, g30r29, g30q28]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30step29 : aSectorG30mod2 ∣ g30r29^2 - g30r30 := by
  refine ⟨g30q29, ?_⟩
  simp only [aSectorG30mod2, g30r29, g30r30, g30q29]
  reduce_mod_char
  ring_nf
  reduce_mod_char

theorem g30Frob21 : aSectorG30mod2 ∣ frobeniusIter 2 21 - g30r21 :=
  frobeniusIter_dvd_next g30Frob20 g30step20
theorem g30Frob22 : aSectorG30mod2 ∣ frobeniusIter 2 22 - g30r22 :=
  frobeniusIter_dvd_next g30Frob21 g30step21
theorem g30Frob23 : aSectorG30mod2 ∣ frobeniusIter 2 23 - g30r23 :=
  frobeniusIter_dvd_next g30Frob22 g30step22
theorem g30Frob24 : aSectorG30mod2 ∣ frobeniusIter 2 24 - g30r24 :=
  frobeniusIter_dvd_next g30Frob23 g30step23
theorem g30Frob25 : aSectorG30mod2 ∣ frobeniusIter 2 25 - g30r25 :=
  frobeniusIter_dvd_next g30Frob24 g30step24
theorem g30Frob26 : aSectorG30mod2 ∣ frobeniusIter 2 26 - g30r26 :=
  frobeniusIter_dvd_next g30Frob25 g30step25
theorem g30Frob27 : aSectorG30mod2 ∣ frobeniusIter 2 27 - g30r27 :=
  frobeniusIter_dvd_next g30Frob26 g30step26
theorem g30Frob28 : aSectorG30mod2 ∣ frobeniusIter 2 28 - g30r28 :=
  frobeniusIter_dvd_next g30Frob27 g30step27
theorem g30Frob29 : aSectorG30mod2 ∣ frobeniusIter 2 29 - g30r29 :=
  frobeniusIter_dvd_next g30Frob28 g30step28
theorem g30Frob30 : aSectorG30mod2 ∣ frobeniusIter 2 30 - g30r30 :=
  frobeniusIter_dvd_next g30Frob29 g30step29

end
end Biunimodular.F11
