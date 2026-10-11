/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorF30Frobenius3

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

theorem g30copSmall1 : IsCoprime aSectorG30mod2 (g30r1 - X) := by
  refine ⟨(1 : (ZMod 2)[X]), (X + X^4 + X^5 + X^8 + X^10 + X^12 + X^13 + X^14 + X^15 + X^20 + X^22 + X^23 + X^25 + X^27 + X^28 : (ZMod 2)[X]), ?_⟩
  simp only [aSectorG30mod2, g30r1]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30copSmall2 : IsCoprime aSectorG30mod2 (g30r2 - X) := by
  refine ⟨(1 : (ZMod 2)[X]), (X + X^2 + X^5 + X^6 + X^10 + X^11 + X^12 + X^13 + X^14 + X^15 + X^17 + X^18 + X^22 + X^24 + X^26 : (ZMod 2)[X]), ?_⟩
  simp only [aSectorG30mod2, g30r2]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30copSmall3 : IsCoprime aSectorG30mod2 (g30r3 - X) := by
  refine ⟨(1 + X^2 + X^3 + X^4 + X^5 + X^6 + X^7 : (ZMod 2)[X]), (X^5 + X^6 + X^7 + X^8 + X^11 + X^16 + X^17 + X^22 + X^24 + X^26 + X^28 + X^29 : (ZMod 2)[X]), ?_⟩
  simp only [aSectorG30mod2, g30r3]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30copSmall5 : IsCoprime aSectorG30mod2 (g30r5 - X) := by
  refine ⟨(X^2 + X^5 + X^6 + X^8 + X^9 + X^10 + X^12 + X^14 + X^16 + X^20 + X^21 + X^22 + X^27 : (ZMod 2)[X]), (1 + X + X^3 + X^5 + X^6 + X^9 + X^11 + X^12 + X^13 + X^15 + X^17 + X^18 + X^19 + X^22 + X^24 + X^26 + X^28 : (ZMod 2)[X]), ?_⟩
  simp only [aSectorG30mod2, g30r5]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30copSmall6 : IsCoprime aSectorG30mod2 (g30r6 - X) := by
  refine ⟨(X^5 + X^11 + X^13 + X^15 + X^17 + X^18 + X^21 + X^22 + X^23 + X^24 + X^25 + X^26 + X^27 : (ZMod 2)[X]), (1 + X^2 + X^8 + X^9 + X^10 + X^15 + X^20 + X^21 + X^22 + X^23 + X^24 + X^25 + X^26 + X^29 : (ZMod 2)[X]), ?_⟩
  simp only [aSectorG30mod2, g30r6]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30copSmall10 : IsCoprime aSectorG30mod2 (g30r10 - X) := by
  refine ⟨(X + X^2 + X^3 + X^4 + X^5 + X^6 + X^8 + X^9 + X^10 + X^14 + X^15 + X^17 + X^19 + X^20 + X^24 : (ZMod 2)[X]), (1 + X + X^3 + X^5 + X^9 + X^10 + X^11 + X^12 + X^14 + X^18 + X^20 + X^21 + X^22 + X^23 + X^25 + X^26 : (ZMod 2)[X]), ?_⟩
  simp only [aSectorG30mod2, g30r10]
  reduce_mod_char
  ring_nf
  reduce_mod_char
theorem g30copSmall15 : IsCoprime aSectorG30mod2 (g30r15 - X) := by
  refine ⟨(X + X^2 + X^3 + X^4 + X^10 + X^13 + X^14 + X^15 + X^16 + X^18 + X^19 + X^23 + X^25 + X^26 + X^27 : (ZMod 2)[X]), (1 + X^2 + X^4 + X^5 + X^6 + X^7 + X^8 + X^10 + X^11 + X^12 + X^13 + X^16 + X^18 + X^19 + X^20 + X^26 + X^29 : (ZMod 2)[X]), ?_⟩
  simp only [aSectorG30mod2, g30r15]
  reduce_mod_char
  ring_nf
  reduce_mod_char


end
end Biunimodular.F11
