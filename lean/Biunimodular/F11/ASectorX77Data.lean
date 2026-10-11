/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodRealization

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Biunimodular.F11

open Polynomial

noncomputable section

/-! Exact polynomial representative of the conductor-77
phase-coordinate expression. All reductions below are proved by `ring`. -/
def aSectorXPoly77 : ℤ[X] := -627 + 490*X + 97*X^2 - 198*X^3 + 674*X^4 - 53*X^5 - 650*X^6 + 641*X^7 - 365*X^8 + 103*X^9 + 1506*X^10 + X^11 + 481*X^12 - 521*X^14 - 235*X^15 - 169*X^17 + 199*X^18 - 576*X^20 + 1194*X^21 + 599*X^23 + 854*X^24 - 90*X^26 - 228*X^27 - 419*X^29 + 9*X^30 + 511*X^32 + 162*X^33 + 572*X^35 - 185*X^36 + 295*X^38 + 295*X^39 - 185*X^41 + 572*X^42 + 162*X^44 + 511*X^45 + 9*X^47 - 419*X^48 - 228*X^50 - 90*X^51 + 854*X^53 + 599*X^54 + 1194*X^56 - 576*X^57 + 199*X^59 - 169*X^60 - 235*X^62 - 521*X^63 + 481*X^65 + X^66 + 1506*X^67 + 103*X^68 - 365*X^69 + 641*X^70 - 650*X^71 - 53*X^72 + 674*X^73 - 198*X^74 + 97*X^75 + 490*X^76
def aSectorXRed : ℤ[X] := 176 - 535*X + 47*X^2 - 742*X^3 - 290*X^4 + 500*X^5 - 606*X^6 + 771*X^7 + 314*X^8 + 59*X^9 + 107*X^10 + 481*X^11 - 641*X^12 - 59*X^13 - 261*X^14 - 718*X^15 + 606*X^16 - 1034*X^17 + 6*X^18 + 582*X^19 - 629*X^20 + 599*X^21 + 961*X^22 - 470*X^23 - 114*X^24 - 63*X^25 - 670*X^26 + 369*X^27 - 61*X^28 - 131*X^29 + 644*X^30 - 962*X^31 - 407*X^32 + 1026*X^33 - 1078*X^34 + 408*X^35 + 233*X^36 - 527*X^37 - 17*X^38 - 89*X^39 + 191*X^40 + 441*X^41 + 414*X^42 - 437*X^43 + 1079*X^44 - 1476*X^45 - 487*X^46 + 330*X^47 - 955*X^48 + 492*X^49 - 131*X^50 + 154*X^51 - 283*X^52 + 373*X^53 + 65*X^54 + 908*X^55 + 11*X^56 - 582*X^57 + 374*X^58 - 1246*X^59
private def aSectorXQRed : ℤ[X] := -803 + 222*X + 272*X^2 + 816*X^3 + 1780*X^4 + 1227*X^5 + 1183*X^6 + 1856*X^7 + 152*X^8 + 146*X^9 + 1001*X^10 + 360*X^11 + 1010*X^12 + 1063*X^13 + 389*X^14 + 587*X^15 + 490*X^16
theorem aSectorXPoly77_reduction :
    aSectorXPoly77 = phi77 * aSectorXQRed + aSectorXRed := by
  simp only [aSectorXPoly77, phi77, aSectorXQRed, aSectorXRed]
  ring

def aSectorXR0 : ℤ[X] := 1
def aSectorXR1 : ℤ[X] := aSectorXRed

end
end Biunimodular.F11
