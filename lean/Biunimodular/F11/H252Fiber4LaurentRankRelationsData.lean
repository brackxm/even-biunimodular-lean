/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber4LaurentRankRelationsLiterals001
import Biunimodular.F11.H252Fiber4LaurentRankRelationsLiterals002
import Biunimodular.F11.H252Fiber4LaurentRankRelationsLiterals003
import Biunimodular.F11.H252Fiber4LaurentRankRelationsLiterals004
import Biunimodular.F11.H252Fiber4LaurentRankRelationsLiterals005
import Biunimodular.F11.H252Fiber4LaurentRankRelationsLiterals006
import Biunimodular.F11.H252Fiber4LaurentRankRelationsLiterals007
import Biunimodular.F11.H252Fiber4LaurentRankRelationsLiterals008
import Biunimodular.F11.H252Fiber4LaurentRankRelationsLiterals009
import Biunimodular.F11.H252Fiber4LaurentRankRelationsLiterals010

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0

def h252Fiber4LaurentRankColumns := h252Fiber4LaurentRankColumns001 ++ h252Fiber4LaurentRankColumns002 ++ h252Fiber4LaurentRankColumns003 ++ h252Fiber4LaurentRankColumns004 ++ h252Fiber4LaurentRankColumns005 ++ h252Fiber4LaurentRankColumns006 ++ h252Fiber4LaurentRankColumns007 ++ h252Fiber4LaurentRankColumns008 ++ h252Fiber4LaurentRankColumns009 ++ h252Fiber4LaurentRankColumns010

def h252Fiber4LaurentRankConstants := h252Fiber4LaurentRankConstants001 ++ h252Fiber4LaurentRankConstants002 ++ h252Fiber4LaurentRankConstants003 ++ h252Fiber4LaurentRankConstants004 ++ h252Fiber4LaurentRankConstants005 ++ h252Fiber4LaurentRankConstants006 ++ h252Fiber4LaurentRankConstants007 ++ h252Fiber4LaurentRankConstants008 ++ h252Fiber4LaurentRankConstants009 ++ h252Fiber4LaurentRankConstants010

def h252Fiber4LaurentRankMonomials := h252Fiber4LaurentRankMonomials001 ++ h252Fiber4LaurentRankMonomials002 ++ h252Fiber4LaurentRankMonomials003 ++ h252Fiber4LaurentRankMonomials004 ++ h252Fiber4LaurentRankMonomials005 ++ h252Fiber4LaurentRankMonomials006 ++ h252Fiber4LaurentRankMonomials007 ++ h252Fiber4LaurentRankMonomials008 ++ h252Fiber4LaurentRankMonomials009 ++ h252Fiber4LaurentRankMonomials010

def h252Fiber4LaurentRankGlobal : List RurInverseTerm7 := [⟨1, ⟨4, 4, 4, 4, 0, 0, 0⟩⟩]

def h252Fiber4LaurentRankPhi : List RurInverseTerm7 := rurInverseSparseOfZ5 [1, 26, -375, -12850, -6906, 1368104, 4142409, -54815718, -212818474, 839205532, 3494548409, -3872363003, -16740839424, 7654817085, 44709045596, -30112515373, -55199648848, 87284009000, -34034737712, -46495037501, 95226464839, -75083478382, 9174538112, 34701903270, -29400243975, 6057684154, 5204480804, -4088566633, 859300144, 317562022, -254534434, 64054364, -1628253, -2696123, 391145, 94975, -37002, 4288, -89, -18, 1]
def h252Fiber4LaurentRankInverseRoot : List RurInverseTerm7 := rurInverseSparseOfZ5 [-26, 375, 12850, 6906, -1368104, -4142409, 54815718, 212818474, -839205532, -3494548409, 3872363003, 16740839424, -7654817085, -44709045596, 30112515373, 55199648848, -87284009000, 34034737712, 46495037501, -95226464839, 75083478382, -9174538112, -34701903270, 29400243975, -6057684154, -5204480804, 4088566633, -859300144, -317562022, 254534434, -64054364, 1628253, 2696123, -391145, -94975, 37002, -4288, 89, 18, -1]

end Biunimodular.F11
