/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber5LaurentRankRelationsLiterals001
import Biunimodular.F11.H252Fiber5LaurentRankRelationsLiterals002
import Biunimodular.F11.H252Fiber5LaurentRankRelationsLiterals003
import Biunimodular.F11.H252Fiber5LaurentRankRelationsLiterals004
import Biunimodular.F11.H252Fiber5LaurentRankRelationsLiterals005
import Biunimodular.F11.H252Fiber5LaurentRankRelationsLiterals006
import Biunimodular.F11.H252Fiber5LaurentRankRelationsLiterals007
import Biunimodular.F11.H252Fiber5LaurentRankRelationsLiterals008
import Biunimodular.F11.H252Fiber5LaurentRankRelationsLiterals009
import Biunimodular.F11.H252Fiber5LaurentRankRelationsLiterals010

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0

def h252Fiber5LaurentRankColumns := h252Fiber5LaurentRankColumns001 ++ h252Fiber5LaurentRankColumns002 ++ h252Fiber5LaurentRankColumns003 ++ h252Fiber5LaurentRankColumns004 ++ h252Fiber5LaurentRankColumns005 ++ h252Fiber5LaurentRankColumns006 ++ h252Fiber5LaurentRankColumns007 ++ h252Fiber5LaurentRankColumns008 ++ h252Fiber5LaurentRankColumns009 ++ h252Fiber5LaurentRankColumns010

def h252Fiber5LaurentRankConstants := h252Fiber5LaurentRankConstants001 ++ h252Fiber5LaurentRankConstants002 ++ h252Fiber5LaurentRankConstants003 ++ h252Fiber5LaurentRankConstants004 ++ h252Fiber5LaurentRankConstants005 ++ h252Fiber5LaurentRankConstants006 ++ h252Fiber5LaurentRankConstants007 ++ h252Fiber5LaurentRankConstants008 ++ h252Fiber5LaurentRankConstants009 ++ h252Fiber5LaurentRankConstants010

def h252Fiber5LaurentRankMonomials := h252Fiber5LaurentRankMonomials001 ++ h252Fiber5LaurentRankMonomials002 ++ h252Fiber5LaurentRankMonomials003 ++ h252Fiber5LaurentRankMonomials004 ++ h252Fiber5LaurentRankMonomials005 ++ h252Fiber5LaurentRankMonomials006 ++ h252Fiber5LaurentRankMonomials007 ++ h252Fiber5LaurentRankMonomials008 ++ h252Fiber5LaurentRankMonomials009 ++ h252Fiber5LaurentRankMonomials010

def h252Fiber5LaurentRankGlobal : List RurInverseTerm7 := [⟨1, ⟨4, 4, 4, 4, 0, 0, 0⟩⟩]

def h252Fiber5LaurentRankPhi : List RurInverseTerm7 := rurInverseSparseOfZ5 [1, -18, -89, 4288, -37002, 94975, 391145, -2696123, -1628253, 64054364, -254534434, 317562022, 859300144, -4088566633, 5204480804, 6057684154, -29400243975, 34701903270, 9174538112, -75083478382, 95226464839, -46495037501, -34034737712, 87284009000, -55199648848, -30112515373, 44709045596, 7654817085, -16740839424, -3872363003, 3494548409, 839205532, -212818474, -54815718, 4142409, 1368104, -6906, -12850, -375, 26, 1]
def h252Fiber5LaurentRankInverseRoot : List RurInverseTerm7 := rurInverseSparseOfZ5 [18, 89, -4288, 37002, -94975, -391145, 2696123, 1628253, -64054364, 254534434, -317562022, -859300144, 4088566633, -5204480804, -6057684154, 29400243975, -34701903270, -9174538112, 75083478382, -95226464839, 46495037501, 34034737712, -87284009000, 55199648848, 30112515373, -44709045596, -7654817085, 16740839424, 3872363003, -3494548409, -839205532, 212818474, 54815718, -4142409, -1368104, 6906, 12850, 375, -26, -1]

end Biunimodular.F11
