/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber5LaurentRankInverse001
import Biunimodular.F11.H252Fiber5LaurentRankInverse002
import Biunimodular.F11.H252Fiber5LaurentRankInverse003
import Biunimodular.F11.H252Fiber5LaurentRankInverse004
import Biunimodular.F11.H252Fiber5LaurentRankInverse005
import Biunimodular.F11.H252Fiber5LaurentRankInverse006
import Biunimodular.F11.H252Fiber5LaurentRankInverse007
import Biunimodular.F11.H252Fiber5LaurentRankInverse008
import Biunimodular.F11.H252Fiber5LaurentRankInverse009
import Biunimodular.F11.H252Fiber5LaurentRankInverse010
import Biunimodular.F11.H252Fiber5LaurentRankInverse011
import Biunimodular.F11.H252Fiber5LaurentRankInverse012
import Biunimodular.F11.H252Fiber5LaurentRankInverse013
import Biunimodular.F11.H252Fiber5LaurentRankRows001
import Biunimodular.F11.H252Fiber5LaurentRankRows002
import Biunimodular.F11.H252Fiber5LaurentRankRows003
import Biunimodular.F11.H252Fiber5LaurentRankRows004
import Biunimodular.F11.H252Fiber5LaurentRankRows005
import Biunimodular.F11.H252Fiber5LaurentRankRows006
import Biunimodular.F11.H252Fiber5LaurentRankRows007
import Biunimodular.F11.H252Fiber5LaurentRankRows008
import Biunimodular.F11.H252Fiber5LaurentRankRows009
import Biunimodular.F11.H252Fiber5LaurentRankRows010
import Biunimodular.F11.H252Fiber5LaurentRankRows011
import Biunimodular.F11.H252Fiber5LaurentRankRows012
import Biunimodular.F11.H252Fiber5LaurentRankRows013

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0

def h252Fiber5LaurentRankRows : Array TorusMacaulayRow := h252Fiber5LaurentRankRows001 ++ h252Fiber5LaurentRankRows002 ++ h252Fiber5LaurentRankRows003 ++ h252Fiber5LaurentRankRows004 ++ h252Fiber5LaurentRankRows005 ++ h252Fiber5LaurentRankRows006 ++ h252Fiber5LaurentRankRows007 ++ h252Fiber5LaurentRankRows008 ++ h252Fiber5LaurentRankRows009 ++ h252Fiber5LaurentRankRows010 ++ h252Fiber5LaurentRankRows011 ++ h252Fiber5LaurentRankRows012 ++ h252Fiber5LaurentRankRows013

def h252Fiber5LaurentRankInverseText : Array String := h252Fiber5LaurentRankInverseText001 ++ h252Fiber5LaurentRankInverseText002 ++ h252Fiber5LaurentRankInverseText003 ++ h252Fiber5LaurentRankInverseText004 ++ h252Fiber5LaurentRankInverseText005 ++ h252Fiber5LaurentRankInverseText006 ++ h252Fiber5LaurentRankInverseText007 ++ h252Fiber5LaurentRankInverseText008 ++ h252Fiber5LaurentRankInverseText009 ++ h252Fiber5LaurentRankInverseText010 ++ h252Fiber5LaurentRankInverseText011 ++ h252Fiber5LaurentRankInverseText012 ++ h252Fiber5LaurentRankInverseText013

def h252Fiber5LaurentRankInverse : Array (Array ℤ) := h252Fiber5LaurentRankInverseText.map torusMacaulayParseIntegerRow

end Biunimodular.F11
