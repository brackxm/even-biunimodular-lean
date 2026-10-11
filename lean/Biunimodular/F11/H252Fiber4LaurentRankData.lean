/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252Fiber4LaurentRankInverse001
import Biunimodular.F11.H252Fiber4LaurentRankInverse002
import Biunimodular.F11.H252Fiber4LaurentRankInverse003
import Biunimodular.F11.H252Fiber4LaurentRankInverse004
import Biunimodular.F11.H252Fiber4LaurentRankInverse005
import Biunimodular.F11.H252Fiber4LaurentRankInverse006
import Biunimodular.F11.H252Fiber4LaurentRankInverse007
import Biunimodular.F11.H252Fiber4LaurentRankInverse008
import Biunimodular.F11.H252Fiber4LaurentRankInverse009
import Biunimodular.F11.H252Fiber4LaurentRankInverse010
import Biunimodular.F11.H252Fiber4LaurentRankInverse011
import Biunimodular.F11.H252Fiber4LaurentRankInverse012
import Biunimodular.F11.H252Fiber4LaurentRankInverse013
import Biunimodular.F11.H252Fiber4LaurentRankRows001
import Biunimodular.F11.H252Fiber4LaurentRankRows002
import Biunimodular.F11.H252Fiber4LaurentRankRows003
import Biunimodular.F11.H252Fiber4LaurentRankRows004
import Biunimodular.F11.H252Fiber4LaurentRankRows005
import Biunimodular.F11.H252Fiber4LaurentRankRows006
import Biunimodular.F11.H252Fiber4LaurentRankRows007
import Biunimodular.F11.H252Fiber4LaurentRankRows008
import Biunimodular.F11.H252Fiber4LaurentRankRows009
import Biunimodular.F11.H252Fiber4LaurentRankRows010
import Biunimodular.F11.H252Fiber4LaurentRankRows011
import Biunimodular.F11.H252Fiber4LaurentRankRows012
import Biunimodular.F11.H252Fiber4LaurentRankRows013

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11
set_option maxHeartbeats 0

def h252Fiber4LaurentRankRows : Array TorusMacaulayRow := h252Fiber4LaurentRankRows001 ++ h252Fiber4LaurentRankRows002 ++ h252Fiber4LaurentRankRows003 ++ h252Fiber4LaurentRankRows004 ++ h252Fiber4LaurentRankRows005 ++ h252Fiber4LaurentRankRows006 ++ h252Fiber4LaurentRankRows007 ++ h252Fiber4LaurentRankRows008 ++ h252Fiber4LaurentRankRows009 ++ h252Fiber4LaurentRankRows010 ++ h252Fiber4LaurentRankRows011 ++ h252Fiber4LaurentRankRows012 ++ h252Fiber4LaurentRankRows013

def h252Fiber4LaurentRankInverseText : Array String := h252Fiber4LaurentRankInverseText001 ++ h252Fiber4LaurentRankInverseText002 ++ h252Fiber4LaurentRankInverseText003 ++ h252Fiber4LaurentRankInverseText004 ++ h252Fiber4LaurentRankInverseText005 ++ h252Fiber4LaurentRankInverseText006 ++ h252Fiber4LaurentRankInverseText007 ++ h252Fiber4LaurentRankInverseText008 ++ h252Fiber4LaurentRankInverseText009 ++ h252Fiber4LaurentRankInverseText010 ++ h252Fiber4LaurentRankInverseText011 ++ h252Fiber4LaurentRankInverseText012 ++ h252Fiber4LaurentRankInverseText013

def h252Fiber4LaurentRankInverse : Array (Array ℤ) := h252Fiber4LaurentRankInverseText.map torusMacaulayParseIntegerRow

end Biunimodular.F11
