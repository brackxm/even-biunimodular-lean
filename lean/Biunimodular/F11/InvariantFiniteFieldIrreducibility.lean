/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.InvariantA3FiniteFieldCertificates
import Biunimodular.F11.InvariantB5FiniteFieldCertificates

/-!
Aggregator for the arithmetic finite-field irreducibility certificates.

The degree-six and degree-eight proofs live in independent modules so Lake can
compile them separately (and in parallel when scheduling permits), while all
existing imports of `InvariantFiniteFieldIrreducibility` continue to re-export
`invariantA3_irreducible` and `invariantB5_irreducible` unchanged.
-/
