/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.ASectorPeriodTraceData77
import Biunimodular.F11.ASectorConductor77Certificates
import Biunimodular.F11.IntegerCoefficientPolynomialMap
import Biunimodular.F11.P150CofactorPositive11
import Lean.Util.CollectAxioms

/-!
The reflected trace-matrix certificates, small conductor computations and
coefficient-list bridges must use only Lean's standard axioms. In particular,
this audit rejects a future reintroduction of native evaluation axioms.
-/

open Lean in
run_cmd do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations := #[
    ``Biunimodular.F11.periodOrderTraceGramData77_mul_dual,
    ``Biunimodular.F11.periodOrderTraceGramData77_rank,
    ``Biunimodular.F11.periodOrderTraceGramData77_det,
    ``Biunimodular.F11.six_pow_five_mod77,
    ``Biunimodular.F11.conductor77Powers6_nodup,
    ``Biunimodular.F11.conductor77Powers6_eq_H0,
    ``Biunimodular.F11.periodC77_discriminant_decomposition,
    ``Biunimodular.F11.conductor77_conductor_discriminant_product,
    ``Biunimodular.F11.integerCoefficientPolynomial_eq_ofCoeffList,
    ``Biunimodular.F11.integerCoefficientPolynomial_coeff,
    ``Biunimodular.F11.polynomialOfCoefficientsQ11_eq_ofCoeffList,
    ``Biunimodular.F11.polynomialOfCoefficientsZ_eq_ofCoeffList,
    ``Biunimodular.F11.polynomialOfCoefficientsQ11_coeff,
    ``Biunimodular.F11.polynomialOfCoefficientsQ11_scale,
    ``Biunimodular.F11.polynomialOfCoefficientsZ_map_Q11]
  for declaration in declarations do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses the nonstandard axiom {axiomName}"
