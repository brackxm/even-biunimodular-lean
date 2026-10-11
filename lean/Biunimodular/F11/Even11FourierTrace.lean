/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.Even11FourierLift
import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.Multiset.Bind

set_option autoImplicit false
namespace Biunimodular.F11
open ZMod AddChar
noncomputable section

def even11FourierTraceResidues : Multiset (ZMod 11) :=
  (Finset.univ : Finset (Fin 6)).val.bind fun j =>
    ((Finset.univ : Finset (ZMod 11)).val.filter (fun t => even11Coordinate t = j)).map
      (fun t => -(t * (j.val : ZMod 11)))

theorem even11FourierTraceResidues_exact :
    even11FourierTraceResidues = (Finset.univ : Finset (ZMod 11)).val := by native_decide

theorem even11Fourier_trace : LinearMap.trace ℂ (Even6 ℂ) even11Fourier = 0 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin 6))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_apply, even11Fourier_apply, dft_apply, smul_eq_mul]
  have hsum := congrArg
    (fun m : Multiset (ZMod 11) => (m.map stdAddChar).sum) even11FourierTraceResidues_exact
  have hne : (stdAddChar : AddChar (ZMod 11) ℂ) ≠ 1 := by
    simpa using (isPrimitive_stdAddChar 11) (a := (1 : ZMod 11)) (by decide)
  change (∑ j : Fin 6, ∑ t : ZMod 11,
    stdAddChar (-(t * (j.val : ZMod 11))) * even11Lift (Pi.single j 1) t) = 0
  simp only [even11Lift, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply,
    mul_ite, mul_one, mul_zero]
  simp only [even11FourierTraceResidues, Multiset.map_bind, Multiset.map_map,
    Function.comp_apply, Multiset.sum_bind] at hsum
  have hsum' : (∑ j : Fin 6, ∑ t ∈ (Finset.univ.filter fun t => even11Coordinate t = j),
      stdAddChar (-(t * (j.val : ZMod 11)))) = ∑ t : ZMod 11, stdAddChar t := by
    exact hsum
  simp only [Finset.sum_filter] at hsum'
  rw [hsum', sum_eq_zero_of_ne_one hne]

theorem even11FourierNormalized_trace :
    LinearMap.trace ℂ (Even6 ℂ) even11FourierNormalized = 0 := by
  rw [even11FourierNormalized, _root_.map_smul, even11Fourier_trace, smul_zero]

end
end Biunimodular.F11
