/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.H252ReverseRur

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Polynomial

/-- The original seven polynomial equations have exactly the displayed RUR
solutions. The saturation equation enforces all five nonzero phase coordinates. -/
theorem h252LocalizedTorus_solution_iff (z : Fin 7 → ℂ) :
    (∀ i, MvPolynomial.aeval z (h252LocalizedTorusGenerators i) = 0) ↔
      ∃ x : ℂ, h252RurComplexPolynomial.IsRoot x ∧ z = h252RurTorusPoint x := by
  constructor
  · intro hz
    have hzI : h252LocalizedTorusIdeal ≤ RingHom.ker (MvPolynomial.aeval z).toRingHom := by
      apply Ideal.span_le.mpr
      rintro q ⟨i, rfl⟩
      exact RingHom.mem_ker.mpr (hz i)
    let g : H252LocalizedTorusAlgebra →ₐ[ℂ] ℂ :=
      Ideal.Quotient.liftₐ h252LocalizedTorusIdeal (MvPolynomial.aeval z)
        (fun _q hq ↦ RingHom.mem_ker.mp (hzI hq))
    have hgvar (i : Fin 7) : g (h252LocalizedTorusVar i) = z i := by
      have h := AlgHom.congr_fun
        (Ideal.Quotient.liftₐ_comp h252LocalizedTorusIdeal (MvPolynomial.aeval z)
          (fun _q hq ↦ RingHom.mem_ker.mp (hzI hq))) (MvPolynomial.X i)
      simp [g, h252LocalizedTorusVar, AlgHom.comp_apply] at h ⊢
    obtain ⟨hx, hg⟩ := h252LocalizedTorus_point_unique g
    refine ⟨g (h252LocalizedTorusCoordinate X), hx, ?_⟩
    funext i
    calc
      z i = g (h252LocalizedTorusVar i) := (hgvar i).symm
      _ = h252RurTorusPointEvaluation (g (h252LocalizedTorusCoordinate X)) hx
          (h252LocalizedTorusVar i) := AlgHom.congr_fun hg _
      _ = _ := h252RurTorusPointEvaluation_var _ hx i
  · rintro ⟨x, hx, rfl⟩
    exact h252RurTorusPoint_generators_zero x hx

theorem h252LocalizedTorus_solution_unique (z : Fin 7 → ℂ)
    (hz : ∀ i, MvPolynomial.aeval z (h252LocalizedTorusGenerators i) = 0) :
    ∃! x : ℂ, h252RurComplexPolynomial.IsRoot x ∧ z = h252RurTorusPoint x := by
  obtain ⟨x, hx, hzx⟩ := (h252LocalizedTorus_solution_iff z).mp hz
  refine ⟨x, ⟨hx, hzx⟩, ?_⟩
  intro y hy
  have h := congrFun (hy.2.symm.trans hzx) (6 : Fin 7)
  simpa [h252RurTorusPoint] using h

end
end Biunimodular.F11
