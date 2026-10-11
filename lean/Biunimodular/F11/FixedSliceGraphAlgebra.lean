/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Ideal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Biunimodular.F11

open Polynomial
noncomputable section

abbrev TraceGraphPolynomial := MvPolynomial (Fin 6) ℂ

def traceGraphGenerators (p : ℂ[X]) (fs : Fin 5 → ℂ[X]) : List TraceGraphPolynomial :=
  [Polynomial.aeval (MvPolynomial.X 5) p,
   MvPolynomial.X 0 - Polynomial.aeval (MvPolynomial.X 5) (fs 0),
   MvPolynomial.X 1 - Polynomial.aeval (MvPolynomial.X 5) (fs 1),
   MvPolynomial.X 2 - Polynomial.aeval (MvPolynomial.X 5) (fs 2),
   MvPolynomial.X 3 - Polynomial.aeval (MvPolynomial.X 5) (fs 3),
   MvPolynomial.X 4 - Polynomial.aeval (MvPolynomial.X 5) (fs 4)]

def traceGraphIdeal (p : ℂ[X]) (fs : Fin 5 → ℂ[X]) : Ideal TraceGraphPolynomial :=
  Ideal.span {f | f ∈ traceGraphGenerators p fs}

abbrev TraceGraphAlgebra (p : ℂ[X]) (fs : Fin 5 → ℂ[X]) :=
  TraceGraphPolynomial ⧸ traceGraphIdeal p fs

def traceGraphValues (p : ℂ[X]) (fs : Fin 5 → ℂ[X]) : Fin 6 → AdjoinRoot p :=
  ![AdjoinRoot.mk p (fs 0), AdjoinRoot.mk p (fs 1), AdjoinRoot.mk p (fs 2),
    AdjoinRoot.mk p (fs 3), AdjoinRoot.mk p (fs 4), AdjoinRoot.root p]

private theorem traceGraphEval_vanish (p : ℂ[X]) (fs : Fin 5 → ℂ[X]) :
    ∀ f ∈ traceGraphIdeal p fs, MvPolynomial.aeval (traceGraphValues p fs) f = 0 := by
  have hle : traceGraphIdeal p fs ≤
      RingHom.ker (MvPolynomial.aeval (traceGraphValues p fs)).toRingHom := by
    apply Ideal.span_le.mpr
    intro f hf
    simp only [traceGraphGenerators, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [RingHom.mem_ker, ← Polynomial.aeval_algHom_apply,
        traceGraphValues, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  intro f hf
  exact hle hf

def traceGraphToRoot (p : ℂ[X]) (fs : Fin 5 → ℂ[X]) :
    TraceGraphAlgebra p fs →ₐ[ℂ] AdjoinRoot p :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (traceGraphValues p fs))
    (traceGraphEval_vanish p fs)

def traceGraphTrace (p : ℂ[X]) (fs : Fin 5 → ℂ[X]) : TraceGraphAlgebra p fs :=
  Ideal.Quotient.mkₐ ℂ (traceGraphIdeal p fs) (MvPolynomial.X 5)

private theorem traceGraphTrace_isRoot (p : ℂ[X]) (fs : Fin 5 → ℂ[X]) :
    Polynomial.aeval (traceGraphTrace p fs) p = 0 := by
  rw [traceGraphTrace, Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℂ _)]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp [traceGraphGenerators])

def rootToTraceGraph (p : ℂ[X]) (fs : Fin 5 → ℂ[X]) :
    AdjoinRoot p →ₐ[ℂ] TraceGraphAlgebra p fs :=
  AdjoinRoot.liftAlgHom p (Algebra.ofId ℂ _) (traceGraphTrace p fs)
    (traceGraphTrace_isRoot p fs)

private theorem traceGraph_coordinate (p : ℂ[X]) (fs : Fin 5 → ℂ[X]) (i : Fin 5) :
    Ideal.Quotient.mk (traceGraphIdeal p fs) (MvPolynomial.X i.castSucc) =
      Polynomial.aeval (traceGraphTrace p fs) (fs i) := by
  change Ideal.Quotient.mkₐ ℂ (traceGraphIdeal p fs) (MvPolynomial.X i.castSucc) = _
  rw [traceGraphTrace, Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℂ _)]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  fin_cases i <;> simp [traceGraphGenerators]

/-- Eliminating five graph coordinates gives the exact univariate algebra,
including nilpotents and scheme multiplicities. -/
def traceGraphAlgebraEquivRoot (p : ℂ[X]) (fs : Fin 5 → ℂ[X]) :
    TraceGraphAlgebra p fs ≃ₐ[ℂ] AdjoinRoot p := by
  apply AlgEquiv.ofAlgHom (traceGraphToRoot p fs) (rootToTraceGraph p fs)
  · apply AdjoinRoot.algHom_ext
    simp [traceGraphToRoot, rootToTraceGraph, traceGraphTrace,
      Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, traceGraphValues]
  · apply AlgHom.ext
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ (traceGraphIdeal p fs) x
    have heq : ((rootToTraceGraph p fs).comp (traceGraphToRoot p fs)).comp
        (Ideal.Quotient.mkₐ ℂ (traceGraphIdeal p fs)) =
        Ideal.Quotient.mkₐ ℂ (traceGraphIdeal p fs) := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      all_goals
        simp [traceGraphToRoot, rootToTraceGraph, traceGraphValues,
          Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk, ← Polynomial.aeval_def,
          traceGraphTrace]
      all_goals first
        | exact (traceGraph_coordinate p fs 0).symm
        | exact (traceGraph_coordinate p fs 1).symm
        | exact (traceGraph_coordinate p fs 2).symm
        | exact (traceGraph_coordinate p fs 3).symm
        | exact (traceGraph_coordinate p fs 4).symm
    exact congrArg (fun h : TraceGraphPolynomial →ₐ[ℂ] TraceGraphAlgebra p fs => h f) heq

end
end Biunimodular.F11
