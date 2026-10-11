/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Algebra.Pi
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Biunimodular.F11
open Polynomial
noncomputable section

/-- Evaluation of a complex univariate algebra at all its geometric roots. -/
def splitPolynomialEvaluation (p : ℂ[X]) :
    AdjoinRoot p →ₐ[ℂ] (p.rootSet ℂ → ℂ) :=
  AlgHom.pi fun r => AdjoinRoot.liftAlgHom p (Algebra.ofId ℂ ℂ) r.1 (by
    have hr := (Polynomial.mem_rootSet.mp r.2).2
    change p.eval₂ (algebraMap ℂ ℂ) r.1 = 0
    exact hr)

@[simp] theorem splitPolynomialEvaluation_mk (p f : ℂ[X]) (r : p.rootSet ℂ) :
    splitPolynomialEvaluation p (AdjoinRoot.mk p f) r = f.eval r.1 := by
  simp [splitPolynomialEvaluation, Polynomial.eval₂_id]

private theorem splitPolynomialEvaluation_injective (p : ℂ[X]) (hp : p.Separable) :
    Function.Injective (splitPolynomialEvaluation p) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
  apply AdjoinRoot.mk_eq_zero.mpr
  by_cases hf : f = 0
  · rw [hf]; exact dvd_zero _
  apply (IsAlgClosed.dvd_iff_roots_le_roots hp.ne_zero hf).mpr
  apply (Multiset.le_iff_subset (Polynomial.nodup_roots hp)).mpr
  intro r hr
  apply (Polynomial.mem_roots hf).mpr
  let root : p.rootSet ℂ := ⟨r, by
    apply Polynomial.mem_rootSet.mpr
    exact ⟨hp.ne_zero, by simpa [Polynomial.aeval_def, Algebra.algebraMap_self,
      Polynomial.eval₂_id] using
      (Polynomial.mem_roots hp.ne_zero).mp hr⟩⟩
  have he := congrFun hx root
  simpa using he

/-- A squarefree complex polynomial's coordinate algebra is exactly the
algebra of functions on its roots, with evaluation as the isomorphism. -/
def splitPolynomialAlgebraEquivFunctions (p : ℂ[X]) (hp : p.Separable) :
    AdjoinRoot p ≃ₐ[ℂ] (p.rootSet ℂ → ℂ) := by
  classical
  letI : Module.Finite ℂ (AdjoinRoot p) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hp.ne_zero).basis
  have hcard : Fintype.card (p.rootSet ℂ) = p.natDegree :=
    Polynomial.card_rootSet_eq_natDegree hp
      (IsAlgClosed.splits (p.map (algebraMap ℂ ℂ)))
  have hdim : Module.finrank ℂ (AdjoinRoot p) =
      Module.finrank ℂ (p.rootSet ℂ → ℂ) := by
    rw [(AdjoinRoot.powerBasis hp.ne_zero).finrank, AdjoinRoot.powerBasis_dim,
      Module.finrank_fintype_fun_eq_card, hcard]
  apply AlgEquiv.ofBijective (splitPolynomialEvaluation p)
  have hi := splitPolynomialEvaluation_injective p hp
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
    (f := (splitPolynomialEvaluation p).toLinearMap)).mp hi⟩

end
end Biunimodular.F11
