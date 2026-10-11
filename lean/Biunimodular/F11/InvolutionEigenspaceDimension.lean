/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic.Module

set_option autoImplicit false
namespace Biunimodular.F11
noncomputable section
open Module LinearMap

theorem involution_eigenspace_finrank_three {K V : Type*}
    [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (hf : ∀ x, f (f x) = x)
    (ht : LinearMap.trace K V f = 0) (hd : Module.finrank K V = 6) :
    Module.finrank K (f.eigenspace 1) = 3 := by
  let p : Module.End K V := (1 / 2 : K) • (LinearMap.id + f)
  have hp : LinearMap.IsProj (f.eigenspace 1) p := by
    constructor
    · intro x
      rw [Module.End.mem_eigenspace_iff]
      simp only [p, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, map_smul, map_add, hf, one_smul]
      module
    · intro x hx
      rw [Module.End.mem_eigenspace_iff] at hx
      simp only [p, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply, hx, one_smul]
      module
  have htrace := hp.trace
  have hpTrace : LinearMap.trace K V p = (3 : K) := by
    simp [p, map_smul, map_add, LinearMap.trace_id, ht, hd]
    norm_num
  rw [hpTrace] at htrace
  exact_mod_cast htrace.symm

theorem involution_eigenspaces_finrank_three {K V : Type*}
    [Field K] [CharZero K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (hf : ∀ x, f (f x) = x)
    (ht : LinearMap.trace K V f = 0) (hd : Module.finrank K V = 6) :
    Module.finrank K (f.eigenspace 1) = 3 ∧
      Module.finrank K (f.eigenspace (-1)) = 3 := by
  refine ⟨involution_eigenspace_finrank_three f hf ht hd, ?_⟩
  have hneg : ∀ x, (-f) ((-f) x) = x := by intro x; simp [hf]
  have htneg : LinearMap.trace K V (-f) = 0 := by rw [map_neg, ht, neg_zero]
  have he : (-f).eigenspace 1 = f.eigenspace (-1) := by
    ext x
    simp only [Module.End.mem_eigenspace_iff, LinearMap.neg_apply, one_smul, neg_one_smul]
    constructor <;> intro h <;> simpa using congrArg Neg.neg h
  rw [← he]
  exact involution_eigenspace_finrank_three (-f) hneg htneg hd

end
end Biunimodular.F11
