/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.MonicDivisorSubproduct
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ReduceModChar

set_option autoImplicit false
namespace Biunimodular.F11
open Polynomial

/-- The checked modular factor pattern 10+10+30+30, with constants
1,1,7,11, excludes a degree-40 monic divisor whose constant squares to 9. -/
theorem mod17_divisor_constant_obstruction
    (f₁ f₂ f₃ f₄ q : (ZMod 17)[X])
    (h₁ : f₁.Monic ∧ Irreducible f₁) (h₂ : f₂.Monic ∧ Irreducible f₂)
    (h₃ : f₃.Monic ∧ Irreducible f₃) (h₄ : f₄.Monic ∧ Irreducible f₄)
    (d₁ : f₁.natDegree = 10) (d₂ : f₂.natDegree = 10)
    (d₃ : f₃.natDegree = 30) (d₄ : f₄.natDegree = 30)
    (c₁ : f₁.coeff 0 = 1) (c₂ : f₂.coeff 0 = 1)
    (c₃ : f₃.coeff 0 = 7) (c₄ : f₄.coeff 0 = 11)
    (hq : q.Monic) (hd : q.natDegree = 40)
    (hdiv : q ∣ f₁ * f₂ * f₃ * f₄) : q.coeff 0 ^ 2 ≠ 9 := by
  classical
  let : Fact (Nat.Prime 17) := ⟨by decide⟩
  intro h9
  let s : Multiset (ZMod 17)[X] := f₁ ::ₘ f₂ ::ₘ f₃ ::ₘ f₄ ::ₘ 0
  have hs : ∀ f ∈ s, f.Monic ∧ Irreducible f := by
    intro f hf
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
  have hv : q ∣ s.prod := by simpa [s, mul_assoc] using hdiv
  obtain ⟨t, ht, he⟩ := monic_divisor_eq_subproduct (K := ZMod 17) s hs q hq hv
  rw [he] at hd h9
  have hm := Multiset.mem_powerset.mpr ht
  simp only [s, Multiset.powerset_cons, Multiset.powerset_zero,
    Multiset.map_add, Multiset.map_singleton, Multiset.mem_add,
    Multiset.mem_singleton, or_assoc] at hm
  rcases hm with hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm | hm
  all_goals
    subst t
    simp [Multiset.prod_cons, Multiset.prod_zero, natDegree_mul,
      h₁.1.ne_zero, h₂.1.ne_zero, h₃.1.ne_zero, h₄.1.ne_zero,
      d₁, d₂, d₃, d₄, mul_coeff_zero, c₁, c₂, c₃, c₄] at hd h9 <;> norm_num at h9 <;> reduce_mod_char at h9
    all_goals first
      | exact (by decide : (2 : ZMod 17) ≠ 9) h9
      | exact (by decide : (15 : ZMod 17) ≠ 9) h9

end Biunimodular.F11
