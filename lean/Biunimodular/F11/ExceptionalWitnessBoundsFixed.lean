/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Biunimodular.F11.FinitePhaseNativeScan
public import Biunimodular.F11.ExceptionalCandidateWitnessData
public meta import Biunimodular.F11.ProofTactics
public meta import Biunimodular.F11.FinitePhaseNativeScan
public meta import Biunimodular.F11.ExceptionalCandidateWitnessData

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

deriving instance Inhabited for ExceptionalWitness

/-- Rational center coordinates from the common denominator-1e14 table. -/
def centerQ (i : Nat) : ℚ × ℚ :=
  (((phaseCenters160[i]!).re : ℚ) / phaseCenterScale,
   ((phaseCenters160[i]!).im : ℚ) / phaseCenterScale)

def absQ (x : ℚ) : ℚ := if x < 0 then -x else x

def dotWitness (w : ExceptionalWitness) (v : Fin 4 → ℚ) : ℚ :=
  w.w0*v 0 + w.w1*v 1 + w.w2*v 2 + w.w3*v 3

/-- Rational specialization of the four-row center tail system. -/
def centerTailMatrixQ (ia ic ie : Nat) : Matrix (Fin 4) (Fin 4) ℚ :=
  let a := (centerQ ia).1; let b := (centerQ ia).2
  let c := (centerQ ic).1; let d := (centerQ ic).2
  let e := (centerQ ie).1; let f := (centerQ ie).2
  !![e-c, f-d, -e, -f;
     a, b, c+e, d+f;
     1+e, f, a+c, b+d;
     a+c, b+d, 1+a, b]

def centerTailRhsQ (ia ic ie : Nat) : Fin 4 → ℚ :=
  let a := (centerQ ia).1; let b := (centerQ ia).2
  let c := (centerQ ic).1; let d := (centerQ ic).2
  let e := (centerQ ie).1; let f := (centerQ ie).2
  ![-(a-c+a*c+b*d+c*e+d*f-a*e-b*f),
    -(e+a*c+b*d+(1/2 : ℚ)),
    -(a*e+b*f+(1/2 : ℚ)),
    -(c*e+d*f+(1/2 : ℚ))]

/-- The simple rational witnesses satisfy strong uniform margins. -/
theorem exceptional_witness_uniform_bounds :
    ∀ q : Fin 20,
      let w := exceptionalWitnesses20[q.1]!
      let M := centerTailMatrixQ w.aIdx w.cIdx w.eIdx
      let R := centerTailRhsQ w.aIdx w.cIdx w.eIdx
      absQ (dotWitness w R) > (1/100 : ℚ) ∧
      (∀ j : Fin 4, absQ (dotWitness w (fun i => M i j)) < (1/1000000000 : ℚ)) ∧
      absQ w.w0 + absQ w.w1 + absQ w.w2 + absQ w.w3 < 2 := by native_decide

/-- Find the table witness attached to a triple, if any. -/
def witnessForTriple (ia ic ie : Nat) : Option ExceptionalWitness :=
  exceptionalWitnesses20.find? fun w => w.aIdx = ia ∧ w.cIdx = ic ∧ w.eIdx = ie

/-- The witness table encodes exactly the same 20 exceptional triples as the scan table. -/
theorem witnessForTriple_iff_exceptional :
    ∀ ia ic ie : Fin 160,
      (witnessForTriple ia.1 ic.1 ie.1).isSome = exceptionalTriple ia.1 ic.1 ie.1 := by native_decide

/-- Any witness returned by the finite table satisfies the uniform margins. -/
theorem witnessForTriple_bounds :
    ∀ ia ic ie : Fin 160, ∀ w : ExceptionalWitness,
      witnessForTriple ia.1 ic.1 ie.1 = some w →
      let M := centerTailMatrixQ w.aIdx w.cIdx w.eIdx
      let R := centerTailRhsQ w.aIdx w.cIdx w.eIdx
      absQ (dotWitness w R) > (1/100 : ℚ) ∧
      (∀ j : Fin 4, absQ (dotWitness w (fun i => M i j)) < (1/1000000000 : ℚ)) ∧
      absQ w.w0 + absQ w.w1 + absQ w.w2 + absQ w.w3 < 2 := by
  intro ia ic ie w hw
  have hmem : w ∈ exceptionalWitnesses20 :=
    List.mem_of_find?_eq_some hw
  obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hmem
  have hq20 : q < 20 := by
    simpa [exceptionalWitnesses20_length] using hq
  have hb := exceptional_witness_uniform_bounds ⟨q, hq20⟩
  simpa [getElem!_pos exceptionalWitnesses20 q hq] using hb

end Biunimodular.F11
