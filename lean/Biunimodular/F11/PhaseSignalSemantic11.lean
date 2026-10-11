/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

module

public import Biunimodular.F11.ProofTactics
public import Mathlib.Basic.Complex.Basic

@[expose] public section

set_option autoImplicit false

namespace Biunimodular.F11

/-!
# Normalized even phase coordinates at prime 11

The five independent signal values are `a + ib`, `c + id`, `e + if`,
`g + ih`, and `j + ik`, at indices 1 through 5. Values at negative indices
are equal to these values, and the zeroth value is one.

The circle equations impose unit modulus. `E1` through `E5` impose vanishing
cyclic autocorrelation at lags 1 through 5; evenness supplies lags 6 through
10. The autocorrelation convention is `sum_t z(t + r) * conj(z(t))`.
-/

/-- The real and imaginary parts of the five independent unit phases. -/
structure PhaseCoords11 where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  f : ℝ
  g : ℝ
  h : ℝ
  j : ℝ
  k : ℝ

namespace PhaseCoords11

def CircleEquations (x : PhaseCoords11) : Prop :=
  x.a^2+x.b^2=1 ∧ x.c^2+x.d^2=1 ∧ x.e^2+x.f^2=1 ∧ x.g^2+x.h^2=1 ∧ x.j^2+x.k^2=1

def E1 (x : PhaseCoords11) : Prop := 2*x.a+2*(x.a*x.c+x.b*x.d)+2*(x.c*x.e+x.d*x.f)+2*(x.e*x.g+x.f*x.h)+2*(x.g*x.j+x.h*x.k)+1=0

def E2 (x : PhaseCoords11) : Prop := 2*x.c+2*(x.a*x.e+x.b*x.f)+2*(x.c*x.g+x.d*x.h)+2*(x.e*x.j+x.f*x.k)+2*(x.g*x.j+x.h*x.k)+1=0

def E3 (x : PhaseCoords11) : Prop := 2*x.e+2*(x.a*x.g+x.b*x.h)+2*(x.c*x.j+x.d*x.k)+2*(x.e*x.j+x.f*x.k)+2*(x.a*x.c+x.b*x.d)+1=0

def E4 (x : PhaseCoords11) : Prop := 2*x.g+2*(x.a*x.j+x.b*x.k)+2*(x.c*x.j+x.d*x.k)+2*(x.e*x.g+x.f*x.h)+2*(x.a*x.e+x.b*x.f)+1=0

def E5 (x : PhaseCoords11) : Prop := 2*x.j+2*(x.a*x.j+x.b*x.k)+2*(x.c*x.g+x.d*x.h)+2*(x.a*x.g+x.b*x.h)+2*(x.c*x.e+x.d*x.f)+1=0

def IsPhaseSolution (x : PhaseCoords11) : Prop := x.CircleEquations ∧ x.E1 ∧ x.E2 ∧ x.E3 ∧ x.E4 ∧ x.E5
end PhaseCoords11

def phaseC (x y : ℝ) : ℂ := ⟨x,y⟩
@[simp] theorem phaseC_re (x y : ℝ) : (phaseC x y).re=x := rfl
@[simp] theorem phaseC_im (x y : ℝ) : (phaseC x y).im=y := rfl

def phaseSignal11 (x : PhaseCoords11) : Fin 11 → ℂ :=
  ![1, phaseC x.a x.b, phaseC x.c x.d, phaseC x.e x.f, phaseC x.g x.h,
    phaseC x.j x.k, phaseC x.j x.k, phaseC x.g x.h, phaseC x.e x.f,
    phaseC x.c x.d, phaseC x.a x.b]

def add11 (u v : Fin 11) : Fin 11 := ⟨(u.1+v.1)%11, Nat.mod_lt _ (by norm_num)⟩
def neg11 (u : Fin 11) : Fin 11 := ⟨(11-u.1)%11, Nat.mod_lt _ (by norm_num)⟩
def autocorr11 (z : Fin 11 → ℂ) (r : Fin 11) : ℂ := ∑ t : Fin 11, z (add11 t r) * star (z t)

/-- A normalized even unit-modulus signal with zero autocorrelation at
every nonzero lag. -/
structure ZeroAutocorrSignal11 where
  signal : Fin 11 → ℂ
  normalized : signal 0=1
  even : ∀ t, signal (neg11 t)=signal t
  normSq_one : ∀ t, Complex.normSq (signal t)=1
  zero_autocorr : ∀ r, r≠0 → autocorr11 signal r=0

theorem phaseSignal11_normalized (x : PhaseCoords11) : phaseSignal11 x 0=1 := rfl

theorem phaseSignal11_even (x : PhaseCoords11) : ∀ t, phaseSignal11 x (neg11 t)=phaseSignal11 x t := by
  intro t; fin_cases t <;> rfl

theorem phaseSignal11_normSq_one (x : PhaseCoords11) (hc : x.CircleEquations) :
    ∀ t, Complex.normSq (phaseSignal11 x t)=1 := by
  rcases hc with ⟨hab,hcd,hef,hgh,hjk⟩
  intro t
  fin_cases t <;> simp [phaseSignal11,phaseC,Complex.normSq] <;> nlinarith

private theorem lag1raw (x : PhaseCoords11) : autocorr11 (phaseSignal11 x) 1 =
    phaseC (2*x.a*x.c+2*x.a+2*x.b*x.d+2*x.c*x.e+2*x.d*x.f+2*x.e*x.g+2*x.f*x.h+2*x.g*x.j+2*x.h*x.k+x.j^2+x.k^2) 0 := by
  apply Complex.ext <;> norm_num [autocorr11,phaseSignal11,phaseC,add11,Fin.sum_univ_succ] <;> ring
private theorem lag2raw (x : PhaseCoords11) : autocorr11 (phaseSignal11 x) 2 =
    phaseC (x.a^2+x.b^2+2*x.a*x.e+2*x.b*x.f+2*x.c*x.g+2*x.c+2*x.d*x.h+2*x.e*x.j+2*x.f*x.k+2*x.g*x.j+2*x.h*x.k) 0 := by
  apply Complex.ext <;> norm_num [autocorr11,phaseSignal11,phaseC,add11,Fin.sum_univ_succ] <;> ring
private theorem lag3raw (x : PhaseCoords11) : autocorr11 (phaseSignal11 x) 3 =
    phaseC (2*x.a*x.c+2*x.a*x.g+2*x.b*x.d+2*x.b*x.h+2*x.c*x.j+2*x.d*x.k+2*x.e*x.j+2*x.e+2*x.f*x.k+x.g^2+x.h^2) 0 := by
  apply Complex.ext <;> norm_num [autocorr11,phaseSignal11,phaseC,add11,Fin.sum_univ_succ] <;> ring
private theorem lag4raw (x : PhaseCoords11) : autocorr11 (phaseSignal11 x) 4 =
    phaseC (2*x.a*x.e+2*x.a*x.j+2*x.b*x.f+2*x.b*x.k+x.c^2+2*x.c*x.j+x.d^2+2*x.d*x.k+2*x.e*x.g+2*x.f*x.h+2*x.g) 0 := by
  apply Complex.ext <;> norm_num [autocorr11,phaseSignal11,phaseC,add11,Fin.sum_univ_succ] <;> ring
private theorem lag5raw (x : PhaseCoords11) : autocorr11 (phaseSignal11 x) 5 =
    phaseC (2*x.a*x.g+2*x.a*x.j+2*x.b*x.h+2*x.b*x.k+2*x.c*x.e+2*x.c*x.g+2*x.d*x.f+2*x.d*x.h+x.e^2+x.f^2+2*x.j) 0 := by
  apply Complex.ext <;> norm_num [autocorr11,phaseSignal11,phaseC,add11,Fin.sum_univ_succ] <;> ring

theorem phaseSolution_autocorr1_zero (x : PhaseCoords11) (hs : x.IsPhaseSolution) : autocorr11 (phaseSignal11 x) 1=0 := by
  rcases hs with ⟨⟨hab,hcd,hef,hgh,hjk⟩,h1,h2,h3,h4,h5⟩
  have h1' : 2*x.a+2*(x.a*x.c+x.b*x.d)+2*(x.c*x.e+x.d*x.f)+2*(x.e*x.g+x.f*x.h)+2*(x.g*x.j+x.h*x.k)+1=0 := h1
  rw [lag1raw]; apply Complex.ext <;> simp [phaseC]; nlinarith [h1',hjk]
theorem phaseSolution_autocorr2_zero (x : PhaseCoords11) (hs : x.IsPhaseSolution) : autocorr11 (phaseSignal11 x) 2=0 := by
  rcases hs with ⟨⟨hab,hcd,hef,hgh,hjk⟩,h1,h2,h3,h4,h5⟩
  have h2' : 2*x.c+2*(x.a*x.e+x.b*x.f)+2*(x.c*x.g+x.d*x.h)+2*(x.e*x.j+x.f*x.k)+2*(x.g*x.j+x.h*x.k)+1=0 := h2
  rw [lag2raw]; apply Complex.ext <;> simp [phaseC]; nlinarith [h2',hab]
theorem phaseSolution_autocorr3_zero (x : PhaseCoords11) (hs : x.IsPhaseSolution) : autocorr11 (phaseSignal11 x) 3=0 := by
  rcases hs with ⟨⟨hab,hcd,hef,hgh,hjk⟩,h1,h2,h3,h4,h5⟩
  have h3' : 2*x.e+2*(x.a*x.g+x.b*x.h)+2*(x.c*x.j+x.d*x.k)+2*(x.e*x.j+x.f*x.k)+2*(x.a*x.c+x.b*x.d)+1=0 := h3
  rw [lag3raw]; apply Complex.ext <;> simp [phaseC]; nlinarith [h3',hgh]
theorem phaseSolution_autocorr4_zero (x : PhaseCoords11) (hs : x.IsPhaseSolution) : autocorr11 (phaseSignal11 x) 4=0 := by
  rcases hs with ⟨⟨hab,hcd,hef,hgh,hjk⟩,h1,h2,h3,h4,h5⟩
  have h4' : 2*x.g+2*(x.a*x.j+x.b*x.k)+2*(x.c*x.j+x.d*x.k)+2*(x.e*x.g+x.f*x.h)+2*(x.a*x.e+x.b*x.f)+1=0 := h4
  rw [lag4raw]; apply Complex.ext <;> simp [phaseC]; nlinarith [h4',hcd]
theorem phaseSolution_autocorr5_zero (x : PhaseCoords11) (hs : x.IsPhaseSolution) : autocorr11 (phaseSignal11 x) 5=0 := by
  rcases hs with ⟨⟨hab,hcd,hef,hgh,hjk⟩,h1,h2,h3,h4,h5⟩
  have h5' : 2*x.j+2*(x.a*x.j+x.b*x.k)+2*(x.c*x.g+x.d*x.h)+2*(x.a*x.g+x.b*x.h)+2*(x.c*x.e+x.d*x.f)+1=0 := h5
  rw [lag5raw]; apply Complex.ext <;> simp [phaseC]; nlinarith [h5',hef]

theorem phaseSignal11_lag_symmetry (x : PhaseCoords11) :
    autocorr11 (phaseSignal11 x) 6=autocorr11 (phaseSignal11 x) 5 ∧
    autocorr11 (phaseSignal11 x) 7=autocorr11 (phaseSignal11 x) 4 ∧
    autocorr11 (phaseSignal11 x) 8=autocorr11 (phaseSignal11 x) 3 ∧
    autocorr11 (phaseSignal11 x) 9=autocorr11 (phaseSignal11 x) 2 ∧
    autocorr11 (phaseSignal11 x) 10=autocorr11 (phaseSignal11 x) 1 := by
  constructor
  · apply Complex.ext <;> norm_num [autocorr11,phaseSignal11,phaseC,add11,Fin.sum_univ_succ] <;> ring
  constructor
  · apply Complex.ext <;> norm_num [autocorr11,phaseSignal11,phaseC,add11,Fin.sum_univ_succ] <;> ring
  constructor
  · apply Complex.ext <;> norm_num [autocorr11,phaseSignal11,phaseC,add11,Fin.sum_univ_succ] <;> ring
  constructor
  · apply Complex.ext <;> norm_num [autocorr11,phaseSignal11,phaseC,add11,Fin.sum_univ_succ] <;> ring
  · apply Complex.ext <;> norm_num [autocorr11,phaseSignal11,phaseC,add11,Fin.sum_univ_succ] <;> ring

theorem phaseSolution_all_nonzero_autocorr_zero (x : PhaseCoords11) (hs : x.IsPhaseSolution) :
    ∀ r : Fin 11, r≠0 → autocorr11 (phaseSignal11 x) r=0 := by
  have h1:=phaseSolution_autocorr1_zero x hs; have h2:=phaseSolution_autocorr2_zero x hs
  have h3:=phaseSolution_autocorr3_zero x hs; have h4:=phaseSolution_autocorr4_zero x hs
  have h5:=phaseSolution_autocorr5_zero x hs
  rcases phaseSignal11_lag_symmetry x with ⟨h6,h7,h8,h9,h10⟩
  intro r hr; fin_cases r
  · exact (hr rfl).elim
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · simpa using h6.trans h5
  · simpa using h7.trans h4
  · simpa using h8.trans h3
  · simpa using h9.trans h2
  · simpa using h10.trans h1

def phaseSolutionToZeroAutocorrSignal11 (x : PhaseCoords11) (hs : x.IsPhaseSolution) : ZeroAutocorrSignal11 where
  signal:=phaseSignal11 x
  normalized:=phaseSignal11_normalized x
  even:=phaseSignal11_even x
  normSq_one:=phaseSignal11_normSq_one x hs.1
  zero_autocorr:=phaseSolution_all_nonzero_autocorr_zero x hs

def BiunimodularCriterion11 (z : Fin 11 → ℂ) : Prop := z 0=1 ∧ (∀ t, Complex.normSq (z t)=1) ∧ (∀ r, r≠0 → autocorr11 z r=0)

theorem phaseSolution_biunimodularCriterion11 (x : PhaseCoords11) (hs : x.IsPhaseSolution) : BiunimodularCriterion11 (phaseSignal11 x) :=
  ⟨phaseSignal11_normalized x, phaseSignal11_normSq_one x hs.1, phaseSolution_all_nonzero_autocorr_zero x hs⟩

end Biunimodular.F11
