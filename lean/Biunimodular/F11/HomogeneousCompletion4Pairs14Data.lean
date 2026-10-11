/-
Copyright (c) 2026 Michael Brackx. All rights reserved.
Released under the Apache 2.0 license; see LICENSE at the project root.
SPDX-License-Identifier: Apache-2.0
-/

import Biunimodular.F11.HomogeneousCompletion4BasisData

set_option autoImplicit false
set_option maxRecDepth 1000000
namespace Biunimodular.F11

/-! Generated exact data.
-/

def homogeneousCompletion4Pair5_8U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_8V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_8D1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8D2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8D3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8D4 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8D5 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨10, 34, 14, -12, -6⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_8D6 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-4, 16, 20, -6, -6⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_8D7 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8D8 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, -6, 0, 2, 0⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_8D9 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8D10 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8D11 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, -11, -5, 4, 2⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_8D12 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨0, 4, 0, -1, 0⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_8D13 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8D14 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8D15 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8D : Fin 15 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair5_8D1, homogeneousCompletion4Pair5_8D2, homogeneousCompletion4Pair5_8D3, homogeneousCompletion4Pair5_8D4, homogeneousCompletion4Pair5_8D5, homogeneousCompletion4Pair5_8D6, homogeneousCompletion4Pair5_8D7, homogeneousCompletion4Pair5_8D8, homogeneousCompletion4Pair5_8D9, homogeneousCompletion4Pair5_8D10, homogeneousCompletion4Pair5_8D11, homogeneousCompletion4Pair5_8D12, homogeneousCompletion4Pair5_8D13, homogeneousCompletion4Pair5_8D14, homogeneousCompletion4Pair5_8D15]

def homogeneousCompletion4Pair5_8W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8W3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_8W : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair5_8W1, homogeneousCompletion4Pair5_8W2, homogeneousCompletion4Pair5_8W3]


def homogeneousCompletion4Pair5_8SPTerms :=
  [(homogeneousCompletion4Pair5_8U, homogeneousCompletion4G 4), (rationalSparseNeg homogeneousCompletion4Pair5_8V, homogeneousCompletion4G 7)] ++
    (List.ofFn fun k : Fin 15 => (rationalSparseNeg (homogeneousCompletion4Pair5_8D k), homogeneousCompletion4G k))

def homogeneousCompletion4Pair5_8LastTerms :=
  [(homogeneousCompletion4Pair5_8U, homogeneousCompletion4M (Fin.last 3) 4),
    (rationalSparseNeg homogeneousCompletion4Pair5_8V, homogeneousCompletion4M (Fin.last 3) 7)] ++
    (List.ofFn fun k : Fin 15 =>
      (rationalSparseNeg (homogeneousCompletion4Pair5_8D k), homogeneousCompletion4M (Fin.last 3) k)) ++
    (List.ofFn fun k : Fin 3 =>
      (rationalSparseNeg (homogeneousCompletion4Pair5_8W k), homogeneousCompletion4Original k.castSucc))

def homogeneousCompletion4Pair5_9U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_9V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_9D1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_9D2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_9D3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_9D4 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_9D5 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-3, 1, 1, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨3, -2, -7, 1, 2⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨-4, 2, 7, -1, -2⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨60, 77, -14, -25, -3⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_9D6 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-26, 46, 70, -18, -20⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_9D7 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-10, 0, 10, 0, -2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_9D8 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨4, -14, 6, 4, -2⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_9D9 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨2, -6, 0, 2, 0⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_9D10 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_9D11 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨15, -35, -37, 13, 11⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_9D12 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-4, 15, 6, -5, -2⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_9D13 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_9D14 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_9D15 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_9D : Fin 15 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair5_9D1, homogeneousCompletion4Pair5_9D2, homogeneousCompletion4Pair5_9D3, homogeneousCompletion4Pair5_9D4, homogeneousCompletion4Pair5_9D5, homogeneousCompletion4Pair5_9D6, homogeneousCompletion4Pair5_9D7, homogeneousCompletion4Pair5_9D8, homogeneousCompletion4Pair5_9D9, homogeneousCompletion4Pair5_9D10, homogeneousCompletion4Pair5_9D11, homogeneousCompletion4Pair5_9D12, homogeneousCompletion4Pair5_9D13, homogeneousCompletion4Pair5_9D14, homogeneousCompletion4Pair5_9D15]

def homogeneousCompletion4Pair5_9W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_9W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_9W3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_9W : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair5_9W1, homogeneousCompletion4Pair5_9W2, homogeneousCompletion4Pair5_9W3]


def homogeneousCompletion4Pair5_9SPTerms :=
  [(homogeneousCompletion4Pair5_9U, homogeneousCompletion4G 4), (rationalSparseNeg homogeneousCompletion4Pair5_9V, homogeneousCompletion4G 8)] ++
    (List.ofFn fun k : Fin 15 => (rationalSparseNeg (homogeneousCompletion4Pair5_9D k), homogeneousCompletion4G k))

def homogeneousCompletion4Pair5_9LastTerms :=
  [(homogeneousCompletion4Pair5_9U, homogeneousCompletion4M (Fin.last 3) 4),
    (rationalSparseNeg homogeneousCompletion4Pair5_9V, homogeneousCompletion4M (Fin.last 3) 8)] ++
    (List.ofFn fun k : Fin 15 =>
      (rationalSparseNeg (homogeneousCompletion4Pair5_9D k), homogeneousCompletion4M (Fin.last 3) k)) ++
    (List.ofFn fun k : Fin 3 =>
      (rationalSparseNeg (homogeneousCompletion4Pair5_9W k), homogeneousCompletion4Original k.castSucc))

def homogeneousCompletion4Pair5_10U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 1, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 1, 1, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10D1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_10D2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_10D3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_10D4 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_10D5 : RationalSparsePolynomial :=
  ⟨300763, by decide, [
    ⟨⟨601526, 3007630, 1203052, -1203052, -601526⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
    ⟨⟨-1203052, 1203052, 1503815, -300763, -300763⟩, ⟨0, 0, 2, 0, 0, 0⟩⟩,
    ⟨⟨1203052, -902289, -1203052, 300763, 300763⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩,
    ⟨⟨-1203052, 601526, 2105341, -300763, -601526⟩, ⟨0, 0, 1, 0, 1, 0⟩⟩,
    ⟨⟨8120601, -26467144, -25564855, 11128231, 7218312⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-16548824, -51739176, -21244248, 18506726, 9253242⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨-45029226, 21026744, 54014462, -8467728, -13129052⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨548525665, -740527074, -983505958, 280603499, 268772493⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10D6 : RationalSparsePolynomial :=
  ⟨300763, by decide, [
    ⟨⟨-3007630, 1203052, 4812208, -601526, -1203052⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
    ⟨⟨-16842728, 8421364, 22256462, -3609156, -5413734⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-12371684, 9786020, 13727362, -3896452, -3142300⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨30085652, -251510049, -215861233, 81910636, 76900586⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10D7 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-28, 8, 24, -4, -4⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10D8 : RationalSparsePolynomial :=
  ⟨4489, by decide, [
    ⟨⟨8978, -26934, 0, 8978, 0⟩, ⟨0, 1, 0, 0, 0, 1⟩⟩,
    ⟨⟨80802, -80802, -80802, 26934, 17956⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-63650, 110952, 78658, -35644, -20636⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨-1195160, 1003716, 2145995, -420867, -561864⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10D9 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-4, -52, -32, 20, 12⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10D10 : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨-8, -16, -16, 4, 8⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10D11 : RationalSparsePolynomial :=
  ⟨300763, by decide, [
    ⟨⟨8421364, -11128231, -12632046, 3909919, 3308393⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨-4058056, 14427646, 13139303, -5364355, -4102946⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨11285413, 23418845, 1671583, -8155039, -2003367⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨170208429, 99588180, -62559318, -35950934, 1489480⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10D12 : RationalSparsePolynomial :=
  ⟨300763, by decide, [
    ⟨⟨-3909919, 3609156, 4511445, -1503815, -1203052⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨-6275622, -12793650, 1310788, 4197215, 435433⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨20801031, -31308805, -48614146, 13435596, 12878483⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10D13 : RationalSparsePolynomial :=
  ⟨67, by decide, [
    ⟨⟨-1354, -7046, -3700, 2506, 1472⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10D14 : RationalSparsePolynomial :=
  ⟨67, by decide, [
    ⟨⟨-2434, -582, 1192, 186, -118⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10D15 : RationalSparsePolynomial :=
  ⟨4489, by decide, [
    ⟨⟨-377571, 222678, 464330, -87605, -111731⟩, ⟨0, 0, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_10D : Fin 15 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair5_10D1, homogeneousCompletion4Pair5_10D2, homogeneousCompletion4Pair5_10D3, homogeneousCompletion4Pair5_10D4, homogeneousCompletion4Pair5_10D5, homogeneousCompletion4Pair5_10D6, homogeneousCompletion4Pair5_10D7, homogeneousCompletion4Pair5_10D8, homogeneousCompletion4Pair5_10D9, homogeneousCompletion4Pair5_10D10, homogeneousCompletion4Pair5_10D11, homogeneousCompletion4Pair5_10D12, homogeneousCompletion4Pair5_10D13, homogeneousCompletion4Pair5_10D14, homogeneousCompletion4Pair5_10D15]

def homogeneousCompletion4Pair5_10W1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_10W2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_10W3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_10W : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair5_10W1, homogeneousCompletion4Pair5_10W2, homogeneousCompletion4Pair5_10W3]


def homogeneousCompletion4Pair5_10SPTerms :=
  [(homogeneousCompletion4Pair5_10U, homogeneousCompletion4G 4), (rationalSparseNeg homogeneousCompletion4Pair5_10V, homogeneousCompletion4G 9)] ++
    (List.ofFn fun k : Fin 15 => (rationalSparseNeg (homogeneousCompletion4Pair5_10D k), homogeneousCompletion4G k))

def homogeneousCompletion4Pair5_10LastTerms :=
  [(homogeneousCompletion4Pair5_10U, homogeneousCompletion4M (Fin.last 3) 4),
    (rationalSparseNeg homogeneousCompletion4Pair5_10V, homogeneousCompletion4M (Fin.last 3) 9)] ++
    (List.ofFn fun k : Fin 15 =>
      (rationalSparseNeg (homogeneousCompletion4Pair5_10D k), homogeneousCompletion4M (Fin.last 3) k)) ++
    (List.ofFn fun k : Fin 3 =>
      (rationalSparseNeg (homogeneousCompletion4Pair5_10W k), homogeneousCompletion4Original k.castSucc))

def homogeneousCompletion4Pair5_11U : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 1, 1, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11V : RationalSparsePolynomial :=
  ⟨1, by decide, [
    ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 1, 0, 0, 0, 0⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11D1 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_11D2 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_11D3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_11D4 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_11D5 : RationalSparsePolynomial :=
  ⟨67, by decide, [
    ⟨⟨112, 155, 120, -82, -51⟩, ⟨0, 0, 1, 0, 1, 0⟩⟩,
    ⟨⟨-2336, 2778, 3106, -1008, -774⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨237, -144, -239, 55, 53⟩, ⟨0, 0, 0, 2, 0, 0⟩⟩,
    ⟨⟨-366, 191, 364, -79, -81⟩, ⟨0, 0, 0, 1, 1, 0⟩⟩,
    ⟨⟨5197, -2296, -6018, 903, 1422⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨148, -56, -253, 40, 69⟩, ⟨0, 0, 0, 0, 2, 0⟩⟩,
    ⟨⟨-4643, 1822, 6066, -842, -1496⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨37099, -14664, -43891, 6282, 10277⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11D6 : RationalSparsePolynomial :=
  ⟨67, by decide, [
    ⟨⟨64, 548, 394, -200, -144⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-246, 582, 14, -186, -16⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨-15963, 4758, 22690, -1580, -6042⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11D7 : RationalSparsePolynomial :=
  ⟨67, by decide, [
    ⟨⟨424, -222, -522, 82, 118⟩, ⟨0, 0, 0, 0, 1, 1⟩⟩,
    ⟨⟨-5278, 2754, 6673, -1077, -1625⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11D8 : RationalSparsePolynomial :=
  ⟨67, by decide, [
    ⟨⟨292, 38, -338, -8, 80⟩, ⟨0, 0, 1, 0, 0, 1⟩⟩,
    ⟨⟨-782, -490, 1220, 82, -284⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨1192, -3495, -82, 1166, -69⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11D9 : RationalSparsePolynomial :=
  ⟨67, by decide, [
    ⟨⟨208, -28, -294, 20, 68⟩, ⟨0, 0, 0, 1, 0, 1⟩⟩,
    ⟨⟨2439, 160, -1067, -76, 90⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11D10 : RationalSparsePolynomial :=
  ⟨67, by decide, [
    ⟨⟨308, 644, 464, -192, -224⟩, ⟨0, 0, 0, 0, 0, 2⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11D11 : RationalSparsePolynomial :=
  ⟨67, by decide, [
    ⟨⟨-201, 67, 67, 0, 0⟩, ⟨0, 0, 1, 0, 0, 0⟩⟩,
    ⟨⟨268, -201, -268, 67, 67⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨-268, 134, 469, -67, -134⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨13706, -12748, -19418, 4856, 4973⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11D12 : RationalSparsePolynomial :=
  ⟨67, by decide, [
    ⟨⟨-3154, 4174, 3292, -1450, -776⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11D13 : RationalSparsePolynomial :=
  ⟨67, by decide, [
    ⟨⟨234, 270, -46, -78, -24⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11D14 : RationalSparsePolynomial :=
  ⟨67, by decide, [
    ⟨⟨-250, 330, 718, -140, -208⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11D15 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_11D : Fin 15 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair5_11D1, homogeneousCompletion4Pair5_11D2, homogeneousCompletion4Pair5_11D3, homogeneousCompletion4Pair5_11D4, homogeneousCompletion4Pair5_11D5, homogeneousCompletion4Pair5_11D6, homogeneousCompletion4Pair5_11D7, homogeneousCompletion4Pair5_11D8, homogeneousCompletion4Pair5_11D9, homogeneousCompletion4Pair5_11D10, homogeneousCompletion4Pair5_11D11, homogeneousCompletion4Pair5_11D12, homogeneousCompletion4Pair5_11D13, homogeneousCompletion4Pair5_11D14, homogeneousCompletion4Pair5_11D15]

def homogeneousCompletion4Pair5_11W1 : RationalSparsePolynomial :=
  ⟨737, by decide, [
    ⟨⟨-44, -159, 173, 37, -35⟩, ⟨0, 0, 0, 1, 0, 0⟩⟩,
    ⟨⟨54, -82, 278, -18, -88⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11W2 : RationalSparsePolynomial :=
  ⟨737, by decide, [
    ⟨⟨-77, 40, 286, -19, -78⟩, ⟨0, 0, 0, 0, 1, 0⟩⟩,
    ⟨⟨-54, 82, -278, 18, 88⟩, ⟨0, 0, 0, 0, 0, 1⟩⟩
  ]⟩

def homogeneousCompletion4Pair5_11W3 : RationalSparsePolynomial :=
  ⟨1, by decide, []⟩

def homogeneousCompletion4Pair5_11W : Fin 3 → RationalSparsePolynomial :=
  ![homogeneousCompletion4Pair5_11W1, homogeneousCompletion4Pair5_11W2, homogeneousCompletion4Pair5_11W3]


def homogeneousCompletion4Pair5_11SPTerms :=
  [(homogeneousCompletion4Pair5_11U, homogeneousCompletion4G 4), (rationalSparseNeg homogeneousCompletion4Pair5_11V, homogeneousCompletion4G 10)] ++
    (List.ofFn fun k : Fin 15 => (rationalSparseNeg (homogeneousCompletion4Pair5_11D k), homogeneousCompletion4G k))

def homogeneousCompletion4Pair5_11LastTerms :=
  [(homogeneousCompletion4Pair5_11U, homogeneousCompletion4M (Fin.last 3) 4),
    (rationalSparseNeg homogeneousCompletion4Pair5_11V, homogeneousCompletion4M (Fin.last 3) 10)] ++
    (List.ofFn fun k : Fin 15 =>
      (rationalSparseNeg (homogeneousCompletion4Pair5_11D k), homogeneousCompletion4M (Fin.last 3) k)) ++
    (List.ofFn fun k : Fin 3 =>
      (rationalSparseNeg (homogeneousCompletion4Pair5_11W k), homogeneousCompletion4Original k.castSucc))

end Biunimodular.F11
