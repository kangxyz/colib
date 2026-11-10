/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.Plus.StableGeneralLinearPlus
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic

/-! # Original all-ring plus-certificate consumers
These tests retain the original based map and mixed-universe coefficient maps.
The matrix example is a noncommutative ring, while `ZMod 1` is the zero ring.
-/

open CategoryTheory Topology FundamentalGroupoid
open ModuleCat.FiniteProjective.StableCompletion
noncomputable section
universe u
variable (R : Type u) [Ring R]

example : IsPlusConstruction.{u, u + 1, u + 1}
    (stableZeroMap R) (basepointPath R) (stableElementaryPiOneSubgroup R) :=
  stableZeroMap_isPlusConstruction R

example : Function.Surjective (basedPiOneMap (stableZeroMap R) (basepointPath R)) :=
  (stableZeroMap_isPlusConstruction R).surjective

example : (basedPiOneMap (stableZeroMap R) (basepointPath R)).ker =
    (StableGeneralLinear.elementary R).map
      (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R)).toMonoidHom :=
  (stableZeroMap_isPlusConstruction R).kernelEq

example : (stableElementaryPiOneSubgroup R).Normal :=
  (stableZeroMap_isPlusConstruction R).normal

example : Group.IsPerfect (stableElementaryPiOneSubgroup R) :=
  (stableZeroMap_isPlusConstruction R).perfect

example (A : LocalCoefficients.System.{u + 1, u + 1} (ZeroComponent R)) :
    QuasiIso (LocalCoefficients.UniverseLift.chainMap.{u, u + 1, u + 1}
      (stableZeroMap R) A) :=
  (stableZeroMap_isPlusConstruction R).localCoefficients A

example (A : LocalCoefficients.System.{u + 1, u + 1} (ZeroComponent R)) (n : ℕ) :
    IsIso (LocalCoefficients.UniverseLift.homologyMap.{u, u + 1, u + 1}
      (stableZeroMap R) A n) :=
  (stableZeroMap_isPlusConstruction R).homologyMap_isIso A n

example : basedPiOneMap (stableZeroMap R) (basepointPath R) =
    (pathTransportMulEquiv (basepointPath R) 0).toMonoidHom.comp
      (HomotopyGroup.piMap 0 (stableZeroMap R) rfl) := rfl

example : basedPiOneMap (stableZeroMap R) (basepointPath R) = stablePiOneMap R :=
  basedPiOneMap_stableZeroMap R

example : IsPlusConstruction.{0, 1, 1} (stableZeroMap (Matrix (Fin 2) (Fin 2) (ZMod 3)))
    (basepointPath _) (stableElementaryPiOneSubgroup _) :=
  stableZeroMap_isPlusConstruction _

example : IsPlusConstruction.{0, 1, 1} (stableZeroMap (ZMod 1)) (basepointPath _)
    (stableElementaryPiOneSubgroup _) :=
  stableZeroMap_isPlusConstruction _

example : (1 : ZMod 1) = 0 := Subsingleton.elim _ _

example : ∃ A B : Matrix (Fin 2) (Fin 2) (ZMod 3), A * B ≠ B * A :=
  ⟨(fun i j => if i = 0 ∧ j = 1 then 1 else 0),
    (fun i j => if i = 1 ∧ j = 0 then 1 else 0), by decide⟩
