/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.CrossMultiplication

/-! # The determinant section on the relative square of the projective line

The two tautological coordinate pairs define the actual section
`T₀ ⊗ T₁ - T₁ ⊗ T₀` of the tensor product of the positive twists from the
two factors. This is the equation to compare with the relative diagonal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.RelativeVeryAmple Stacks.ProjectiveSpaceModuli

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => pullback π π

abbrev projectiveLineFirstTuple : GeneratingTuple Q 1 :=
  pullbackTuple (pullback.fst π π) (tautological (projectiveSpaceOver.toIntegralAtUniverse 1 X))

abbrev projectiveLineSecondTuple : GeneratingTuple Q 1 :=
  pullbackTuple (pullback.snd π π) (tautological (projectiveSpaceOver.toIntegralAtUniverse 1 X))

/-- The positive twist from the first factor of the relative square. -/
abbrev projectiveLineFirstPositiveTwist : (Q).Modules :=
  (projectiveLineFirstTuple X).bundle

/-- The positive twist from the second factor of the relative square. -/
abbrev projectiveLineSecondPositiveTwist : (Q).Modules :=
  (projectiveLineSecondTuple X).bundle

/-- The external tensor product of the two positive twists. -/
abbrev projectiveLineDiagonalPositiveTwist : (Q).Modules :=
  Modules.tensorObj (projectiveLineFirstPositiveTwist X) (projectiveLineSecondPositiveTwist X)

def projectiveLineCoordinateTensor (i j : Fin 2) :
    Γ(projectiveLineDiagonalPositiveTwist X, ⊤) :=
  Stacks.SheafOfModules.tensorSectionsAt (Q).sheaf.obj (Q).ringCatSheaf.property (op ⊤)
    (projectiveLineFirstPositiveTwist X) (projectiveLineSecondPositiveTwist X)
    ((projectiveLineFirstTuple X).coord i) ((projectiveLineSecondTuple X).coord j)

/-- The alternating determinant of the two homogeneous coordinate pairs. -/
def projectiveLineDiagonalDeterminant : Γ(projectiveLineDiagonalPositiveTwist X, ⊤) :=
  projectiveLineCoordinateTensor X 0 1 - projectiveLineCoordinateTensor X 1 0

end AlgebraicGeometry.Scheme
