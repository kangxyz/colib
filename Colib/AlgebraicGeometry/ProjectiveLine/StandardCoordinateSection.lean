/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.ProjTwistSection.Basic
public import StacksFrontier.AlgebraicGeometry.ProjInclusionDegreeSection.Unit
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionFiniteFamily
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away

/-!
# The homogeneous coordinate section of the canonical projective line

The section is the native global (T_i/1), pulled back from the integral model.
Multiplication acts from the canonical negative twist to the original module.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open Stacks.ProjTwistSection
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionFiniteFamily

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual integral homogeneous coordinate section of the hyperplane bundle. -/
def integralCoordinateSection (i : Fin 2) :
    (twistingModule (polyGrading (ULift.{u} ℤ) 1) 1).sections :=
  homogeneousSection (polyGrading (ULift.{u} ℤ) 1) (MvPolynomial.X i)
    (X_mem_one (ULift.{u} ℤ) 1 i)

/-- The original coordinate section on the relative native line. -/
def coordinateSection (S : Scheme.{u}) (i : Fin 2) : (twistOver 1 S 1).sections :=
  Stacks.SheafOfModules.sectionsOfTop (twistOver 1 S 1)
    (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection
      (projectiveSpaceOver.toIntegralAtUniverse 1 S)
      (twistingModule (polyGrading (ULift.{u} ℤ) 1) 1)
      ((integralCoordinateSection i).eval (op ⊤)))

/-- Multiplication by the actual coordinate section on the right negative twist. -/
def negativeTwistCoordinate (S : Scheme.{u}) (i : Fin 2)
    (F : (projectiveSpaceOver 1 S).Modules) :=
  twistSectionMulNegOne 1 S F (coordinateSection S i)


variable (S : Scheme.{u})

local instance : MonoidalCategory (projectiveSpaceOver 1 S).Modules :=
  SheafOfModules.monoidalCategorySheafTensor (projectiveSpaceOver 1 S).sheaf

/-- The native coefficient morphism is a natural transformation in the module. -/
def negativeTwistCoordinateNat (i : Fin 2) :
    tensorRight (twistOver 1 S (-1)) ⟶ 𝟭 (projectiveSpaceOver 1 S).Modules where
  app F := negativeTwistCoordinate S i F
  naturality _ _ f := twistSectionMulNegOne_naturality 1 S f (coordinateSection S i)


end AlgebraicGeometry.Scheme.ProjectiveLine
