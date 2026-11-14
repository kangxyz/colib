/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateChartFrame
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Restriction
public import StacksFrontier.AlgebraicGeometry.Constructions.PullbackSectionMultiplication

/-! # The native chart frame on the negative twist of a module -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.AlgebraicGeometry.PullbackSectionMul
open Stacks.RingedSpace
open Stacks.RelativeVeryAmple (tensorModules)
open Stacks.SheafOfModules (sheafifyWhiskerLeft)
open Stacks.PullbackTensorCoherence

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] schemeTensorStrict

set_option backward.isDefEq.respectTransparency false in
/-- The multiplier in the original negative twist is the monoidal multiplier of [Stacks, 01CA]. -/
theorem twistNegOneMulSection_eq_whisker (S : Scheme.{u})
    (F : (projectiveSpaceOver 1 S).Modules) (s : (twistOver 1 S 1).sections) :
    let M := tensorModules (projectiveSpaceOver 1 S) F (twistOver 1 S (-1))
    twistNegOneMulSection 1 S F s =
      (ρ_ M).inv ≫ M ◁ sectionHom (twistOver 1 S 1) s := by
  let Y := projectiveSpaceOver 1 S
  let M := tensorModules Y F (twistOver 1 S (-1))
  let τ := sectionHom (twistOver 1 S 1) s
  let hO := Stacks.SheafInternalHom.isSheaf_structureRingPresheaf Y
  have h := twistNegOneMulSection_eq_map 1 S F s
  change twistNegOneMulSection 1 S F s =
    (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor Y.presheaf hO M).inv ≫
      sheafifyWhiskerLeft Y.presheaf hO M τ at h
  exact h.trans (congrArg₂ CategoryStruct.comp
    (congrArg Iso.inv (tensorProductRightUnitor_eq Y M))
    (sheafifyWhiskerLeft_eq_whiskerLeft Y.presheaf hO M τ))

set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by the chart's own homogeneous coordinate trivializes the actual
negative twist after restriction to that chart. -/
theorem isIso_pullback_negativeTwistCoordinate (S : Scheme.{u}) (i : Fin 2)
    (F : (projectiveSpaceOver 1 S).Modules) :
    IsIso ((Scheme.Modules.pullback (standardChart S i).ι).map
      (negativeTwistCoordinate S i F)) := by
  let U := standardChart S i
  let f := U.ι
  let g := f.toLRSHom.toShHom
  let M := tensorModules (projectiveSpaceOver 1 S) F (twistOver 1 S (-1))
  let L := twistOver 1 S 1
  let τ := sectionHom L (coordinateSection S i)
  let : IsIso ((pullbackFunctor g).map τ) :=
    Stacks.AlgebraicGeometry.ProjInvertibleLocus.isIso_pullback_map_of_isIso_over U τ
      (isIso_coordinateSection_over S i)
  have h := pullbackTensorComparison_mulSection g M L τ
  have hmul := twistNegOneMulSection_eq_whisker S F (coordinateSection S i)
  rw [← hmul] at h
  let : IsIso (pullbackTensorComparison g M L) := isIso_pullbackTensorComparison g M L
  have hh : IsIso ((pullbackFunctor g).map (twistNegOneMulSection 1 S F
      (coordinateSection S i)) ≫ pullbackTensorComparison g M L) := by
    rw [h]
    infer_instance
  have hi : IsIso ((pullbackFunctor g).map (twistNegOneMulSection 1 S F
      (coordinateSection S i))) :=
    (isIso_comp_right_iff _ _).1 hh
  unfold negativeTwistCoordinate
  rw [twistSectionMulNegOne_eq_comp]
  change IsIso ((Scheme.Modules.pullback f).map (_ ≫ _))
  rw [Functor.map_comp]
  let : IsIso ((Scheme.Modules.pullback f).map (twistNegOneMulSection 1 S F
      (coordinateSection S i))) := hi
  infer_instance

end AlgebraicGeometry.Scheme.ProjectiveLine
