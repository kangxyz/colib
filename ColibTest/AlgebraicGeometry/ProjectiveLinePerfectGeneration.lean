/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.PositiveDerivedUnit
public import Colib.AlgebraicGeometry.ProjectiveLine.NegativeDerivedCoefficient
public import Mathlib.Data.ZMod.Basic

/-! # Perfect-coefficient consumers for the projective-line projection -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open AlgebraicGeometry.projectiveSpaceOver

universe u

attribute [local instance] HasDerivedCategory.standard

local instance (S : Scheme.{u}) :
    (modulePullback (projectiveSpaceOver 1 S ↘ S).toLRSHom.toShHom).PreservesHomology :=
  preservesHomology_modulePullback_of_isFlat _ (fun x => Flat.stalkMap _ x)

example (S : Scheme.{u}) (K : DerivedCategory.Plus S.Modules)
    (hK : RingedSpace.IsPerfect (X := S.toRingedSpace) K.obj) :
    IsIso ((modulePullbackPushforwardAdjunction
      (projectiveSpaceOver 1 S ↘ S).toLRSHom.toShHom).rightDerivedFunctorPlus.unit.app K) :=
  isIso_projectiveLineDerivedUnitPlus S K hK

example (S : Scheme.{u}) (K : DerivedCategory.Plus S.Modules)
    (hK : RingedSpace.IsPerfect (X := S.toRingedSpace) K.obj) :
    IsZero ((Scheme.Modules.pushforward
      (projectiveSpaceOver 1 S ↘ S)).rightDerivedFunctorPlus.obj
      ((negativePullback S).rightDerivedFunctorPlus.obj K)) :=
  isZero_projectiveLineNegativePullbackPlus S K hK

example (K : DerivedCategory.Plus (Spec (.of (ZMod 1))).Modules)
    (hK : RingedSpace.IsPerfect (X := (Spec (.of (ZMod 1))).toRingedSpace) K.obj) :
    IsZero ((Scheme.Modules.pushforward
      (projectiveSpaceOver 1 (Spec (.of (ZMod 1))) ↘
        Spec (.of (ZMod 1)))).rightDerivedFunctorPlus.obj
      ((negativePullback (Spec (.of (ZMod 1)))).rightDerivedFunctorPlus.obj K)) :=
  isZero_projectiveLineNegativePullbackPlus _ K hK

#print axioms isIso_projectiveLineDerivedUnitPlus
#print axioms isZero_projectiveLineNegativePullbackPlus
