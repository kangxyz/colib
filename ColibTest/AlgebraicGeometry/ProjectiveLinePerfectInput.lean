/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.PerfectBaseChange
public import Colib.AlgebraicGeometry.ProjectiveLine.PerfectRepresentative
public import Mathlib.Data.ZMod.Basic

/-! # Public API for arbitrary perfect projective-line inputs -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Perfect.BoundedLocallyFreeComplexes
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)

universe u

attribute [local instance] HasDerivedCategory.standard

open projectiveSpaceOver in
example (S : Scheme.{u}) (K : DerivedCategory.Plus (projectiveSpaceOver 1 S).Modules)
    (hK : RingedSpace.IsPerfect (X := (projectiveSpaceOver 1 S).toRingedSpace)
      (DerivedCategory.Plus.ι.obj K)) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      (DerivedCategory.Plus.ι.obj
        ((Scheme.Modules.pushforward (projectiveSpaceOver 1 S ↘ S)).rightDerivedFunctorPlus.obj
          K)) :=
  isPerfect_projectiveLineDerivedPushforwardPlus S K hK

open projectiveSpaceOver in
example (K : DerivedCategory.Plus (projectiveSpaceOver 1 (Spec (.of (ZMod 1)))).Modules)
    (hK : RingedSpace.IsPerfect
      (X := (projectiveSpaceOver 1 (Spec (.of (ZMod 1)))).toRingedSpace)
      (DerivedCategory.Plus.ι.obj K)) :
    ∃ E : CochainComplex (projectiveSpaceOver 1 (Spec (.of (ZMod 1)))).Modules ℤ,
      ∃ hE : boundedFiniteLocallyFreeComplex (projectiveSpaceOver 1 (Spec (.of (ZMod 1)))) E,
        Nonempty (DerivedCategory.Plus.Q.obj ⟨E, hE.1.1⟩ ≅ K) :=
  exists_projectiveLinePerfectRepresentative (.of (ZMod 1)) K hK

open projectiveSpaceOver in
example {S T : Scheme.{u}} (g : T ⟶ S) (E : DerivedCategory (projectiveSpaceOver 1 S).Modules)
    (hE : RingedSpace.IsPerfect (X := (projectiveSpaceOver 1 S).toRingedSpace) E) :
    IsIso (derivedBaseChangeMap (projectiveSpaceOverMap 1 g).toLRSHom.toShHom
      (projectiveSpaceOver 1 T ↘ T).toLRSHom.toShHom
      (projectiveSpaceOver 1 S ↘ S).toLRSHom.toShHom g.toLRSHom.toShHom
      (comp_toShHom_of_comm (isPullback_projectiveSpaceOverMap 1 g).w) E) :=
  isIso_projectiveLinePerfectBaseChange g E hE

#print axioms AlgebraicGeometry.projectiveSpaceOver.isPerfect_projectiveLineDerivedPushforwardPlus
#print axioms AlgebraicGeometry.projectiveSpaceOver.exists_projectiveLinePerfectRepresentative
#print axioms AlgebraicGeometry.projectiveSpaceOver.isIso_projectiveLinePerfectBaseChange
