/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.PerfectComplexPushforward
public import Mathlib.Data.ZMod.Basic

/-! # Consumers of the original perfect-complex projection results -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.projectiveSpaceOver

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable example (X : Scheme.{u}) [CompactSpace X] :
    perfectComplexToDerivedPlus X ⋙ DerivedCategory.Plus.ι ≅
      (perfectComplexes X).ι ⋙ DerivedCategory.Q :=
  perfectComplexToDerivedPlusFactors X

example {S T : Scheme.{u}} [CompactSpace S] (g : T ⟶ S) [Flat g]
    (K : (perfectComplexes (projectiveSpaceOver 1 S)).FullSubcategory) :
    (projectiveLinePerfectComplexFlatBaseChangeIso g).hom.app K =
      (projectiveLineFlatBaseChangePlus g).app
        ((perfectComplexToDerivedPlus (projectiveSpaceOver 1 S)).obj K) :=
  projectiveLinePerfectComplexFlatBaseChangeIso_hom_app g K

example (K : (perfectComplexes (projectiveSpaceOver 1 (Spec (.of (ZMod 1))))).FullSubcategory) :
    (linePerfectComplexSelfBaseChangeIso (.of (ZMod 1))).hom.app K =
      (lineSelfBaseChangePlus (.of (ZMod 1))).app
        ((perfectComplexToDerivedPlus (projectiveSpaceOver 1 (Spec (.of (ZMod 1))))).obj K) :=
  linePerfectComplexSelfBaseChangeIso_hom_app _ K

example (S : Scheme.{u}) (K : CochainComplex.Plus (projectiveSpaceOver 1 S).Modules)
    (hK : RingedSpace.IsPerfectComplex (X := (projectiveSpaceOver 1 S).toRingedSpace) K.obj)
    (hfl : ∀ n, TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf _).obj (K.obj.X n))) :
    RingedSpace.IsPerfectComplex (X := S.toRingedSpace)
      (((Scheme.Modules.pushforward (projectiveSpaceOver 1 S ↘ S)).mapHomologicalComplex
        (.up ℤ)).obj K.obj) :=
  isPerfect_projectiveLinePushforward_of_termwiseFlasque S K hK hfl

#print axioms perfectComplexToDerivedPlusFactors
#print axioms projectiveLinePerfectComplexFlatBaseChangeIso_hom_app
#print axioms linePerfectComplexSelfBaseChangeIso_hom_app
#print axioms isPerfect_projectiveLinePushforward_of_termwiseFlasque
