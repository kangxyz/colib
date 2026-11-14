/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.PerfectFlatBaseChangePlus
public import Mathlib.Data.ZMod.Basic

/-! # Public API for general open base change and flat and self-base change on the line -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.projectiveSpaceOver

universe u

attribute [local instance] HasDerivedCategory.standard

example {X X' S T : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    [IsOpenImmersion g] [IsOpenImmersion a] (h : IsPullback a b f g)
    (K : DerivedCategory.Plus X.Modules) :
    IsIso ((Scheme.Modules.openSquareBaseChangePlus h).app K) :=
  Scheme.Modules.isIso_openSquareBaseChangePlus_app h K

example {S T : Scheme.{u}} (g : T ⟶ S) [Flat g]
    (K : DerivedCategory.Plus (projectiveSpaceOver 1 S).Modules)
    (hK : RingedSpace.IsPerfect (X := (projectiveSpaceOver 1 S).toRingedSpace)
      (DerivedCategory.Plus.ι.obj K)) :
    IsIso ((projectiveLineFlatBaseChangePlus g).app K) :=
  isIso_projectiveLineFlatBaseChangePlus g K hK

example (R : CommRingCat.{u})
    (K : (perfectPlus (projectiveSpaceOver 1 (Spec R))).FullSubcategory) :
    (lineSelfPerfectBaseChangePlusIso R).hom.app K = (lineSelfBaseChangePlus R).app K.obj :=
  lineSelfPerfectBaseChangePlusIso_hom_app R K

example (K : (perfectPlus (projectiveSpaceOver 1 (Spec (.of (ZMod 1))))).FullSubcategory) :
    IsIso ((lineSelfBaseChangePlus (.of (ZMod 1))).app K.obj) :=
  isIso_lineSelfBaseChangePlus (.of (ZMod 1)) K.obj K.property

#print axioms AlgebraicGeometry.Scheme.Modules.openSquareBaseChangePlusIso_unit
#print axioms AlgebraicGeometry.Scheme.Modules.derivedPushforwardOpenBaseChangePlus
#print axioms isIso_flatSquareBaseChangePlus_of_quasicoherent
#print axioms isIso_projectiveLineFlatBaseChangePlus
#print axioms projectiveLinePerfectFlatBaseChangePlusIso_hom_app
#print axioms lineSelfPerfectBaseChangePlusIso_hom_app
#print axioms lineSelfBaseChangePlus_unit
