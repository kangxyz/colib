/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BoundedBelowPullback
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.CoefficientFunctors

/-! # The actual unit for the untwisted coefficient functor

On the bounded below source, the pullback/direct-image adjunction unit followed by the
pushforward of the Godement augmentation is a natural chain map into the geometric coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [Flat f] [IsProper f] [LocallyOfFinitePresentation f]

local notation "c" => ComplexShape.up ℤ

/-- The positive chain map is the termwise adjunction unit followed by actual resolution. -/
def resolvedPullbackUnitChain (K : BoundedBelowPerfect.Obj Y) :
    K.obj ⟶ ((perfectPushforward f).obj ((total X).obj
      ((BoundedBelowPerfect.flatPullback f).obj K))).obj :=
  let adj := (pullbackPushforwardAdjunction f).mapHomologicalComplexAdjunction c
  let unit₀ := adj.unit.app K.obj
  let unit₁ := ((BoundedBelowPerfect.godementUnit X).app
    ((BoundedBelowPerfect.flatPullback f).obj K)).hom
  unit₀ ≫ ((pushforward f).mapHomologicalComplex c).map unit₁

/-- The same chain map in the native perfect category. -/
def resolvedPullbackUnit :
    BoundedBelowPerfect.inclusion Y ⟶
      (BoundedBelowPerfect.flatPullback f ⋙ total X) ⋙ perfectPushforward f where
  app K := ObjectProperty.homMk (resolvedPullbackUnitChain f K)
  naturality {K L} g := by
    apply ObjectProperty.hom_ext
    let A := (pullback f).mapHomologicalComplex c
    let B := (pushforward f).mapHomologicalComplex c
    let η := ((pullbackPushforwardAdjunction f).mapHomologicalComplexAdjunction c).unit
    let s (Q : BoundedBelowPerfect.Obj Y) :=
      ((BoundedBelowPerfect.godementUnit X).app ((BoundedBelowPerfect.flatPullback f).obj Q)).hom
    let t := ((BoundedBelowPerfect.godementTotal X).map
      ((BoundedBelowPerfect.flatPullback f).map g)).hom
    change g.hom ≫ (η.app L.obj ≫ B.map (s L)) =
      (η.app K.obj ≫ B.map (s K)) ≫ B.map t
    have hη : g.hom ≫ η.app L.obj = η.app K.obj ≫ B.map (A.map g.hom) :=
      η.naturality g.hom
    have hs : A.map g.hom ≫ s L = s K ≫ t :=
      congrArg (fun m => m.hom) ((BoundedBelowPerfect.godementUnit X).naturality
        ((BoundedBelowPerfect.flatPullback f).map g))
    rw [← Category.assoc g.hom, hη, Category.assoc, ← B.map_comp, hs, B.map_comp,
      ← Category.assoc]

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
