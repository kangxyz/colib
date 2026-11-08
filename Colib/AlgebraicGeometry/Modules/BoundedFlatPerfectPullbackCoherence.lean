/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullback
public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreePullbackCoherence
public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreeFlat

/-!
# Identity, composition and literal inclusion for flat perfect pullback

All comparisons are on original complexes and chain maps before applying K-theory.

Identity and composition adapt
`Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/PullbackIsomorphisms.lean`
(lines 35-48) at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.Perfect.BoundedLocallyFreeComplexes

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The native identity comparison lifted through the full chain inclusion. -/
def boundedAboveFlatPerfectPullbackIdIso (X : Scheme.{u}) :
    boundedAboveFlatPerfectPullback (𝟙 X) ≅
      𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
      (NatIso.mapHomologicalComplex (pullbackId X) (ComplexShape.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso X.Modules (ComplexShape.up ℤ)))

/-- The native composition comparison lifted through the full chain inclusion. -/
def boundedAboveFlatPerfectPullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedAboveFlatPerfectPullback (f ≫ g) ≅
      boundedAboveFlatPerfectPullback g ⋙ boundedAboveFlatPerfectPullback f :=
  Functor.fullyFaithfulCancelRight (boundedAboveFlatPerfectComplex X.toRingedSpace).ι
    (Functor.isoWhiskerLeft (boundedAboveFlatPerfectComplex Z.toRingedSpace).ι
      (Functor.mapHomologicalComplexCompIso (pullbackComp f g) (ComplexShape.up ℤ)).symm)

/-- The literal bounded-vector-bundle inclusion commutes with actual chain pullback. -/
def boundedFiniteLocallyFreeFlatInclusionPullbackIso (f : X ⟶ Y) :
    boundedFiniteLocallyFreeFlatInclusion Y ⋙ boundedAboveFlatPerfectPullback f ≅
      boundedFiniteLocallyFreePullback f ⋙ boundedFiniteLocallyFreeFlatInclusion X :=
  Iso.refl _

end AlgebraicGeometry.Scheme.Modules
