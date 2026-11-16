/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectFlatPullback

/-! # Composing the native flat pullback of perfect complexes -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false in
/-- The composition law is the degreewise comparison on actual sheaf pullbacks. -/
def perfectFlatPullbackComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Flat f] [Flat g] :
    perfectFlatPullback g ⋙ perfectFlatPullback f ≅ perfectFlatPullback (f ≫ g) :=
  Functor.fullyFaithfulCancelRight
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    (Functor.isoWhiskerLeft
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := Z.toRingedSpace)))
      (Functor.mapHomologicalComplexCompIso (pullbackComp f g) (ComplexShape.up ℤ)))

set_option backward.isDefEq.respectTransparency false in
/-- Equal scheme morphisms give the same geometric pullback comparison on native complexes. -/
def perfectFlatPullbackCongr {X Y : Scheme.{u}} {f g : X ⟶ Y} [Flat f] [Flat g] (h : f = g) :
    perfectFlatPullback f ≅ perfectFlatPullback g :=
  Functor.fullyFaithfulCancelRight
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    (Functor.isoWhiskerLeft
      (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)))
      (NatIso.mapHomologicalComplex (pullbackCongr h) (ComplexShape.up ℤ)))

end AlgebraicGeometry.Scheme.Modules
