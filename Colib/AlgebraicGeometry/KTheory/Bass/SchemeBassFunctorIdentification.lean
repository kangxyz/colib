/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeIndexTransport
public import Colib.KTheory.Bass.ConeTrack

/-! # The literal object of the geometric cone functor -/
@[expose] public section
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u v w
namespace KTheory.Bass.SchemeIteratedSeedTransition

/-- The original Bass functor is the original cone diagram followed by parameter looping. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeBassFunctorIdentification.lean:20"
  "adaptation" "Original exact identification of the same scheme cone and seed data."]
theorem bassFunctor_obj_eq {C : Type u} [Category.{w} C]
    (Q : C ⥤ Arrow (Arrow C)) (G : C ⥤ LoopPrespectrum.{v}) :
    (strictDiagramFunctor Q).obj G = ConeTrack.diagram Q G ⋙ parameterLoopingFunctor := rfl

end KTheory.Bass.SchemeIteratedSeedTransition
