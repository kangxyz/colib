/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.StrictSquareCone
public import Mathlib.CategoryTheory.Whiskering

/-!
# The Bass endofunctor on strict diagrams

A functor `Q : C ⥤ Arrow (Arrow C)` specifies a strictly natural square of evaluation objects.
Applying a strict spectrum diagram to these squares, then the actual double-cylinder comparison,
cone, and parameter looping, is an endofunctor on the same diagram category. Its action includes
strict natural transformations, so all iterated images of a supplied seed arrow are defined.

The original geometric pullback diagram and seed transition must still be rectified and compared
to this strict interface. This owner supplies neither that rectification nor a new seed arrow.
-/
/-! Implementation provenance: `Quillen/KTheory/Bass/StrictDiagram.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology
universe u v w
namespace KTheory.Bass

variable {C : Type u} [Category.{v} C]

/-- The genuine Bass endofunctor associated to a strictly natural evaluation square. -/
def strictDiagramFunctor (Q : C ⥤ Arrow (Arrow C)) :
    (C ⥤ LoopPrespectrum.{w}) ⥤ (C ⥤ LoopPrespectrum.{w}) :=
  Functor.mapArrowFunctor C LoopPrespectrum ⋙
    Functor.mapArrowFunctor (Arrow C) (Arrow LoopPrespectrum) ⋙
    (Functor.whiskeringLeft C (Arrow (Arrow C)) (Arrow (Arrow LoopPrespectrum))).obj Q ⋙
    (Functor.whiskeringRight C (Arrow (Arrow LoopPrespectrum)) LoopPrespectrum).obj
      LoopPrespectrum.strictSquareLoopedConeFunctor

/-- Every value is the original parameter-looped cone of the actual strict comparison. -/
theorem strictDiagramFunctor_obj (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) (X : C) :
    ((strictDiagramFunctor Q).obj F).obj X =
      LoopPrespectrum.parameterLooping
        (LoopPrespectrum.mappingCone
          (LoopPrespectrum.StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X)))) := rfl

/-- Identity transformations are preserved as literal maps, not only up to homotopy. -/
theorem strictDiagramFunctor_map_id (Q : C ⥤ Arrow (Arrow C))
    (F : C ⥤ LoopPrespectrum.{w}) :
    (strictDiagramFunctor Q).map (𝟙 F) = 𝟙 ((strictDiagramFunctor Q).obj F) :=
  (strictDiagramFunctor Q).map_id F

/-- Composition of strict natural transformations is preserved literally. -/
theorem strictDiagramFunctor_map_comp (Q : C ⥤ Arrow (Arrow C))
    {F G H : C ⥤ LoopPrespectrum.{w}} (a : F ⟶ G) (b : G ⟶ H) :
    (strictDiagramFunctor Q).map (a ≫ b) =
      (strictDiagramFunctor Q).map a ≫ (strictDiagramFunctor Q).map b :=
  (strictDiagramFunctor Q).map_comp a b

/-- Iteration stays within the same strict diagram category. -/
def strictDiagramIterate (Q : C ⥤ Arrow (Arrow C)) :
    ℕ → (C ⥤ LoopPrespectrum.{w}) ⥤ (C ⥤ LoopPrespectrum.{w})
  | 0 => 𝟭 _
  | n + 1 => strictDiagramFunctor Q ⋙ strictDiagramIterate Q n

/-- The tower arrow is the actual iterated image of the supplied original seed arrow. -/
def strictDiagramTransition (Q : C ⥤ Arrow (Arrow C))
    {F : C ⥤ LoopPrespectrum.{w}} (η : F ⟶ (strictDiagramFunctor Q).obj F) (n : ℕ) :
    (strictDiagramIterate Q n).obj F ⟶ (strictDiagramIterate Q (n + 1)).obj F :=
  (strictDiagramIterate Q n).map η

/-- At stage zero the original supplied seed is retained literally. -/
theorem strictDiagramTransition_zero (Q : C ⥤ Arrow (Arrow C))
    {F : C ⥤ LoopPrespectrum.{w}} (η : F ⟶ (strictDiagramFunctor Q).obj F) :
    strictDiagramTransition Q η 0 = η := rfl

end KTheory.Bass

attribute [colib_tag "COL-0338",
  colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagram.lean" "adaptation"
    "Actual strict-square cylinder, cone-loop maps and supplied-seed finite iteration"]
  KTheory.Bass.strictDiagramFunctor
  KTheory.Bass.strictDiagramIterate
  KTheory.Bass.strictDiagramTransition
