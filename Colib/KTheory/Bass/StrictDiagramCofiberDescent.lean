/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StrictSquareCofiberDescent
public import Colib.Topology.Prespectrum.ConeDiagramDescent
public import Colib.KTheory.Bass.StrictDiagramHomotopy

/-!
# Coefficient-natural Bass cofiber comparison and original null descent

The actual square comparison assembles into a natural transformation on coefficient diagrams.
Its factorization theorem uses the unchanged pointwise mapping-cone descents and the existing
Bass action on the specified original whole null track, including its literal endpoint casts.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
    {F G K : C ⥤ LoopPrespectrum.{w}} (a : F ⟶ G)

/-- The original comparison commutes with every original coefficient cube. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramCofiberDescent.lean:30"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
def strictDiagramCofiberComparison :
    mappingConeDiagram ((strictDiagramFunctor Q).map a) ⟶
      (strictDiagramFunctor Q).obj (mappingConeDiagram a) where
  app X := StrictSquare.loopedConeCofiberComparison (diagramSquareMap a (Q.obj X))
  naturality X Y f := by
    let k : Arrow.mk (diagramSquareMap a (Q.obj X)) ⟶
        Arrow.mk (diagramSquareMap a (Q.obj Y)) :=
      Arrow.homMk (F.mapArrow.mapArrow.map (Q.map f)) (G.mapArrow.mapArrow.map (Q.map f))
        (by
          apply Arrow.hom_ext <;> apply Arrow.hom_ext <;> exact a.naturality _)
    exact StrictSquare.loopedConeCofiberComparison_naturality _ k

variable (b : G ⟶ K)
    (N : ∀ X, Homotopy (a.app X ≫ b.app X) (zeroHom (F.obj X) (K.obj X)))
    (hN : ∀ {X Y} (f : X ⟶ Y) n r x,
      (K.map f).map n ((N X).level n (r, x)) =
        (N Y).level n (r, (F.map f).map n x))

/-- The actual square of the original natural cone descents retains all four prescribed tracks. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramCofiberDescent.lean:49"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem diagramSquareMap_coneDescTransformation (S : Arrow (Arrow C)) :
    diagramSquareMap (mappingConeDescTransformation a b N hN) S =
      StrictSquare.coneSquareDesc (diagramSquareMap a S) (diagramSquareMap b S)
        (diagramSquareMapHomotopy (η := a ≫ b) (θ := diagramZeroMap F K) N hN S)
        rfl rfl rfl rfl := by
  apply Arrow.hom_ext <;> apply Arrow.hom_ext <;> rfl

/-- The square construction keeps the entire existing diagram null action at the same times. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramCofiberDescent.lean:57"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem strictDiagramNullHomotopy_square (X : C) :
    strictDiagramNullHomotopy a b N hN Q X =
      StrictSquare.loopedConeNullHomotopy (diagramSquareMap a (Q.obj X))
        (diagramSquareMap b (Q.obj X))
        (diagramSquareMapHomotopy (η := a ≫ b) (θ := diagramZeroMap F K) N hN (Q.obj X))
        rfl rfl rfl rfl := by
  apply Homotopy.ext
  rfl

/-- The actual comparison factors the Bass image of descent through the original Bass null. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/StrictDiagramCofiberDescent.lean:67"
  "adaptation" "Original whole-null cofiber comparison and actual finite Model excision"]
theorem strictDiagramCofiberComparison_desc (X : C) :
    (strictDiagramCofiberComparison Q a).app X ≫
        (((strictDiagramFunctor Q).map (mappingConeDescTransformation a b N hN)).app X) =
      mappingConeDesc (((strictDiagramFunctor Q).map a).app X)
        (((strictDiagramFunctor Q).map b).app X) (strictDiagramNullHomotopy a b N hN Q X) := by
  change StrictSquare.loopedConeCofiberComparison (diagramSquareMap a (Q.obj X)) ≫
    strictSquareLoopedConeFunctor.map
      (diagramSquareMap (mappingConeDescTransformation a b N hN) (Q.obj X)) = _
  rw [diagramSquareMap_coneDescTransformation]
  rw [strictDiagramNullHomotopy_square]
  exact StrictSquare.loopedConeCofiberComparison_desc
    (diagramSquareMap a (Q.obj X)) (diagramSquareMap b (Q.obj X))
    (diagramSquareMapHomotopy (η := a ≫ b) (θ := diagramZeroMap F K) N hN (Q.obj X))
    rfl rfl rfl rfl

end KTheory.Bass


namespace KTheory.Bass

attribute [colib_tag "COL-0581"] strictDiagramCofiberComparison_desc

end KTheory.Bass
