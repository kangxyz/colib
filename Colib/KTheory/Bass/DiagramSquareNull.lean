/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.PointwisePushout
public import Colib.KTheory.Bass.DiagramConeInclusion
public import Colib.KTheory.Bass.StrictDiagramZeroMap
public import Colib.Topology.Prespectrum.StrictSquareNull

/-! # Original coefficient-natural null/unit/null seed word

Only the original whole-word construction and its same-time naturality are selected.
No comparison under Bass, stability or telescope statement is assumed here.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.SquareConeStrength
open PushoutStrength PushoutCofiberSquare
variable {C : Type u} [Category.{v} C]
variable (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w})))

/-- The original component squares of a strict square of natural transformations. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SquareConeStrength.lean:31"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
def squareDiagram (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))) :
    C ⥤ Arrow (Arrow LoopPrespectrum.{w}) :=
  (ArrowDiagrams.toDiagram.mapArrow ⋙ ArrowDiagrams.toDiagram).obj S

/-- The original comparison, with its constant whole overlap, is coefficient-natural. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SquareConeStrength.lean:36"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
def comparison (S : Arrow (Arrow (C ⥤ LoopPrespectrum.{w}))) :
    pushout S.left.hom S.hom.left ⟶ S.right.right where
  app X := StrictSquare.comparison ((squareDiagram S).obj X)
  naturality _X _Y k := StrictSquare.comparison_naturality ((squareDiagram S).map k)

/-- The actual source-null track is the original strict-square cylinder contraction. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SquareConeStrength.lean:157"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
def sourceNull (X : C) :
    Homotopy (((S.left.hom ≫ S.hom.right) ≫ coneInclusion (comparison S)).app X)
      ((diagramZeroMap S.left.left (mappingConeDiagram (comparison S))).app X) :=
  StrictSquare.sourceNullHomotopy ((squareDiagram S).obj X)

/-- The full original source null is coefficient-natural at the identical time. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SquareConeStrength.lean:163"
  "adaptation" "Original actual null/unit/null word and coefficient-natural maps"]
theorem sourceNull_naturality {X Y : C} (k : X ⟶ Y) n r x :
    ((mappingConeDiagram (comparison S)).map k).map n ((sourceNull S X).level n (r, x)) =
      (sourceNull S Y).level n (r, (S.left.left.map k).map n x) := by
  exact StrictSquare.sourceNullHomotopy_naturality_apply ((squareDiagram S).map k) n r x

end KTheory.Bass.SquareConeStrength
