/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.DiagramRowBoundaryData
public import Colib.Topology.Prespectrum.RowRefinementCone
public import Colib.Topology.Prespectrum.RefinedNullSeed

/-!
# Independent row seeds on the original four-corner diagram

The original last-corner inclusion acts on the computed row refinement. An
independent cell then gives a seed using the image of the complete original
source null. A whole-cell equality supplies the original seed comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.DiagramRowSeed
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ Arrow (Arrow C)) (F : C ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)


/-- Its actual comparison from the original cone. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/DiagramRowSeed.lean:40"
  "adaptation" "Original whole-null refinement and normalized boundary comparison"]
def comparison (X : C) : (ConeTrack.diagram Q F).obj X ⟶ carrier Q F q hp hn X :=
  RowRefinement.comparison _ _ _ (DiagramRowInterchange.cone_structure Q F q hp hn hs X)


/-- The last-corner inclusion square uses the original cone comparison. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/DiagramRowSeed.lean:57"
  "adaptation" "Original whole-null refinement and normalized boundary comparison"]
theorem comparison_inclusion (X : C) :
    cornerComparison Q F q hp hs X ≫ inclusion Q F q hp hn X =
      mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))) ≫
        comparison Q F q hp hn hs X :=
  (RowRefinement.comparison_naturality _ _ _ _
    (mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))
    (fun _ _ => rfl) (hs (Q.obj X).right.right)
    (DiagramRowInterchange.cone_structure Q F q hp hn hs X)).symm


/-- Form the independent seed with the full original source null, including its cone height. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/DiagramRowSeed.lean:70"
  "adaptation" "Original whole-null refinement and normalized boundary comparison"]
def seed (X : C)
    (K : Homotopy (diagonal Q F X ≫ cornerComparison Q F q hp hs X)
      (diagonal Q F X ≫ cornerComparison Q F q hp hs X)) :
    F.obj (Q.obj X).left.left ⟶ parameterLooping (carrier Q F q hp hn X) :=
  RefinedNullSeed.seed (diagonal Q F X)
    (mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))
    (cornerComparison Q F q hp hs X) (comparison Q F q hp hn hs X)
    (inclusion Q F q hp hn X) (comparison_inclusion Q F q hp hn hs X) K
    (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X)))

/-- The original seed and the independent row seed agree under the actual looped comparison. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/DiagramRowSeed.lean:81"
  "adaptation" "Original whole-null refinement and normalized boundary comparison"]
theorem seed_eq (X : C) (H : Homotopy (diagonal Q F X) (diagonal Q F X))
    (K : Homotopy (diagonal Q F X ≫ cornerComparison Q F q hp hs X)
      (diagonal Q F X ≫ cornerComparison Q F q hp hs X))
    (hK : K = H.postcomp (cornerComparison Q F q hp hs X)) :
    seed Q F q hp hn hs X K =
      ((H.postcomp (mappingConeInclusion
        (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))).nullLoopMap
          (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (Q.obj X)))) ≫
        parameterLoopingMap (comparison Q F q hp hn hs X) :=
  RefinedNullSeed.seed_eq _ _ _ _ _ _ _ _ H hK

end KTheory.Bass.DiagramRowSeed
