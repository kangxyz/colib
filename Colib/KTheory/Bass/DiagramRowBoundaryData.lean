/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.DiagramRowInterchange
public import Colib.Topology.Prespectrum.RowRefinementCone

/-! # Original DiagramRowSeed declarations required by returned tensor strictification

Only the selected declarations listed in the source correspondence are migrated here.
The actual row carrier, inclusion, diagonal and iteration remain the original constructions.
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

/-- The original unlooped cone's actual computed row carrier. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/DiagramRowSeed.lean:36"
  "adaptation" "Original actual row data and tensor-started recursion"]
abbrev carrier (X : C) := RowRefinement.spectrum ((ConeTrack.diagram Q F).obj X)
  (DiagramRowInterchange.cone Q F q hp hn X) (DiagramRowInterchange.cone_point Q F q hp hn X)

/-- The last corner's genuine row comparison. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/DiagramRowSeed.lean:44"
  "adaptation" "Original actual row data and tensor-started recursion"]
def cornerComparison (X : C) :=
  RowRefinement.comparison (F.obj (Q.obj X).right.right)
    (q (Q.obj X).right.right) (hp (Q.obj X).right.right) (hs (Q.obj X).right.right)

/-- The original last-corner inclusion acts on the actual row, at every coordinate. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/DiagramRowSeed.lean:49"
  "adaptation" "Original actual row data and tensor-started recursion"]
def inclusion (X : C) :
    RowRefinement.spectrum (F.obj (Q.obj X).right.right)
      (q (Q.obj X).right.right) (hp (Q.obj X).right.right) ⟶ carrier Q F q hp hn X :=
  RowRefinement.map _ _ _ _
    (mappingConeInclusion (StrictSquare.comparison (F.mapArrow.mapArrow.obj (Q.obj X))))
    (fun _ _ => rfl)

/-- The actual original diagonal of the four-corner square. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/DiagramRowSeed.lean:67"
  "adaptation" "Original actual row data and tensor-started recursion"]
abbrev diagonal (X : C) := F.map (Q.obj X).left.hom ≫ F.map (Q.obj X).hom.right

end KTheory.Bass.DiagramRowSeed
