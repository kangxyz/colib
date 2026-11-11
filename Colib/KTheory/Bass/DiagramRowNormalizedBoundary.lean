/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.DiagramRowBoundaryData
public import Colib.Topology.Prespectrum.RowNormalizedOperation

/-! # Original DiagramRowNormalizedBoundary declarations required by returned tensor strictification

Only the selected declarations listed in the source correspondence are migrated here.
The actual row carrier, inclusion, diagonal and iteration remain the original constructions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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


variable (X : C)
  (K : Homotopy (diagonal Q F X ≫ cornerComparison Q F q hp hs X)
    (diagonal Q F X ≫ cornerComparison Q F q hp hs X))

/-- Normalize the independent cell before applying the original refined boundary inclusion. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/DiagramRowNormalizedBoundary.lean:44"
  "adaptation" "Original actual row data and tensor-started recursion"]
def normalizedBoundary :
    F.obj (Q.obj X).left.left ⟶ parameterLooping (carrier Q F q hp hn X) :=
  RowRefinement.normalizedOperation (q (Q.obj X).right.right)
    (hp (Q.obj X).right.right) (diagonal Q F X ≫ cornerComparison Q F q hp hs X) K ≫
      parameterLoopingMap (inclusion Q F q hp hn X)

end KTheory.Bass.DiagramRowSeed

namespace KTheory.Bass.DiagramRowSeed

attribute [colib_tag "COL-0549"] normalizedBoundary

end KTheory.Bass.DiagramRowSeed
