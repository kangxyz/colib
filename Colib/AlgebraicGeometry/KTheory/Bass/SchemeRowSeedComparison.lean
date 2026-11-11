/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeRowDiagonal
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeNaturalSeed
public import Colib.KTheory.Bass.DiagramRowSeedComparison

/-! # The original whole scheme current-transition comparison

The actual original coefficient track, finite-stage seed and literal row target are retained.
No stable class substitutes for the whole map or normalized boundary homotopy.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.SchemeRowSeed
open GeometricSeedCospan NaturalTrack GeometricSquareInterchange
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)

/-- The genuine refined seed is formed from the independent cell and original whole cone null. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeRowSeed.lean:54"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
def seed (X : Scheme.{u}ᵒᵖ)
    (K : Homotopy ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X)
      ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X)) :
    F.obj X ⟶ parameterLooping (DiagramRowSeed.carrier squareFunctor F q hp hn X) :=
  DiagramRowSeed.seed squareFunctor F q hp hn hs X (diagonalCell F q hp hn hs X K)

/-- An independently proved whole-cell equality identifies the original map, not only classes. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeRowSeed.lean:61"
  "adaptation" "Original whole scheme seed and literal current-transition comparison"]
theorem seed_eq (A : Track laurent.op coefficient F) (X : Scheme.{u}ᵒᵖ)
    (K : Homotopy ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X)
      ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X))
    (hK : K = (A.homotopy X).postcomp
      ((DiagramRowRefinement.comparison F q hp hn hs).app (laurent.op.obj X))) :
    seed F q hp hn hs X K = (SchemeNaturalSeed.seed A).app X ≫
      parameterLoopingMap (DiagramRowSeed.comparison squareFunctor F q hp hn hs X) := by
  apply DiagramRowSeed.seed_eq
  subst K
  apply Homotopy.ext
  rfl

end KTheory.Bass.SchemeRowSeed
