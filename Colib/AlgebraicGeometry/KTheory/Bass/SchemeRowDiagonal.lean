/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricIndexSquare
public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentCoefficient
public import Colib.KTheory.Bass.DiagramRowBoundaryData
public import Colib.KTheory.Bass.DiagramRowCellCone

/-! # Original SchemeRowSeed declarations required by returned tensor strictification

Only the selected declarations listed in the source correspondence are migrated here.
The actual row carrier, inclusion, diagonal and iteration remain the original constructions.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.SchemeRowSeed
open GeometricSquareInterchange
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)

/-- The geometric square's original diagonal is the specified Laurent coefficient. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeRowSeed.lean:38"
  "adaptation" "Original actual row data and tensor-started recursion"]
theorem diagonal_eq (X : Scheme.{u}ᵒᵖ) :
    DiagramRowSeed.diagonal squareFunctor F X = F.map (coefficient.app X) :=
  congrArg (fun a => a.app X) (geometricSquare_diagonal F)

/-- Only endpoint witnesses change when the original cell is used on the geometric square. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/SchemeRowSeed.lean:43"
  "adaptation" "Original actual row data and tensor-started recursion"]
def diagonalCell (X : Scheme.{u}ᵒᵖ)
    (K : Homotopy ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X)
      ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X)) :
    Homotopy
      (DiagramRowSeed.diagonal squareFunctor F X ≫
        DiagramRowSeed.cornerComparison squareFunctor F q hp hs X)
      (DiagramRowSeed.diagonal squareFunctor F X ≫
        DiagramRowSeed.cornerComparison squareFunctor F q hp hs X) :=
  K.cast (by rw [diagonal_eq]; rfl) (by rw [diagonal_eq]; rfl)

end KTheory.Bass.SchemeRowSeed
