/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Scheme.PolynomialLaurentIndexSquareFactor
public import Colib.KTheory.Bass.StrictDiagram

/-! # Original GeometricIndexTransport declarations required by returned tensor strictification

Only the selected declarations listed in the source correspondence are migrated here.
The actual row carrier, inclusion, diagonal and iteration remain the original constructions.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
universe u w u₁ v₁
namespace KTheory.Bass.GeometricSquareInterchange
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})

/-- The original polynomial projection applied by the actual spectrum diagram. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/GeometricIndexTransport.lean:72"
  "adaptation" "Original actual row data and tensor-started recursion"]
def projectionMap : F ⟶ polynomial.op ⋙ F :=
  Functor.whiskerRight (NatTrans.op projection) F

/-- The original positive chart applied by the actual spectrum diagram. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/GeometricIndexTransport.lean:76"
  "adaptation" "Original actual row data and tensor-started recursion"]
def plusMap : polynomial.op ⋙ F ⟶ laurent.op ⋙ F :=
  Functor.whiskerRight (NatTrans.op plus) F

/-- The original inverse chart applied by the actual spectrum diagram. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/GeometricIndexTransport.lean:80"
  "adaptation" "Original actual row data and tensor-started recursion"]
def minusMap : polynomial.op ⋙ F ⟶ laurent.op ⋙ F :=
  Functor.whiskerRight (NatTrans.op minus) F

/-- The original charts have the same original spectrum-level composite. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/GeometricIndexTransport.lean:84"
  "adaptation" "Original actual row data and tensor-started recursion"]
theorem chartMap_projection :
    projectionMap F ≫ plusMap F = projectionMap F ≫ minusMap F := by
  apply NatTrans.ext
  funext X
  change F.map (projection.app X.unop).op ≫ F.map (plus.app X.unop).op =
    F.map (projection.app X.unop).op ≫ F.map (minus.app X.unop).op
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg F.map (Quiver.Hom.unop_inj (chart_projection X.unop))

/-- Collect the unchanged geometric maps into a square with its source literally F. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/GeometricIndexTransport.lean:94"
  "adaptation" "Original actual row data and tensor-started recursion"]
def geometricSquare : Arrow (Arrow (Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})) :=
  Arrow.mk (Arrow.homMk (f := Arrow.mk (projectionMap F))
    (g := Arrow.mk (minusMap F)) (projectionMap F) (plusMap F)
    (chartMap_projection F).symm)

/-- The original diagonal is exactly the original Laurent projection. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/GeometricIndexTransport.lean:120"
  "adaptation" "Original actual row data and tensor-started recursion"]
theorem geometricSquare_diagonal :
    (geometricSquare F).left.hom ≫ (geometricSquare F).hom.right =
      Functor.whiskerRight (NatTrans.op
        (baseProductProjection (laurentProjection (.of (ULift.{u} ℤ))))) F := by
  apply NatTrans.ext
  funext X
  change F.map (projection.app X.unop).op ≫ F.map (plus.app X.unop).op = _
  rw [← F.map_comp]
  apply congrArg F.map
  apply Quiver.Hom.unop_inj
  exact baseProductTransformation_projection
    (laurentProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ)))
    (laurentToPolynomial (.of (ULift.{u} ℤ))) (laurentToPolynomial_projection (.of (ULift.{u} ℤ)))
      X.unop

end KTheory.Bass.GeometricSquareInterchange
