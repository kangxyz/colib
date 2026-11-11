module
import Colib.AlgebraicGeometry.KTheory.Bass.GeometricSquareInterchange
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

example : (squareInterchangeMap F).left.left =
    𝟙 ((strictDiagramFunctor squareFunctor).obj F) :=
  squareInterchange_base F

example : (squareInterchangeMap F).left.right =
    (eta (polynomialProjection (.of (ULift.{u} ℤ))) F).hom :=
  squareInterchange_polynomial F

example : (squareInterchangeMap F).right.right =
    (eta (laurentProjection (.of (ULift.{u} ℤ))) F).hom :=
  squareInterchange_laurent F

end KTheory.Bass.GeometricSquareInterchange
