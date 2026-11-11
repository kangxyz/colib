module
import Colib.AlgebraicGeometry.KTheory.Bass.GeometricChiPermutation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
universe u w
namespace KTheory.Bass.GeometricChiPermutation
open GeometricConeInterchange

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    (GeometricSeedCospan.chiGeom F).app X =
      LoopFactor.coneStrength ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) ≫
        parameterLoopingMap (permutation F X).hom :=
  comparison F X

end KTheory.Bass.GeometricChiPermutation
