module
import Colib.AlgebraicGeometry.KTheory.Bass.GeometricChiScalar
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

open GeometricSquareInterchange SquareConeStrength
open PushoutStrength PushoutCofiberSquare

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (z : ((coneFunctor.obj F).obj (laurent.op.obj X)).space n) :
    ((coneFunctor.map (targetMap F)).app X).map n
      (((GeometricConeInterchange.eta
        (laurentProjection (.of (ULift.{u} ℤ))) F).hom.app X).map n z) =
      (permutation F X).hom.map n
        (Cell.target ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n z) :=
  target_scalar F X n z

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r : unitInterval) (z : ((coneFunctor.obj F).obj (polynomial.op.obj X)).space n) :
    ((coneFunctor.map (upperMap F r)).app X).map n (((GeometricConeInterchange.eta
        (polynomialProjection (.of (ULift.{u} ℤ))) F).hom.app X).map n z) =
      (permutation F X).hom.map n
        (Cell.upper ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r z) :=
  upper_scalar F X n r z

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r : unitInterval) (z : ((coneFunctor.obj F).obj (polynomial.op.obj X)).space n) :
    ((coneFunctor.map (lowerMap F r)).app X).map n (((GeometricConeInterchange.eta
        (polynomialProjection (.of (ULift.{u} ℤ))) F).hom.app X).map n z) =
      (permutation F X).hom.map n
        (Cell.lower ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r z) :=
  lower_scalar F X n r z

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ)
    (n : ℕ) (r s : unitInterval) (z : ((coneFunctor.obj F).obj (X)).space n) :
    ((coneFunctor.map (overlapMap F r s)).app X).map n z =
      (permutation F X).hom.map n
        (Cell.overlap ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)) n r s z) :=
  overlap_scalar F X n r s z

end KTheory.Bass.GeometricChiPermutation
