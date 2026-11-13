module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterCoefficientSeed
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass
universe u
noncomputable section
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]
example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (squareComparison f a).left.left = (rowComparison f).app a :=
  squareComparison_source f a
example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (bassComparison f).app a = strictSquareLoopedConeFunctor.map (squareComparison f a) :=
  bassComparison_app f a
example : Functor.whiskerLeft specUnder
    (SchemeNaturalSeed.seed (ParameterLaurentTrack.supportedTrack f.left)) ≫ bassComparison f =
      rowComparison f ≫ (GlobalSectionChangeIndex.supportedLaurentAction f).track.seed :=
  seed_square f
