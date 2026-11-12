module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassSeed
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example : LaurentSeed.ModelAction (boundedAboveFlatCoefficientOpenModelFunctor f) :=
  boundedAboveFlatCoefficientOpenLaurentAction f

example (a : Under R) : boundedAboveFlatCoefficientOpenBassSeedMap f a =
    (boundedAboveFlatCoefficientOpenLaurentAction f).track.seedMap a := rfl

example : boundedAboveFlatCoefficientOpenPrespectrumFunctor f ⟶
    (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedAboveFlatCoefficientOpenPrespectrumFunctor f) :=
  boundedAboveFlatCoefficientOpenBassSeed f

example : LaurentSeed.ModelAction (boundedAboveFlatCoefficientFullOpenModelFunctor f) :=
  boundedAboveFlatCoefficientFullOpenLaurentAction f

example (a : Under R) : boundedAboveFlatCoefficientFullOpenBassSeedMap f a =
    (boundedAboveFlatCoefficientFullOpenLaurentAction f).track.seedMap a := rfl

example : boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f ⟶
    (strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedAboveFlatCoefficientFullOpenPrespectrumFunctor f) :=
  boundedAboveFlatCoefficientFullOpenBassSeed f

end
