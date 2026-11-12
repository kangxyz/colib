module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOpenRestrictionSeed
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules KTheory.Bass
open Topology.LoopPrespectrum CommRingCat.PolynomialLaurent
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
example : boundedAboveFlatCoefficientOpenBassSeed f ≫
    (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
      (boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f) =
    boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f ≫
      boundedAboveFlatCoefficientFullOpenBassSeed f :=
  boundedAboveFlatCoefficientOpenBassSeed_restriction f
example (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a).space n) :
    ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app
      ((laurentUnderFunctor R).obj a)).map n
        ((boundedAboveFlatCoefficientOpenLaurentHomotopy f a).level n (t, x)) =
      (boundedAboveFlatCoefficientFullOpenLaurentHomotopy f a).level n
        (t, ((boundedAboveFlatCoefficientOpenRestrictionPrespectrumTransformation f).app a).map
          n x) :=
  boundedAboveFlatCoefficientOpenRestriction_laurent_apply f a n t x
