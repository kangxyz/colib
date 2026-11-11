module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberBassSeed

open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass
open CategoryTheory.Functor.IdentityAutomorphism CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
noncomputable section
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

example {a b : Under R} (g : a ⟶ b) :
    Preserves ((boundedAboveFlatCoefficientSupportedFiberModelFunctor f T).map
      ((laurentUnderFunctor R).map g)).hom.toFunctor
      (boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso f T a)
      (boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso f T b) :=
  boundedAboveFlatCoefficientSupportedFiberLaurentUnitIso_coefficient f T g

example (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    Preserves (boundedAboveFlatCoefficientSupportedFiberForget f T a)
      (boundedAboveFlatCoefficientSupportSectionUnitIso
        (boundedAboveFlatCoefficientFiberSupportOpen f T a).ι r)
      (boundedAboveFlatCoefficientSupportSectionUnitIso
        (boundedAboveFlatCoefficientSupportOpen Q T a).ι r) :=
  supportedFiberForget_unit_preserves f T a r

example (a : Under R) :
    Preserves (boundedAboveFlatCoefficientSupportedOpenRestriction f T
      ((laurentUnderFunctor R).obj a))
      (boundedAboveFlatCoefficientSupportedAmbientLaurentUnitIso Q T a)
      (boundedAboveFlatCoefficientSupportedFullOpenLaurentUnitIso f T a) :=
  boundedAboveFlatCoefficientSupportedOpenRestriction_laurentUnit_preserves f T a

example (a : Under R) :
    Homotopy
      ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).map
          ((laurentUnderCoefficient R).app a) ≫
        mappingConeInclusion (StrictSquare.comparison
          (boundedAboveFlatCoefficientSupportedOpenBassSquare f T a)))
      (zeroHom ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)
        (boundedAboveFlatCoefficientSupportedOpenBassCone f T a)) :=
  boundedAboveFlatCoefficientSupportedOpenBassNullHomotopy f T a

example (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app
      ((laurentUnderFunctor R).obj a)).map n
      (((boundedAboveFlatCoefficientSupportedFiberLaurentAction f T).track.homotopy a).level n
        (t, x)) =
    ((boundedAboveFlatCoefficientSupportedAmbientLaurentAction T).track.homotopy a).level n
      (t, ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app
        a).map n x) :=
  boundedAboveFlatCoefficientSupportedFiberForget_laurent_apply f T a n t x

example :
    boundedAboveFlatCoefficientSupportedFiberBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T) =
    boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T ≫
      boundedAboveFlatCoefficientSupportedAmbientBassSeed T :=
  boundedAboveFlatCoefficientSupportedFiberBassSeed_forget f T

example :
    boundedAboveFlatCoefficientSupportedAmbientBassSeed T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T) =
    boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T ≫
      boundedAboveFlatCoefficientSupportedOpenBassSeed f T :=
  boundedAboveFlatCoefficientSupportedAmbientBassSeed_open f T

example (s : unitInterval) :
    boundedAboveFlatCoefficientSupportedFiberBassSeed f T ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedFiberOpenNullTimeSlice f T s) =
    boundedAboveFlatCoefficientSupportedFiberOpenNullTimeSlice f T s ≫
      boundedAboveFlatCoefficientSupportedOpenBassSeed f T :=
  boundedAboveFlatCoefficientSupportedFiberOpenNullTimeSlice_seed f T s
