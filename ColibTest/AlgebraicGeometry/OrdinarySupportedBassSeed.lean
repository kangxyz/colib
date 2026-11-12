module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinarySupportedBassSeed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Functor.IdentityAutomorphism CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
open AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedPrespectrumFunctor f).obj a).space n) :
    ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app
      ((laurentUnderFunctor R).obj a)).map n
        (((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy a).level n (t, x)) =
      ((boundedAboveFlatCoefficientAmbientLaurentAction Q).track.homotopy a).level n
        (t, ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a).map n x)
    :=
  boundedAboveFlatCoefficientSupportedForget_laurent_apply f a n t x

example :
    boundedAboveFlatCoefficientSupportedBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f) =
      boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f ≫
        boundedAboveFlatCoefficientAmbientBassSeed Q :=
  boundedAboveFlatCoefficientSupportedBassSeed_forget f

example
    (a : Under R) (r : (Γ(Spec a.right, ⊤))ˣ) :
    IdentityActionInterchange
      (V := (boundedAboveFlatCoefficientSupportedModelFunctor f).obj a)
      (T := (boundedAboveFlatCoefficientOpenModelFunctor f).obj a)
      ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a)
      (boundedAboveFlatCoefficientSupportedUnitIso f a r)
      (boundedAboveFlatCoefficientSectionUnitIso (op Q, a)
        (boundedAboveFlatCoefficientUnit (op Q, a) r)) :=
  boundedAboveFlatCoefficientSupportedOpenNull_unitInterchange f a r

example (a : Under R) :
    TrackInterchange
      ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a)
      ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy
        ((laurentUnderFunctor R).obj a))
      ((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy a)
      ((boundedAboveFlatCoefficientOpenLaurentAction f).track.homotopy a) :=
  boundedAboveFlatCoefficientSupportedOpenNull_laurentInterchange f a

example (s : unitInterval) :
    boundedAboveFlatCoefficientSupportedBassSeed f ≫
      (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatCoefficientSupportedOpenNullTimeSlice f s) =
      boundedAboveFlatCoefficientSupportedOpenNullTimeSlice f s ≫
        boundedAboveFlatCoefficientOpenBassSeed f :=
  boundedAboveFlatCoefficientSupportedOpenNullTimeSlice_seed f s

end
