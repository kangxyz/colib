module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryPresentationActions
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open KTheory.Bass.NaturalTrack KTheory.Bass.SchemeNaturalSeed
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((currentTelescope (fiberAction f T)).obj X).space n) :
    ((telescopeMap (openAction f T)).app X).map n
      (((currentNull f T).homotopy X).level n (r, x)) =
      ((normalizedNull f T).homotopy X).level n
        (r, ((telescopeMap (fiberAction f T)).app X).map n x) := current_null_square f T X n r x
end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
open GlobalSectionChangeIndex GlobalSupportedSection ParameterAuxiliarySupport
open ParameterTensorNormalizedTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
example : Equivariant (supportedTrack (unionOpen f T).ι) (supportedTrack T.ι) (firstMap f T) :=
  enlargement_equivariant f T
omit [IsOpenImmersion f] in
example : Equivariant (supportedTrack T.ι) (supportedTrack (inverseOpen f T).ι) (secondMap f T) :=
  restriction_equivariant f T
example (r : unitInterval) :
    Equivariant (supportedTrack (unionOpen f T).ι) (supportedTrack (inverseOpen f T).ι)
      (diagramHomotopyAt (η := firstMap f T ≫ secondMap f T)
        (θ := diagramZeroMap (fiber f T ⋙ prespectrumFunctor)
          (openModel f T ⋙ prespectrumFunctor))
        (fullNull f T).homotopy (fullNull f T).naturality r) := auxiliaryNull_equivariant f T r
end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
