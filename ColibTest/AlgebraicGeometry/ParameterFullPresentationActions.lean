module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullPresentationActions
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
open GlobalSectionChangeIndex GlobalSupportedSection NaturalTrack ParameterTensorNormalizedTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
example : Equivariant (ambientTrack Q) (ambientTrack P)
    (ParameterFullCurrentNull.fullMap f) := fullMap_equivariant f
example (r : unitInterval) :
    Equivariant (supportedTrack f) (ambientTrack P)
      (diagramHomotopyAt
        (η := Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor ≫
          ParameterFullCurrentNull.fullMap f)
        (θ := diagramZeroMap (ParameterModels.supported f ⋙ prespectrumFunctor)
          (ParameterModels.ambient P ⋙ prespectrumFunctor))
        (ParameterFullCurrentNull.fullNull f).homotopy
        (ParameterFullCurrentNull.fullNull f).naturality r) := fullNull_equivariant f r
end AlgebraicGeometry.Scheme.Modules.ParameterTensorPresentation
