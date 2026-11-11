module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentNull
open CategoryTheory Topology Opposite AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open KTheory.Bass.NaturalTrack KTheory.Bass.SchemeNaturalSeed
open AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection
open AlgebraicGeometry.Scheme.Modules.ParameterLaurentTrack
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]
example : DiagramNullHomotopy
    (Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor) (fullMap f) :=
  fullNull f
example : Equivariant (ambientTrack Q) (ambientTrack P) (fullMap f) :=
  fullMap_equivariant f
example (r : unitInterval) :
    Equivariant (supportedTrack f) (ambientTrack P)
      (diagramHomotopyAt
        (η := Functor.whiskerRight (ParameterModels.forget f) prespectrumFunctor ≫ fullMap f)
        (θ := diagramZeroMap (ParameterModels.supported f ⋙ prespectrumFunctor)
          (ParameterModels.ambient P ⋙ prespectrumFunctor))
        (fullNull f).homotopy (fullNull f).naturality r) := timeSlice_equivariant f r
example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : ((currentTelescope (supportedTrack f)).obj X).space n) :
    ((telescopeMap (ambientTrack P)).app X).map n
      (((currentNull f).homotopy X).level n (r, x)) =
      ((normalizedNull f).homotopy X).level n
        (r, ((telescopeMap (supportedTrack f)).app X).map n x) := current_null_square f X n r x
end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
