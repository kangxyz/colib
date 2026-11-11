module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliarySupportNull
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
open ParameterLaurentTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
example : toBasic f T ≫ ParameterModels.forget f =
    ParameterModels.forget (unionOpen f T).ι := toBasic_forget f T
example : DiagramNullHomotopy
    (Functor.whiskerRight (enlargement f T) prespectrumFunctor)
    (Functor.whiskerRight (restriction f T) prespectrumFunctor) := fullNull f T
example (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    ((fullNull f T).homotopy X).level n (r, x) =
      (prespectrumTransformationHomotopy (zeroToFull f T X)
        (zeroToFull_weak f T X)).level n (unitInterval.symm r, x) := fullNull_level f T X n r x
example (X : Scheme.{u}ᵒᵖ) :
    TrackInterchange ((fullNull f T).homotopy X)
      ((fullNull f T).homotopy (laurent.op.obj X))
      ((supportedTrack (unionOpen f T).ι).homotopy X)
      ((supportedTrack (inverseOpen f T).ι).homotopy X) := fullNull_laurentInterchange f T X
end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
