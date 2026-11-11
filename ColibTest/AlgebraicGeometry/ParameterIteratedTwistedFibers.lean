module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterIteratedTwistedFiber
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryIteratedFiberComparison
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
example (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ParameterFullCurrentNull.iteratedLift f X) ↔
      IsStableEquivalence (ParameterFullCurrentNull.twistedLift f X) :=
  ParameterFullCurrentNull.iterated_twisted_lift_stable_iff f X
example (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ParameterAuxiliaryCurrentFiber.iteratedLift f T X) ↔
      IsStableEquivalence (ParameterAuxiliaryCurrentFiber.twistedLift f T X) :=
  ParameterAuxiliaryCurrentFiber.iterated_twisted_lift_stable_iff f T X
example (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ParameterAuxiliaryCurrentFiber.currentLift f T X) ↔
      IsStableEquivalence (ParameterAuxiliaryCurrentFiber.iteratedLift f T X) :=
  ParameterAuxiliaryCurrentFiber.current_iterated_lift_stable_iff f T X
end AlgebraicGeometry.Scheme.Modules
