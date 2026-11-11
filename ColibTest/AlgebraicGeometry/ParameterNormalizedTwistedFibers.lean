module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullTwistedFiberComparison
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryTwistedFiberComparison
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
example (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ParameterFullCurrentNull.normalizedLift f X) ↔
      IsStableEquivalence (ParameterFullCurrentNull.twistedLift f X) :=
  ParameterFullCurrentNull.normalized_twisted_lift_stable_iff f X
example (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ParameterFullCurrentNull.currentLift f X) ↔
      IsStableEquivalence (ParameterFullCurrentNull.twistedLift f X) :=
  ParameterFullCurrentNull.current_twisted_lift_stable_iff f X
example (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ParameterAuxiliaryCurrentFiber.normalizedLift f T X) ↔
      IsStableEquivalence (ParameterAuxiliaryCurrentFiber.twistedLift f T X) :=
  ParameterAuxiliaryCurrentFiber.normalized_twisted_lift_stable_iff f T X
end AlgebraicGeometry.Scheme.Modules
