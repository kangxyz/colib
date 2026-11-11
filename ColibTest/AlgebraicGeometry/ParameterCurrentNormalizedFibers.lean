module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterFullCurrentFiberComparison
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryCurrentFiber
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
example (X : Scheme.{u}ᵒᵖ) : IsStableEquivalence (ParameterFullCurrentNull.currentLift f X) ↔
    IsStableEquivalence (ParameterFullCurrentNull.normalizedLift f X) :=
  ParameterFullCurrentNull.current_normalized_lift_stable_iff f X
example (X : Scheme.{u}ᵒᵖ) :
    ParameterFullCurrentNull.currentLift f X =
      homotopyFiberLift ((ParameterFullCurrentNull.currentOpen f).app X)
        ((ParameterFullCurrentNull.currentForget f).app X)
        ((ParameterFullCurrentNull.currentNull f).homotopy X) := rfl
example (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (ParameterAuxiliaryCurrentFiber.currentLift f T X) ↔
      IsStableEquivalence (ParameterAuxiliaryCurrentFiber.normalizedLift f T X) :=
  ParameterAuxiliaryCurrentFiber.current_normalized_lift_stable_iff f T X
example (X : Scheme.{u}ᵒᵖ) :
    ParameterAuxiliaryCurrentFiber.currentLift f T X =
      homotopyFiberLift
        ((GlobalSupportedSection.ParameterAuxiliarySupport.currentRestriction f T).app X)
        ((GlobalSupportedSection.ParameterAuxiliarySupport.currentEnlargement f T).app X)
        ((GlobalSupportedSection.ParameterAuxiliarySupport.currentNull f T).homotopy X) := rfl
end AlgebraicGeometry.Scheme.Modules
