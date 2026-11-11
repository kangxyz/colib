module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterIteratedFullNull
import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryIteratedNull
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
universe u
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)
example (X : Scheme.{u}ᵒᵖ) : ParameterFullCurrentNull.iteratedLift f X =
    homotopyFiberLift ((ParameterFullCurrentNull.iteratedOpen f).app X)
      ((ParameterFullCurrentNull.iteratedForget f).app X)
      ((ParameterFullCurrentNull.iteratedNull f).homotopy X) := rfl
open GlobalSupportedSection.ParameterAuxiliarySupport
example : iteratedNull f T =
    KTheory.Bass.SchemeNaturalSeed.iteratedInputNull (fiberAction f T) (ambientAction T)
      (openAction f T) (firstMap f T) (secondMap f T)
      (enlargement_equivariant f T) (restriction_equivariant f T)
      (fullNull f T) (timeSlice_equivariant f T) := rfl
end AlgebraicGeometry.Scheme.Modules
