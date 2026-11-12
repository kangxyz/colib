module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportConeStable
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section
example {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedOpenConeComparison f).app a) :=
  boundedAboveFlatCoefficientSupportedOpenConeComparison_isStableEquivalence f a
end
