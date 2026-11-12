module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedCoarseNull
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
universe u
noncomputable section
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]
example :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f)
    (boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f) :=
  boundedAboveFlatCoefficientSupportedOpenDiagramNull f
example :
    mappingConeDiagram (boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f) ⟶
    boundedAboveFlatCoefficientOpenPrespectrumFunctor f :=
  boundedAboveFlatCoefficientSupportedOpenConeComparison f
example (a : Under R) : boundedAboveFlatCoefficientSupportAcyclicEvaluation f a ⋙
    acyclicInclusion (boundedAboveFlatPerfectOpenNested (schemeMap f a)) =
      (boundedAboveFlatCoefficientSectionSupported (schemeMap f a)).ι ⋙
        boundedAboveFlatCoefficientOriginalEvaluation (Opposite.op Q, a) :=
  boundedAboveFlatCoefficientSupportAcyclicEvaluation_inclusion f a
end
