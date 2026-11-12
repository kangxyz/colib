module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenBassStages
noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
open AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example (i : ℕ) : boundedAboveFlatCoefficientOpenBassDiagram f i ⟶
    boundedAboveFlatCoefficientOpenBassDiagram f (i + 1) :=
  boundedAboveFlatCoefficientOpenBassTransition f i

example (i : ℕ) : boundedAboveFlatCoefficientOpenBassDiagram f i ⟶
    boundedAboveFlatCoefficientOpenBassTelescopeFunctor f :=
  boundedAboveFlatCoefficientOpenBassTelescopeInclusion f i

example (i : ℕ) : boundedAboveFlatCoefficientFullOpenBassDiagram f i ⟶
    boundedAboveFlatCoefficientFullOpenBassDiagram f (i + 1) :=
  boundedAboveFlatCoefficientFullOpenBassTransition f i

example (i : ℕ) : boundedAboveFlatCoefficientFullOpenBassDiagram f i ⟶
    boundedAboveFlatCoefficientFullOpenBassTelescopeFunctor f :=
  boundedAboveFlatCoefficientFullOpenBassTelescopeInclusion f i

end
