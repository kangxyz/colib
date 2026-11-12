module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTower
noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
open AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example (i : ℕ) :
    boundedAboveFlatCoefficientSupportedBassForget f i ≫
        boundedAboveFlatCoefficientAmbientBassTransition Q i =
      boundedAboveFlatCoefficientSupportedBassTransition f i ≫
        boundedAboveFlatCoefficientSupportedBassForget f (i + 1) :=
  boundedAboveFlatCoefficientSupportedBassForget_transition f i

example
    (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedBassDiagram f i).obj a).space m) :
    ((boundedAboveFlatCoefficientOpenBassTransition f i).app a).map m
        (((boundedAboveFlatCoefficientSupportedBassOpenNull f i).homotopy a).level m (s, x)) =
      ((boundedAboveFlatCoefficientSupportedBassOpenNull f (i + 1)).homotopy a).level m
        (s, ((boundedAboveFlatCoefficientSupportedBassTransition f i).app a).map m x) :=
  boundedAboveFlatCoefficientSupportedBassOpenNull_transition f i a m s x

example (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedBassForget f i).app a) ≫
        (boundedAboveFlatCoefficientSupportedBassOpenConeMap f i).app a =
      (boundedAboveFlatCoefficientAmbientBassOpen f i).app a :=
  boundedAboveFlatCoefficientSupportedBassOpenConeMap_inclusion f i a

example
    (i : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedBassOpenConeMap f i).app a) :=
  boundedAboveFlatCoefficientSupportedBassOpenConeMap_isStableEquivalence f i a

example
    (i : ℕ) (a : Under R) :
    IsStableEquivalence (mappingConeFiberComparison
      ((boundedAboveFlatCoefficientSupportedBassForget f i).app a)) :=
  boundedAboveFlatCoefficientSupportedBassForget_coneFiber_isStableEquivalence f i a

end
