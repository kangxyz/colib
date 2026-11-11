module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedBassTelescope

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]

example (i : ℕ) :
    boundedAboveFlatCoefficientOpenBassGrading f i ≫
      boundedAboveFlatCoefficientGradedOpenBassTransition f i =
      boundedAboveFlatCoefficientFullOpenBassTransition f i ≫
        boundedAboveFlatCoefficientOpenBassGrading f (i + 1) :=
  boundedAboveFlatCoefficientOpenBassGrading_transition f i

example
    (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenBassDiagram f i).obj a).space m) :
    ((boundedAboveFlatCoefficientGradedOpenBassTransition f i).app a).map m
      (((boundedAboveFlatCoefficientOpenBassGradingNull f i).homotopy a).level m (s, x)) =
    ((boundedAboveFlatCoefficientOpenBassGradingNull f (i + 1)).homotopy a).level m
      (s, ((boundedAboveFlatCoefficientOpenBassTransition f i).app a).map m x) :=
  boundedAboveFlatCoefficientOpenBassGradingNull_transition f i a m s x

example (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientOpenBassRestriction f i).app a) ≫
        (boundedAboveFlatCoefficientOpenBassConeComparison f i).app a =
      (boundedAboveFlatCoefficientOpenBassGrading f i).app a :=
  boundedAboveFlatCoefficientOpenBassConeComparison_inclusion f i a

example
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientOpenBassDiagram f i).obj a).space m) :
    ((boundedAboveFlatCoefficientOpenBassTelescopeGradingNull f).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientOpenBassDiagram f k).obj a)
        (fun k ↦ (boundedAboveFlatCoefficientOpenBassTransition f k).app a) m i (t, x)) =
    Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientGradedOpenBassDiagram f k).obj a)
      (fun k ↦ (boundedAboveFlatCoefficientGradedOpenBassTransition f k).app a) m i
        (t, ((boundedAboveFlatCoefficientOpenBassGradingNull f i).homotopy a).level m (s, x)) :=
  boundedAboveFlatCoefficientOpenBassTelescopeGradingNull_cylinder f a m i s t x

variable [QuasiSeparatedSpace Q.left]

example
    (i : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientOpenBassConeComparison f i).app a) :=
  boundedAboveFlatCoefficientOpenBassConeComparison_isStableEquivalence f i a

example
    (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientOpenBassTelescopeConeComparison f).app a) :=
  boundedAboveFlatCoefficientOpenBassTelescopeConeComparison_isStableEquivalence f a

