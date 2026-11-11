module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedGradedBassTelescope

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules KTheory.Bass
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

example (i : ℕ) :
    boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i ≫
        boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T i =
      boundedAboveFlatCoefficientSupportedOpenBassTransition f T i ≫
        boundedAboveFlatCoefficientSupportedOpenBassRestriction f T (i + 1) :=
  boundedAboveFlatCoefficientSupportedOpenBassRestriction_transition f T i

example (i : ℕ) (a : Under R) :
    IsStableEquivalence
      (mappingConeFiberComparison
        ((boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i).app a)) :=
  boundedAboveFlatCoefficientSupportedOpenBassRestriction_coneFiber_isStableEquivalence f T i a

variable [CompactSpace P.left] [CompactSpace Q.left]

example (i : ℕ) (a : Under R) :
    Homotopy ((boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T i).app a)
      (zeroHom ((boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T i).obj a)
        ((boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T (i + 1)).obj a)) :=
  boundedAboveFlatCoefficientSupportedGradedOpenBassTransitionNull f T i a

example (i k : ℕ) (a : Under R) :
    (stableHomotopyFunctor (-(k : ℤ) - 1)).map
      ((boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T i).app a) = 0 :=
  boundedAboveFlatCoefficientSupportedGradedOpenBassTransition_stableMap_eq_zero
    f T i a (-(k : ℤ) - 1)

example (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T i).app a).map m
      (((boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T i).homotopy a).level m
        (s, x)) =
    ((boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T (i + 1)).homotopy a).level m
      (s, ((boundedAboveFlatCoefficientSupportedOpenBassTransition f T i).app a).map m x) :=
  boundedAboveFlatCoefficientSupportedOpenBassGradingNull_transition f T i a m s x

example (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i).app a) ≫
        (boundedAboveFlatCoefficientSupportedOpenBassConeComparison f T i).app a =
      (boundedAboveFlatCoefficientSupportedOpenBassGrading f T i).app a :=
  boundedAboveFlatCoefficientSupportedOpenBassConeComparison_inclusion f T i a

example (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedOpenBassDiagram f T i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeGradingNull f T).homotopy a).level m
      (s, Telescope.cylinder
        (fun k ↦ (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T k).obj a)
        (fun k ↦ (boundedAboveFlatCoefficientSupportedOpenBassTransition f T k).app a) m i
          (t, x)) =
    Telescope.cylinder
      (fun k ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassDiagram f T k).obj a)
      (fun k ↦ (boundedAboveFlatCoefficientSupportedGradedOpenBassTransition f T k).app a) m i
        (t, ((boundedAboveFlatCoefficientSupportedOpenBassGradingNull f T i).homotopy a).level m
          (s, x)) :=
  boundedAboveFlatCoefficientSupportedOpenBassTelescopeGradingNull_cylinder f T a m i s t x

example (i k : ℕ) (a : Under R) :
    (stableHomotopyFunctor (-(k : ℤ) - 1)).map
      ((boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeInclusion f T i).app a) = 0 :=
  boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeInclusion_stableMap_eq_zero
    f T i a (-(k : ℤ) - 1)

example (a : Under R) (d : ℤ) :
    Subsingleton (stableHomotopyGroup
      ((boundedAboveFlatCoefficientSupportedGradedOpenBassTelescopeFunctor f T).obj a) d) :=
  boundedAboveFlatCoefficientSupportedGradedOpenBassTelescope_stableGroup_subsingleton f T a d

variable [QuasiSeparatedSpace Q.left] [CompactSpace T]

example (a : Under R) :
    IsStableEquivalence
      ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeConeComparison f T).app a) :=
  boundedAboveFlatCoefficientSupportedOpenBassTelescopeConeComparison_isStableEquivalence f T a

example (a : Under R) :
    IsStableEquivalence
      ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a) :=
  boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction_isStableEquivalence f T a
