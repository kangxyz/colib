module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryGradedBassVanishing

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]

example : Under R ⥤ LoopPrespectrum.{u + 1} :=
  boundedAboveFlatCoefficientGradedOpenBassTelescopeFunctor f

example (i : ℕ) (a : Under R) :
    LoopPrespectrum.Homotopy ((boundedAboveFlatCoefficientGradedOpenBassTransition f i).app a)
      (zeroHom ((boundedAboveFlatCoefficientGradedOpenBassDiagram f i).obj a)
        ((boundedAboveFlatCoefficientGradedOpenBassDiagram f (i + 1)).obj a)) :=
  boundedAboveFlatCoefficientGradedOpenBassTransitionNull f i a

example
    (i : ℕ) (a : Under R) (k : ℕ) :
    (stableHomotopyFunctor (-(k : ℤ) - 1)).map
      ((boundedAboveFlatCoefficientGradedOpenBassTransition f i).app a) = 0 :=
  boundedAboveFlatCoefficientGradedOpenBassTransition_stableMap_eq_zero f i a (-(k : ℤ) - 1)

example
    (i : ℕ) (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientGradedOpenBassTelescopeInclusion f i).app a) = 0 :=
  boundedAboveFlatCoefficientGradedOpenBassTelescopeInclusion_stableMap_eq_zero f i a d

example
    (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup ((boundedAboveFlatCoefficientGradedOpenBassTelescopeFunctor f).obj a)
      d) :
    x = 0 :=
  boundedAboveFlatCoefficientGradedOpenBassTelescope_stableClass_eq_zero f a d x

example
    (a : Under R) (d : ℤ) : Subsingleton (stableHomotopyGroup
      ((boundedAboveFlatCoefficientGradedOpenBassTelescopeFunctor f).obj a) d) :=
  boundedAboveFlatCoefficientGradedOpenBassTelescope_stableGroup_subsingleton f a d
