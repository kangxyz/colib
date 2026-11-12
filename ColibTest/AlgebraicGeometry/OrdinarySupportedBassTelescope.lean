module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTelescope
noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
open AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

example
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedBassDiagram f i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientSupportedBassDiagram f k).obj a)
        (fun k ↦ (boundedAboveFlatCoefficientSupportedBassTransition f k).app a) m i (t, x)) =
    Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientOpenBassDiagram f k).obj a)
      (fun k ↦ (boundedAboveFlatCoefficientOpenBassTransition f k).app a) m i
        (t, ((boundedAboveFlatCoefficientSupportedBassOpenNull f i).homotopy a).level m (s, x)) :=
  boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull_cylinder f a m i s t x

example (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a) ≫
        (boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap f).app a =
      (boundedAboveFlatCoefficientAmbientBassTelescopeOpen f).app a :=
  boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap_inclusion f a

example
    (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap f).app a)
      :=
  boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap_isStableEquivalence f a

example
    (a : Under R) : IsStableEquivalence (mappingConeFiberComparison
      ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)) :=
  boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a

example
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap f).app a) ≫
      stableFiberConnecting ((boundedAboveFlatCoefficientAmbientBassTelescopeOpen f).app a) d =
    stableMappingConeConnecting ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
      (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a)
        d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift
          ((boundedAboveFlatCoefficientAmbientBassTelescopeOpen f).app a)
          ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
          ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a)) :=
  boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap_connecting f a d

end
