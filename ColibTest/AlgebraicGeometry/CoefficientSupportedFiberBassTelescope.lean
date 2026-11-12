module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberBassTelescope

open CategoryTheory Topology Topology.LoopPrespectrum AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules KTheory.Bass CommRingCat.PolynomialLaurent
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (T : Q.left.Opens)

example (i : ℕ) :
    boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T i ≫
        boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T =
      boundedAboveFlatCoefficientSupportedFiberBassForget f T i ≫
        boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T i :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion_forget f T i

example (i : ℕ) :
    boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T i ≫
        boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f T =
      boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i ≫
        boundedAboveFlatCoefficientSupportedOpenBassTelescopeInclusion f T i :=
  boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion_open f T i

example
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a).level m
      (s, Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientSupportedFiberBassDiagram f T
        k).obj a)
        (fun k ↦ (boundedAboveFlatCoefficientSupportedFiberBassTransition f T k).app a) m i (t,
          x)) =
    Telescope.cylinder (fun k ↦ (boundedAboveFlatCoefficientSupportedOpenBassDiagram f T k).obj a)
      (fun k ↦ (boundedAboveFlatCoefficientSupportedOpenBassTransition f T k).app a) m i
        (t, ((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a).level m (s,
          x)) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull_cylinder f T a m i s t x

example (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app
      a) ≫
        (boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap f T).app a =
      (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f T).app a :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_inclusion f T a

example
    (a : Under R) : IsStableEquivalence (mappingConeFiberComparison
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence f T a

example
    (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap f
      T).app a)
      :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_isStableEquivalence f T a

example
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap f T).app a) ≫
      stableFiberConnecting ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f
        T).app a) d
        =
    stableMappingConeConnecting ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f
      T).app
      a)
      (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence
        f T a)
        d ≫
        (stableHomotopyFunctor d).map (homotopyFiberLift
          ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f T).app a)
          ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
          ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a)) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_connecting f T a d

example :
    DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T)
      (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeOpen f T) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T

example (a : Under R) (j : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat j + 1))).map
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap f T).app a)) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenConeMap_isStableEquivalence f T a _
