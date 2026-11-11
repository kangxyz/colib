module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFullOpenBassLocalization

open CategoryTheory Topology Topology.LoopPrespectrum AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules KTheory.Bass CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS
noncomputable section
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (T : Q.left.Opens)

example : boundedAboveFlatCoefficientSupportedAmbientModelFunctor T ⟶
    boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T :=
  boundedAboveFlatCoefficientSupportedFineRestrictionModelTransformation f T

example : DiagramNullHomotopy (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T)
    (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T

example (i : ℕ) :
    boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i ≫
      boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i =
      (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
        (Functor.whiskerRight
          (boundedAboveFlatCoefficientSupportedFineRestrictionModelTransformation f T)
          prespectrumFunctor) :=
  boundedAboveFlatCoefficientSupportedAmbientBassFullOpen_eq_original f T i

example (i : ℕ) :
    boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T i ≫
        boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T =
      (boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i ≫
        boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i) ≫
        boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T i :=
  boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion_fullOpen f T i

example
    (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a).level m
        (s, x) =
      ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a).map m
        (((boundedAboveFlatCoefficientSupportedFiberBassTelescopeOpenNull f T).homotopy a).level m
          (s, x)) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull_level f T a m s x

example (a : Under
  R) :
    (boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a =
      mappingConeDesc ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_eq_desc f T a

example (a : Under
  R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app
      a) ≫
        (boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a =
      (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_inclusion f T a

example
    (a : Under R) (m i : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a).map m
      (Topology.ReducedMappingCone.cylinder
        (((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj a).point m)
        (((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFunctor T).obj a).point m)
        (((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a).map m)
        (s, Telescope.cylinder
          (fun n ↦ (boundedAboveFlatCoefficientSupportedFiberBassDiagram f T n).obj a)
          (fun n ↦ (boundedAboveFlatCoefficientSupportedFiberBassTransition f T n).app a) m i (t,
            x))) =
      Telescope.cylinder (fun n ↦ (boundedAboveFlatCoefficientSupportedFullOpenBassDiagram f T
        n).obj a)
        (fun n ↦ (boundedAboveFlatCoefficientSupportedFullOpenBassTransition f T n).app a) m i
          (t, ((boundedAboveFlatCoefficientSupportedOpenBassRestriction f T i).app a).map m
            (((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a).level m
              (s, x))) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_cylinder f T a m i s t x

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
    [CompactSpace T]

example
    (a : Under R) :
    IsStableEquivalence
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_isStableEquivalence f T a

example (a :
  Under R) :
    boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f T a ≫
        homotopyFiberProjection
          ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a) =
      (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_projection f T a

example
    (a : Under R) :
    IsStableEquivalence (boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f
      T a) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence f T a

example
    (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a) ≫
      stableFiberConnecting
          ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a) d =
    stableMappingConeConnecting
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
      (boundedAboveFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence
        f T a)
        d ≫
        (stableHomotopyFunctor d).map
          (boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f T a) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_connecting f T a d

example (a : Under R) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(k : ℤ) - 1)).map
      (boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f T a)) :=
  boundedAboveFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence
    f T a (-(k : ℤ) - 1)
