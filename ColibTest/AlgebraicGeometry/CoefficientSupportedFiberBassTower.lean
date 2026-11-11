module
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberBassTower

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open AlgebraicGeometry.Scheme.Modules CommRingCat.PolynomialLaurent
universe u
noncomputable section
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

example (i : ℕ) :
    boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i =
      (strictDiagramIterate (laurentUnderSquareFunctor R) i).obj
        (boundedAboveFlatCoefficientSupportedFiberPrespectrumFunctor f T) := rfl

example (i : ℕ) :
    boundedAboveFlatCoefficientSupportedFiberBassForget f T i ≫
        boundedAboveFlatCoefficientSupportedAmbientBassTransition T i =
      boundedAboveFlatCoefficientSupportedFiberBassTransition f T i ≫
        boundedAboveFlatCoefficientSupportedFiberBassForget f T (i + 1) :=
  boundedAboveFlatCoefficientSupportedFiberBassForget_transition f T i

example (i : ℕ) (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatCoefficientSupportedFiberBassDiagram f T i).obj a).space m) :
    ((boundedAboveFlatCoefficientSupportedOpenBassTransition f T i).app a).map m
        (((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T i).homotopy a).level m
          (s, x)) =
      ((boundedAboveFlatCoefficientSupportedFiberBassOpenNull f T (i + 1)).homotopy a).level m
        (s, ((boundedAboveFlatCoefficientSupportedFiberBassTransition f T i).app a).map m x) :=
  boundedAboveFlatCoefficientSupportedFiberBassOpenNull_transition f T i a m s x

example (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedAboveFlatCoefficientSupportedFiberBassForget f T i).app a) ≫
        (boundedAboveFlatCoefficientSupportedFiberBassOpenConeMap f T i).app a =
      (boundedAboveFlatCoefficientSupportedAmbientBassOpen f T i).app a :=
  boundedAboveFlatCoefficientSupportedFiberBassOpenConeMap_inclusion f T i a

example (i : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedAboveFlatCoefficientSupportedFiberBassOpenConeMap f T i).app a) :=
  boundedAboveFlatCoefficientSupportedFiberBassOpenConeMap_isStableEquivalence f T i a

example (i : ℕ) (a : Under R) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      ((boundedAboveFlatCoefficientSupportedFiberBassOpenConeMap f T i).app a)) :=
  boundedAboveFlatCoefficientSupportedFiberBassOpenConeMap_isStableEquivalence f T i a _

example (i : ℕ) (a : Under R) :
    IsStableEquivalence (mappingConeFiberComparison
      ((boundedAboveFlatCoefficientSupportedFiberBassForget f T i).app a)) :=
  boundedAboveFlatCoefficientSupportedFiberBassForget_coneFiber_isStableEquivalence f T i a
