/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientInitialEvaluationConnecting
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportEvaluationClasses
public import Colib.KTheory.Waldhausen.Fibration.StableConnectingComparison

/-!
# The original geometric sign in initial coefficient localization

The intrinsic initial coefficient connecting map, evaluated by the actual
supported-to-acyclic Model map, is the negative of the unchanged geometric
Waldhausen boundary class. The original coefficient evaluation and degree cast
are kept explicitly; this does not yet identify a Bass telescope endpoint.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem stableMap_degree_cast {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    {d e : ℤ} (h : d = e) :
    eqToHom (congrArg (stableHomotopyGroup E) h) ≫ (stableHomotopyFunctor e).map f =
      (stableHomotopyFunctor d).map f ≫ eqToHom (congrArg (stableHomotopyGroup F) h) := by
  subst e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- Original evaluation detects the actual negative sign of the initial geometric boundary. -/
theorem boundedAboveFlatCoefficientInitialConnecting_original_sign (a : Under R) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : (boundedAboveFlatCoefficientOpenModel f a).obj.waldhausen.K (n + 1)) :
    let := boundedAboveFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ)
    (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap (supportAcyclicModelMap f a))
        (stableFiberLiftConnecting
          ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
          ((boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
          ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a) (n : ℤ)
          (eqToHom (congrArg (stableHomotopyGroup
            ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a)) κ)
            (smallModelKStableEquiv (boundedAboveFlatCoefficientOpenModel f a) (n + 1)
              (Additive.ofMul x)))) =
      -(originalKStableEquiv (acyclicStructure
        (boundedAboveFlatPerfectOpenNested (schemeMap f a))) n
        (Additive.ofMul (changeWeakConnectingHom (boundedAboveFlatPerfectOpenNested (schemeMap f a))
          (boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence
            (schemeMap f a)) n
          (boundedAboveFlatCoefficientOpenKEquiv f a (n + 1) x)))) := by
  let := boundedAboveFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ)
  let := boundedAboveFlatCoefficientGeometricFiberLift_isStableEquivalence f a (n : ℤ)
  have he := ConcreteCategory.congr_hom
    (boundedAboveFlatCoefficientInitialConnecting_evaluation f a (n : ℤ))
    (eqToHom (congrArg (stableHomotopyGroup
      ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a)) κ)
      (smallModelKStableEquiv (boundedAboveFlatCoefficientOpenModel f a) (n + 1)
        (Additive.ofMul x)))
  have hc := ConcreteCategory.congr_hom
    (stableMap_degree_cast (prespectrumMap (openEvaluationModelMap f a)) κ)
    (smallModelKStableEquiv (boundedAboveFlatCoefficientOpenModel f a) (n + 1) (Additive.ofMul x))
  have hk := openEvaluationModelMap_stable f a (n + 1) x
  have ht := hc.trans (congrArg
    (eqToHom (congrArg (stableHomotopyGroup
      (originalPrespectrum (boundedAboveFlatPerfectOpenWaldhausen (schemeMap f a)))) κ)) hk)
  exact he.trans ((congrArg
    (stableFiberLiftConnecting
      (acyclicInclusionPrespectrumMap (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
      (changeWeakPrespectrumMap (boundedAboveFlatPerfectOpenNested (schemeMap f a)))
      (acyclicPrespectrumNullhomotopy
        (boundedAboveFlatPerfectOpenNested (schemeMap f a))) (n : ℤ))
    ht).trans (originalKStableEquiv_liftConnecting_sign _
      (boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence (schemeMap f a)) n κ
      (boundedAboveFlatCoefficientOpenKEquiv f a (n + 1) x)))

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-1276",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      CoefficientInitialConnectingSign.lean:40"
    "adaptation" "The literal initial supported evaluation preserves the original minus sign"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientInitialConnecting_original_sign
