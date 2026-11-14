/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientInitialConnectingSign
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientInitialTelescopeConnecting
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAuxiliaryInitialConnectingSign
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAuxiliaryFiberConnecting
import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAuxiliaryInitialTelescopeConnecting

open AlgebraicGeometry.Scheme.Modules

#check boundedAboveFlatCoefficientInitialConnecting_original_sign
#check boundedAboveFlatCoefficientInitialConnecting_telescope
#check boundedAboveFlatCoefficientAuxiliaryInitialConnecting_native_sign
#print axioms boundedAboveFlatCoefficientInitialConnecting_original_sign
#print axioms boundedAboveFlatCoefficientInitialConnecting_telescope
#print axioms boundedAboveFlatCoefficientAuxiliaryInitialConnecting_native_sign
#print axioms boundedAboveFlatCoefficientAuxiliaryInitialTelescope_fullOpenNull
#print axioms boundedAboveFlatCoefficientAuxiliaryInitialConnecting_telescope

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Consumer.CoefficientInitialTelescopeConnecting

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The unchanged open inclusion and restriction carry the initial kernel into the fine kernel. -/
theorem initialBoundary_kernel_maps_to_fineBoundary_kernel (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup ((boundedAboveFlatCoefficientOpenBassDiagram f 0).obj a) (d + 1)) :
    let := boundedAboveFlatCoefficientInitialFiberLift_isStableEquivalence f a d
    stableFiberLiftConnecting
        ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
        ((boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
        ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a) d x = 0 →
      boundedAboveFlatCoefficientFineLocalizationConnecting f a d
        ((stableHomotopyFunctor (d + 1)).map
          ((boundedAboveFlatCoefficientOpenBassTelescopeInclusion f 0).app a ≫
            (boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a) x) = 0 := by
  let := boundedAboveFlatCoefficientInitialFiberLift_isStableEquivalence f a d
  dsimp only
  intro hx
  have h := ConcreteCategory.congr_hom
    (boundedAboveFlatCoefficientInitialConnecting_telescope f a d) x
  exact h.symm.trans ((congrArg
    ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)) hx).trans
      (map_zero _))

variable (T : Q.left.Opens) [CompactSpace T]

/-- Auxiliary-support classes with trivial initial boundary still have trivial boundary after
the actual stage-zero inclusion and full-open restriction. -/
theorem auxiliaryInitialBoundary_kernel_maps_to_fineBoundary_kernel (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj
      a) (d + 1)) :
    let := boundedAboveFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a d
    stableFiberLiftConnecting
        ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
        ((boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
        ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a) d x = 0 →
      boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d
        ((stableHomotopyFunctor (d + 1)).map
          ((boundedAboveFlatCoefficientSupportedOpenBassTelescopeInclusion f T 0).app a ≫
            (boundedAboveFlatCoefficientSupportedOpenBassTelescopeRestriction f T).app a) x) =
        0 := by
  let := boundedAboveFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a d
  dsimp only
  intro hx
  have h := ConcreteCategory.congr_hom
    (boundedAboveFlatCoefficientAuxiliaryInitialConnecting_telescope f T a d) x
  exact h.symm.trans ((congrArg
    ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)) hx).trans
      (map_zero _))

end Consumer.CoefficientInitialTelescopeConnecting

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients

namespace Consumer.CoefficientInitialConnecting
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The unchanged geometric boundary detects vanishing before supported evaluation. -/
theorem initial_boundary_eq_zero_iff_original_boundary_eq_one (a : Under R) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : (boundedAboveFlatCoefficientOpenModel f a).obj.waldhausen.K (n + 1)) :
    let := boundedAboveFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ)
    stableFiberLiftConnecting
      ((boundedAboveFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
      ((boundedAboveFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
      ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a) (n : ℤ)
      (eqToHom (congrArg (stableHomotopyGroup
        ((boundedAboveFlatCoefficientOpenPrespectrumFunctor f).obj a)) κ)
        (smallModelKStableEquiv (boundedAboveFlatCoefficientOpenModel f a) (n + 1)
            (Additive.ofMul x))) = 0 ↔
      changeWeakConnectingHom (boundedAboveFlatPerfectOpenNested (schemeMap f a))
        (boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence
          (schemeMap f a)) n
        (boundedAboveFlatCoefficientOpenKEquiv f a (n + 1) x) = 1 := by
  let := boundedAboveFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ)
  dsimp only
  have hi := (ConcreteCategory.isIso_iff_bijective
    ((stableHomotopyFunctor (n : ℤ)).map (prespectrumMap (supportAcyclicModelMap f a)))).mp
      (supportAcyclicModelMap_isStableEquivalence f a n)
  have hs := boundedAboveFlatCoefficientInitialConnecting_original_sign f a n κ x
  dsimp only at hs
  constructor
  · intro hx
    rw [hx, map_zero, eq_comm, neg_eq_zero] at hs
    have hz : Additive.ofMul (changeWeakConnectingHom
        (boundedAboveFlatPerfectOpenNested (schemeMap f a))
        (boundedAboveFlatPerfectOpen_canonicalFiberMap_isWeakHomotopyEquivalence
          (schemeMap f a)) n
        (boundedAboveFlatCoefficientOpenKEquiv f a (n + 1) x)) = 0 :=
      (originalKStableEquiv (acyclicStructure
        (boundedAboveFlatPerfectOpenNested (schemeMap f a))) n).injective
        (hs.trans (map_zero _).symm)
    exact ofMul_eq_zero.mp hz
  · intro hx
    apply hi.injective
    rw [map_zero]
    rw [hs, hx, ofMul_one, map_zero, neg_zero]

end Consumer.CoefficientInitialConnecting
