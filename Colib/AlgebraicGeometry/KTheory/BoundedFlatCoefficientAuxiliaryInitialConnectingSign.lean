/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAuxiliaryInitialConnecting
public import Colib.KTheory.Waldhausen.Iterated.SmallModelComparison
public import Colib.KTheory.Waldhausen.Fibration.StableConnectingComparison

/-!
# The original native sign in initial auxiliary-supported localization

The intrinsic initial coefficient connecting map, evaluated by the actual
native supported-to-acyclic Model map, is the negative of the unchanged native
Waldhausen boundary class. The original native inclusion and degree cast
are kept explicitly; this does not yet identify a Bass telescope endpoint.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Fibration
open CategoryTheory.Waldhausen.IteratedS
open Topology Topology.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology
open HomotopyGroup
universe u
namespace AlgebraicGeometry.Scheme.Modules

private theorem stableMap_degree_cast {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    {d e : ℤ} (h : d = e) :
    eqToHom (congrArg (stableHomotopyGroup E) h) ≫ (stableHomotopyFunctor e).map f =
      (stableHomotopyFunctor d).map f ≫ eqToHom (congrArg (stableHomotopyGroup F) h) := by
  subst e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem piMap_congr {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y} (n : ℕ) (f g : C(X, Y)) (hf : f x = y) (hg : g x = y)
    (h : f = g) : piMap n f hf = piMap n g hg := by
  subst g
  rfl

/-- The literal common-universe inclusion preserves the original native K-stable class. -/
theorem boundedAboveFlatCoefficientNativeSmallModelMap_stable
    (M : WideSubcategory preservesZero.{u})
    (F : M ⟶ asSmallCategory M.obj.waldhausen) (hF : F.hom.toFunctor = AsSmall.up)
    (n : ℕ) (x : M.obj.waldhausen.K n) :
    (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap F)
        (smallModelKStableEquiv M n (Additive.ofMul x)) =
      originalKStableEquiv M.obj.waldhausen n (Additive.ofMul x) := by
  have hK : KMap F.hom.isExact n x = M.obj.waldhausen.asSmallKEquiv n x := by
    rw [KMap_eq_piMap_of_zeroEq F.hom.isExact F.property]
    have hd : (deloopingMap F.hom.isExact).hom =
        M.obj.waldhausen.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun := by
      change (SSet.toTop.map (sSetMap F.hom.isExact)).hom = _
      have hs : sSetMap F.hom.isExact = M.obj.waldhausen.asSmallSSetIso.hom := by
        ext A B : 4
        apply Subtype.ext
        change _ ⋙ F.hom.toFunctor = _ ⋙ AsSmall.up
        rw [hF]
      rw [hs]
      rfl
    change piMap n (deloopingMap F.hom.isExact).hom _ x =
      piMap n M.obj.waldhausen.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun _ x
    exact DFunLike.congr_fun (piMap_congr n _ _ _ _ hd) x
  have hn := (smallModelKStableEquiv_naturality F n x).symm
  rw [hK] at hn
  exact hn

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Original native conversion detects the negative sign of the actual auxiliary boundary. -/
theorem boundedAboveFlatCoefficientAuxiliaryInitialConnecting_native_sign (a : Under R) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : (boundedAboveFlatCoefficientSupportedOpenModel f T a).obj.waldhausen.K (n + 1)) :
    let := boundedAboveFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a (n : ℤ)
    (stableHomotopyFunctor (n : ℤ)).map
      (prespectrumMap (supportedNativeFiberAcyclicModelMap f T a))
        (stableFiberLiftConnecting
          ((boundedAboveFlatCoefficientSupportedFiberForgetPrespectrumTransformation f T).app a)
          ((boundedAboveFlatCoefficientSupportedAmbientOpenPrespectrumTransformation f T).app a)
          ((boundedAboveFlatCoefficientSupportedFiberOpenDiagramNull f T).homotopy a) (n : ℤ)
          (eqToHom (congrArg (stableHomotopyGroup
            ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)) κ)
            (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedOpenModel f T a) (n + 1)
              (Additive.ofMul x)))) =
      -(originalKStableEquiv (acyclicStructure
        (boundedAboveFlatCoefficientSupportedOpenNested f T a)) n
        (Additive.ofMul (changeWeakConnectingHom
          (boundedAboveFlatCoefficientSupportedOpenNested f T a)
          (boundedAboveFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
            f T a) n
          x))) := by
  let := boundedAboveFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a (n : ℤ)
  let := boundedAboveFlatCoefficientAuxiliaryNativeFiberLift_isStableEquivalence f T a (n : ℤ)
  have he := ConcreteCategory.congr_hom
    (boundedAboveFlatCoefficientAuxiliaryInitialConnecting_native f T a (n : ℤ))
    (eqToHom (congrArg (stableHomotopyGroup
      ((boundedAboveFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)) κ)
      (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedOpenModel f T a) (n + 1)
        (Additive.ofMul x)))
  have hc := ConcreteCategory.congr_hom
    (stableMap_degree_cast (prespectrumMap (supportedNativeCoarseModelMap f T a)) κ)
    (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedOpenModel f T a) (n + 1)
      (Additive.ofMul x))
  have hk := boundedAboveFlatCoefficientNativeSmallModelMap_stable
    (boundedAboveFlatCoefficientSupportedOpenModel f T a)
    (supportedNativeCoarseModelMap f T a) rfl (n + 1) x
  have ht := hc.trans (congrArg
    (eqToHom (congrArg (stableHomotopyGroup
      (originalPrespectrum (boundedAboveFlatCoefficientSupportedOpenWaldhausen f T a))) κ)) hk)
  exact he.trans ((congrArg
    (stableFiberLiftConnecting
      (acyclicInclusionPrespectrumMap (boundedAboveFlatCoefficientSupportedOpenNested f T a))
      (changeWeakPrespectrumMap (boundedAboveFlatCoefficientSupportedOpenNested f T a))
      (acyclicPrespectrumNullhomotopy
            (boundedAboveFlatCoefficientSupportedOpenNested f T a)) (n : ℤ))
    ht).trans (originalKStableEquiv_liftConnecting_sign _
      (boundedAboveFlatCoefficientSupportedOpen_canonicalFiberMap_isWeakHomotopyEquivalence
            f T a) n κ
      x))

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-1276",
  colib_ref "quillen"
    "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
      CoefficientAuxiliaryInitialConnectingSign.lean:74"
    "adaptation" "Native auxiliary support conversion gives the original initial minus sign"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatCoefficientAuxiliaryInitialConnecting_native_sign
