/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInitialModelClasses
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryInitialClasses
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAuxiliaryPerfectClasses
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeStageZeroComparison

/-! # Independently defined auxiliary stage-zero classes through the actual comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass CategoryTheory.Waldhausen.IteratedS
open KTheory.Bass.SchemeNaturalSeed
open CategoryTheory.Waldhausen.SmallWaldhausenCategory

universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber
open GlobalSectionChangeIndex GlobalSupportedSection.ParameterAuxiliarySupport
  GlobalAuxiliaryParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The actual ambient Spec-row map preserves the independent original stage-zero inclusion. -/
theorem iterated_fine_initial_ambient :
    Functor.whiskerLeft specUnder (iteratedInitial (ambientAction T)) ≫
        ambientTelescopeComparison Q T =
      Functor.whiskerRight (ambientComparison Q T) prespectrumFunctor ≫
        boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0 := by
  ext a
  rfl

/-- The ambient comparison uses the same three actual telescope maps and original row map. -/
def currentFineAmbientComparison (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    stableHomotopyGroup ((currentTelescope (ambientAction T)).obj (specUnder.obj a)) d ≅
      stableHomotopyGroup
        ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeFunctor T).obj a) d := by
  letI := ambientTelescopeComparison_stable Q T a d
  exact (currentIteratedStableIso (ambient T) (ambientAction T) (specUnder.obj a) d) ≪≫
    asIso ((stableHomotopyFunctor d).map ((ambientTelescopeComparison Q T).app a))

/-- The independent ambient initial class follows the original supported evaluation. -/
theorem current_fine_ambient_modelClass
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((ambient T).obj (specUnder.obj a)).obj.waldhausen.K n) :
    (currentFineAmbientComparison T a (n : ℤ)).hom
        (currentModelClass (ambient T) (ambientAction T) (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a)
        (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedAmbientModel T a) n
          (Additive.ofMul (CategoryTheory.Waldhausen.KMap
            ((ambientComparison Q T).app a).hom.isExact n x))) := by
  have h := currentIteratedStableIso_initial (ambient T)
    (ambientAction T) (specUnder.obj a) (n : ℤ)
  have hv := congrArg (stableHomotopyFunctor (n : ℤ)).map
    (congrArg (fun η => η.app a) (iterated_fine_initial_ambient T))
  simp only [NatTrans.comp_app, Functor.map_comp] at hv
  have hi : (stableHomotopyFunctor (n : ℤ)).map
      ((currentInitial (ambientAction T)).app (specUnder.obj a)) ≫
        (currentFineAmbientComparison T a (n : ℤ)).hom =
      (stableHomotopyFunctor (n : ℤ)).map (prespectrumMap ((ambientComparison Q T).app a)) ≫
        (stableHomotopyFunctor (n : ℤ)).map
          ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a) := by
    change _ ≫ ((currentIteratedStableIso _ _ _ _).hom ≫ _) = _
    rw [← Category.assoc, h]
    exact hv
  exact (ConcreteCategory.congr_hom hi
    (smallModelKStableEquiv ((ambient T).obj (specUnder.obj a)) n (Additive.ofMul x))).trans
    (congrArg ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a))
      (smallModelKStableEquiv_naturality ((ambientComparison Q T).app a) n x).symm)

/-- The original nonnegative fiber Model class follows the actual row map and old inclusion. -/
theorem current_fine_fiber_modelClass (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((fiber f.left T).obj (specUnder.obj a)).obj.waldhausen.K n) :
    (ParameterAuxiliaryCurrentFiber.currentFineSupportComparison f T a (n : ℤ)).hom
        (currentModelClass (fiber f.left T)
          (fiberAction f.left T) (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedFiberModel f T a) n
          (Additive.ofMul (CategoryTheory.Waldhausen.KMap
            ((GlobalAuxiliaryParameterCoefficient.fiberComparison f T).app a).hom.isExact n x)))
              := by
  have h := ConcreteCategory.congr_hom
    (ParameterAuxiliaryCurrentFiber.current_fine_initial_fiber f T a (n : ℤ))
    (smallModelKStableEquiv ((fiber f.left T).obj (specUnder.obj a)) n
      (Additive.ofMul x))
  exact h.trans (congrArg
    ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a))
    (smallModelKStableEquiv_naturality ((GlobalAuxiliaryParameterCoefficient.fiberComparison f
      T).app
      a) n x).symm)

omit [IsOpenImmersion f.left] in
/-- The original nonnegative open Model class follows the actual row map and old inclusion. -/
theorem current_fine_open_modelClass (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((openModel f.left T).obj (specUnder.obj a)).obj.waldhausen.K n) :
    (ParameterAuxiliaryCurrentFiber.currentFineOpenComparison f T a (n : ℤ)).hom
        (currentModelClass (openModel f.left T)
          (openAction f.left T) (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
        (smallModelKStableEquiv (boundedAboveFlatCoefficientSupportedFullOpenModel f T a) n
          (Additive.ofMul (CategoryTheory.Waldhausen.KMap
            ((GlobalAuxiliaryParameterCoefficient.openComparison f T).app a).hom.isExact n x)))
              := by
  have h := ConcreteCategory.congr_hom
    (ParameterAuxiliaryCurrentFiber.current_fine_initial_open f T a (n : ℤ))
    (smallModelKStableEquiv ((openModel f.left T).obj (specUnder.obj a)) n
      (Additive.ofMul x))
  exact h.trans (congrArg
    ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a))
    (smallModelKStableEquiv_naturality ((GlobalAuxiliaryParameterCoefficient.openComparison f
      T).app a)
      n x).symm)


/-- The independent current fiber class reaches the original perfect supported group. -/
theorem current_fine_fiber_perfectClass [CompactSpace Q.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((fiber f.left T).obj (specUnder.obj a)).obj.waldhausen.K n) :
    (currentFineSupportComparison f T a (n : ℤ)).hom
        (currentModelClass (fiber f.left T) (fiberAction f.left T) (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (auxiliaryFiberPerfectStableEquiv f T a n
          (Additive.ofMul (auxiliaryFiberPerfectKEquiv f T a n
            (CategoryTheory.Waldhausen.KMap ((fiberComparison f T).app a).hom.isExact n x)))) := by
  rw [auxiliaryFiberPerfectStableEquiv_evaluation]
  exact current_fine_fiber_modelClass f T a n x

/-- The independent current ambient class reaches the original perfect supported group. -/
theorem current_fine_ambient_perfectClass [CompactSpace Q.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((ambient T).obj (specUnder.obj a)).obj.waldhausen.K n) :
    (currentFineAmbientComparison T a (n : ℤ)).hom
        (currentModelClass (ambient T) (ambientAction T) (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T 0).app a)
        (auxiliaryAmbientPerfectStableEquiv T a n
          (Additive.ofMul (auxiliaryAmbientPerfectKEquiv T a n
            (CategoryTheory.Waldhausen.KMap ((ambientComparison Q T).app a).hom.isExact n x))))
              := by
  rw [auxiliaryAmbientPerfectStableEquiv_evaluation]
  exact current_fine_ambient_modelClass T a n x

omit [IsOpenImmersion f.left] in
/-- The independent current open class reaches the original perfect supported group. -/
theorem current_fine_open_perfectClass [CompactSpace P.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((openModel f.left T).obj (specUnder.obj a)).obj.waldhausen.K n) :
    (currentFineOpenComparison f T a (n : ℤ)).hom
        (currentModelClass (openModel f.left T) (openAction f.left T) (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
        (auxiliaryOpenPerfectStableEquiv f T a n
          (Additive.ofMul (auxiliaryOpenPerfectKEquiv f T a n
            (CategoryTheory.Waldhausen.KMap ((openComparison f T).app a).hom.isExact n x)))) := by
  rw [auxiliaryOpenPerfectStableEquiv_evaluation]
  exact current_fine_open_modelClass f T a n x

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber
