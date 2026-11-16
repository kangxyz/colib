/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryFineConnectingComparison
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

/-- The actual fiber Spec-row map preserves the independent original stage-zero inclusion. -/
theorem iterated_fine_initial_fiber :
    Functor.whiskerLeft specUnder (iteratedInitial (fiberAction f.left T)) ≫
        fiberTelescopeComparison f T =
      Functor.whiskerRight (fiberComparison f T) prespectrumFunctor ≫
        boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0 := by
  ext a
  rfl

omit [IsOpenImmersion f.left] in
/-- The actual open Spec-row map preserves the independent original stage-zero inclusion. -/
theorem iterated_fine_initial_open :
    Functor.whiskerLeft specUnder (iteratedInitial (openAction f.left T)) ≫
        openTelescopeComparison f T =
      Functor.whiskerRight (openComparison f T) prespectrumFunctor ≫
        boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0 := by
  ext a
  rfl


/-- The auxiliary current initial class is sent to the original fine fiber class, in every
degree. -/
theorem current_fine_initial_fiber (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (stableHomotopyFunctor d).map ((currentInitial (fiberAction f.left T)).app
      (specUnder.obj a)) ≫ (currentFineSupportComparison f T a d).hom =
      (stableHomotopyFunctor d).map (prespectrumMap ((fiberComparison f T).app a)) ≫
        (stableHomotopyFunctor d).map
          ((boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a) := by
  have h := currentIteratedStableIso_initial (fiber f.left T)
    (fiberAction f.left T) (specUnder.obj a) d
  have hv := congrArg (stableHomotopyFunctor d).map
    (congrArg (fun η => η.app a) (iterated_fine_initial_fiber f T))
  simp only [NatTrans.comp_app, Functor.map_comp] at hv
  change _ ≫ ((currentIteratedStableIso _ _ _ _).hom ≫ _) = _
  rw [← Category.assoc, h]
  exact hv

omit [IsOpenImmersion f.left] in
/-- The auxiliary current initial open class is sent to the original fine open class. -/
theorem current_fine_initial_open (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (stableHomotopyFunctor d).map ((currentInitial (openAction f.left T)).app
      (specUnder.obj a)) ≫ (currentFineOpenComparison f T a d).hom =
      (stableHomotopyFunctor d).map (prespectrumMap ((openComparison f T).app a)) ≫
        (stableHomotopyFunctor d).map
          ((boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a) := by
  have h := currentIteratedStableIso_initial (openModel f.left T)
    (openAction f.left T) (specUnder.obj a) d
  have hv := congrArg (stableHomotopyFunctor d).map
    (congrArg (fun η => η.app a) (iterated_fine_initial_open f T))
  simp only [NatTrans.comp_app, Functor.map_comp] at hv
  change _ ≫ ((currentIteratedStableIso _ _ _ _).hom ≫ _) = _
  rw [← Category.assoc, h]
  exact hv

end AlgebraicGeometry.Scheme.Modules.ParameterAuxiliaryCurrentFiber
