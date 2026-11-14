/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowNormalizedClasses
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterTensorNormalizedRowPresentation
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterSupportedCurrentStageRange

/-!
# Original supported negative classes in the normalized row

The original finite-bottom comparison is followed by the actual independent
finite normalized-row inclusion. The current comparison has this same image
at every index. The definition retains the original negative groups and every
finite degree cast, without defining their classes through a telescope inverse.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- The unchanged finite negative class followed by the actual finite row inclusion. -/
def normalizedRowNegativeClass (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  (finiteNegativeKComparison f i).hom.app a ≫
    (stableHomotopyFunctor (-(i : ℤ))).map
      (SchemeModelRowSeed.normalizedStageInclusion (ParameterModels.supported f.left)
        (ParameterLaurentTrack.supportedUnit f.left)
        (ParameterLaurentTrack.supportedUnit_naturality f.left) (specUnder.obj a) i)

variable [CompactSpace P.left] [QuasiSeparatedSpace Q.left]

/-- Every original current negative class has its independent finite normalized-row image. -/
@[reassoc]
theorem currentNegativeKComparison_normalizedRow (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison f i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (ParameterTensorNormalizedRowPresentation.supportedComparison f.left (specUnder.obj a)) =
      normalizedRowNegativeClass f i a := by
  have hraw : (currentStageInclusion f i).app (specUnder.obj a) ≫
      ParameterTensorNormalizedRowPresentation.supportedComparison f.left (specUnder.obj a) =
    SchemeModelRowSeed.normalizedStageInclusion (ParameterModels.supported f.left)
      (ParameterLaurentTrack.supportedUnit f.left)
      (ParameterLaurentTrack.supportedUnit_naturality f.left) (specUnder.obj a) i :=
    SchemeModelRowSeed.normalizedComparison_stageInclusion (ParameterModels.supported f.left)
      (ParameterLaurentTrack.supportedUnit f.left)
      (ParameterLaurentTrack.supportedUnit_naturality f.left) (specUnder.obj a) i
  have hr := congrArg (stableHomotopyFunctor (-(i : ℤ))).map hraw
  have h := ((stableHomotopyFunctor (-(i : ℤ))).map_comp _ _).symm.trans hr
  rw [currentNegativeKComparison_hom_app, Category.assoc, h]
  rfl

/-- The independent original negative-class map is an isomorphism in its actual degree. -/
theorem normalizedRowNegativeClass_isIso (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsIso (normalizedRowNegativeClass f i a) := by
  have hs : IsIso ((stableHomotopyFunctor (-(i : ℤ))).map
      (ParameterTensorNormalizedRowPresentation.supportedComparison f.left (specUnder.obj a))) :=
    ParameterTensorNormalizedRowPresentation.supportedComparison_stable f.left
      (specUnder.obj a) (-(i : ℤ))
  have hc : IsIso ((currentNegativeKComparison f i).hom.app a) := inferInstance
  rw [← currentNegativeKComparison_normalizedRow f i a]
  exact IsIso.comp_isIso' hc hs

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
