/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNormalizedRowForget
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterSupportedNormalizedRowClasses
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterCurrentNegativeForget

/-!
# Original negative classes under normalized support forgetting

Ambient classes use the original finite comparison and the independently defined
finite normalized inclusion. The actual support-forgetful map preserves these
classes in every original negative degree, including zero.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Topology.LoopPrespectrum KTheory.Bass CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules
open GlobalSectionChangeIndex GlobalSupportedSection
namespace GlobalParameterCoefficient
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [CompactSpace P.left]

/-- The original ambient finite negative class enters through its actual normalized inclusion. -/
def normalizedRowNegativeClass (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :=
  (finiteNegativeKComparison P i).hom.app a ≫
    (stableHomotopyFunctor (-(i : ℤ))).map
      (SchemeModelRowSeed.normalizedStageInclusion (ParameterModels.ambient P.left)
        (ParameterLaurentUnit.ambientUnit P.left)
        (ParameterLaurentUnit.ambientUnit_naturality P.left) (specUnder.obj a) i)

variable [QuasiSeparatedSpace P.left]

/-- The original current class has precisely its independent normalized finite image. -/
@[reassoc]
theorem currentNegativeKComparison_normalizedRow (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison P i).hom.app a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (ParameterTensorNormalizedRowPresentation.ambientComparison P.left (specUnder.obj a)) =
      normalizedRowNegativeClass P i a := by
  have hraw : (currentStageInclusion P i).app (specUnder.obj a) ≫
      ParameterTensorNormalizedRowPresentation.ambientComparison P.left (specUnder.obj a) =
    SchemeModelRowSeed.normalizedStageInclusion (ParameterModels.ambient P.left)
      (ParameterLaurentUnit.ambientUnit P.left)
      (ParameterLaurentUnit.ambientUnit_naturality P.left) (specUnder.obj a) i :=
    SchemeModelRowSeed.normalizedComparison_stageInclusion
      (ParameterModels.ambient P.left) (ParameterLaurentUnit.ambientUnit P.left)
      (ParameterLaurentUnit.ambientUnit_naturality P.left) (specUnder.obj a) i
  have hr := congrArg (stableHomotopyFunctor (-(i : ℤ))).map hraw
  have h := ((stableHomotopyFunctor (-(i : ℤ))).map_comp _ _).symm.trans hr
  rw [currentNegativeKComparison_hom_app, Category.assoc, h]
  rfl

/-- These original ambient class maps are invertible under the original qcqs hypothesis. -/
theorem normalizedRowNegativeClass_isIso (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsIso (normalizedRowNegativeClass P i a) := by
  have hs := ParameterTensorNormalizedRowPresentation.ambientComparison_stable P.left
    (specUnder.obj a) (-(i : ℤ))
  rw [← currentNegativeKComparison_normalizedRow P i a]
  infer_instance

end GlobalParameterCoefficient
namespace GlobalSupportedParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- Actual normalized support forgetting retains every original negative-group forget map. -/
@[reassoc]
theorem normalizedRowNegativeClass_forget (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.supportedNegativeKForgetNat i).app
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≫
      GlobalParameterCoefficient.normalizedRowNegativeClass Q i a =
    normalizedRowNegativeClass f i a ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        (ParameterTensorNormalizedRowPresentation.forget f.left (specUnder.obj a)) := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  have hraw := SchemeModelRowSeed.normalizedStageInclusion_input
    (ParameterModels.supported f.left) (ParameterLaurentTrack.supportedUnit f.left)
    (ParameterLaurentTrack.supportedUnit_naturality f.left)
    (ParameterModels.ambient Q.left) (ParameterLaurentUnit.ambientUnit Q.left)
    (ParameterLaurentUnit.ambientUnit_naturality Q.left)
    (ParameterModels.forget f.left) (ParameterLaurentTrack.forget_unit f.left)
    (specUnder.obj a) i
  have h := congrArg H.map hraw
  simp only [Functor.map_comp] at h
  unfold GlobalParameterCoefficient.normalizedRowNegativeClass normalizedRowNegativeClass
  rw [← Category.assoc, finiteNegativeKComparison_forget, Category.assoc]
  exact congrArg (fun k => (finiteNegativeKComparison f i).hom.app a ≫ k) h.symm

end GlobalSupportedParameterCoefficient
end AlgebraicGeometry.Scheme.Modules
