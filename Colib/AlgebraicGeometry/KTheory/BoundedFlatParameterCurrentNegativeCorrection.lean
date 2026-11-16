/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAmbientCurrentNegativeComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterSupportedCurrentStageRange
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFineTelescopeComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFineTelescope
public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedPairDiagram
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeStageClassComparison

/-! # Original finite negative classes under iterated-to-fine evaluation -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules
open GlobalSectionChangeIndex GlobalSupportedSection KTheory.Bass.SchemeNaturalSeed

private theorem class_inverse_square {C : Type*} [Category C]
    {A B C₁ D E F : C} (x : A ⟶ B) (v : C₁ ⟶ B) (w : D ⟶ C₁)
    [IsIso v] [IsIso w] (j : D ⟶ E) (k : E ⟶ F) (l : B ⟶ F)
    (h : j ≫ k = w ≫ v ≫ l) :
    (x ≫ inv v ≫ inv w) ≫ j ≫ k = x ≫ l := by
  simp only [Category.assoc]
  rw [h, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id_assoc]

namespace GlobalParameterCoefficient
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))

/-- The original iterated inclusion keeps the actual finite comparison to the fine tower. -/
theorem iteratedStageInclusion_fine (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (iteratedStageInclusion P i).app (specUnder.obj a) ≫
        (fineTelescopeComparison P).app a =
      (finiteIso P i).hom.app a ≫ (finiteRestriction P i).app a ≫
        (boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P i).app a := by
  dsimp only [fineTelescopeComparison, NatTrans.comp_app]
  rw [← Category.assoc, iteratedStageInclusion_telescopeIso, Category.assoc]
  exact congrArg (fun t => (finiteIso P i).hom.app a ≫ t)
    (congrArg (fun η => η.app a) (telescopeRestriction_inclusion P i))

variable [CompactSpace P.left] [QuasiSeparatedSpace P.left]

/-- The fixed finite negative class followed by its original iterated inclusion is unchanged. -/
@[reassoc]
theorem finiteNegativeKComparison_iterated_fine (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (finiteNegativeKComparison P i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((iteratedStageInclusion P i).app (specUnder.obj a)) ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison P).app a) =
      (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  let : IsIso (H.map ((finiteRestriction P i).app a)) :=
    finiteRestriction_isStableEquivalence P i a (-(i : ℤ))
  have h := congrArg H.map (iteratedStageInclusion_fine P i a)
  simp only [Functor.map_comp] at h
  have hh := class_inverse_square
    ((boundedAboveFlatCoefficientAmbientNegativeKComparison P i).hom.app a)
    (H.map ((finiteRestriction P i).app a))
    (H.map ((finiteIso P i).hom.app a)) _ _ _ h
  rw [finiteNegativeKComparison_hom_app,
    boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison_hom_app]
  simpa only [← Functor.map_inv, NatIso.inv_hom_app] using hh

/-- The genuine finite-word correction, expressed on the unchanged original negative group. -/
def negativeClassCorrection (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.negativeKFunctor i).obj ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a) ≅
      (Bass.negativeKFunctor i).obj ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a) :=
  (finiteNegativeKComparison P i).app a ≪≫
    finiteStageStableIso (ParameterModels.ambient P.left) i (specUnder.obj a) (-(i : ℤ)) ≪≫
      ((finiteNegativeKComparison P i).app a).symm

/-- The original current class retains its finite correction through the fine comparison. -/
@[reassoc]
theorem currentNegativeKComparison_fine_correction (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison P i).hom.app a ≫
        (currentIteratedStableIso (ParameterModels.ambient P.left)
          (ParameterLaurentTrack.ambientTrack P.left) (specUnder.obj a) (-(i : ℤ))).hom ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison P).app a) =
      (negativeClassCorrection P i a).hom ≫
        (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a := by
  have h := currentIteratedStableIso_inclusion (ParameterModels.ambient P.left)
    (ParameterLaurentTrack.ambientTrack P.left) i (specUnder.obj a) (-(i : ℤ))
  change (stableHomotopyFunctor (-(i : ℤ))).map
      ((currentStageInclusion P i).app (specUnder.obj a)) ≫ _ =
    (finiteStageStableIso (ParameterModels.ambient P.left) i (specUnder.obj a) (-(i : ℤ))).hom ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((iteratedStageInclusion P i).app (specUnder.obj a)) at h
  have hh := congrArg (fun z => (finiteNegativeKComparison P i).hom.app a ≫ z ≫
    (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison P).app a)) h
  rw [← finiteNegativeKComparison_iterated_fine P i a]
  simpa only [currentNegativeKComparison_hom_app, negativeClassCorrection,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app_assoc] using hh

end GlobalParameterCoefficient

namespace GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex.SupportedTelescope
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The original iterated inclusion keeps the actual finite comparison to the fine tower. -/
theorem iteratedStageInclusion_fine (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (iteratedStageInclusion f i).app (specUnder.obj a) ≫
        (fineTelescopeComparison f).app a =
      (finiteIso f i).hom.app a ≫ (SupportedTelescope.finiteRestriction f i).app a ≫
        (boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f i).app a := by
  dsimp only [fineTelescopeComparison, NatTrans.comp_app]
  rw [← Category.assoc, iteratedStageInclusion_telescopeIso, Category.assoc]
  exact congrArg (fun t => (finiteIso f i).hom.app a ≫ t)
    (congrArg (fun η => η.app a) (SupportedTelescope.telescopeRestriction_inclusion f i))

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The fixed finite negative class followed by its original iterated inclusion is unchanged. -/
@[reassoc]
theorem finiteNegativeKComparison_iterated_fine (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (finiteNegativeKComparison f i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((iteratedStageInclusion f i).app (specUnder.obj a)) ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison f).app a) =
      (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison f i).hom.app a := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  let : IsIso (H.map ((SupportedTelescope.finiteRestriction f i).app a)) :=
    SupportedTelescope.finiteRestriction_isStableEquivalence f i a (-(i : ℤ))
  have h := congrArg H.map (iteratedStageInclusion_fine f i a)
  simp only [Functor.map_comp] at h
  have hh := class_inverse_square
    ((boundedAboveFlatCoefficientSupportedNegativeKComparison f i).hom.app a)
    (H.map ((SupportedTelescope.finiteRestriction f i).app a))
    (H.map ((finiteIso f i).hom.app a)) _ _ _ h
  rw [finiteNegativeKComparison_hom_app,
    boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_hom_app]
  simpa only [← Functor.map_inv, NatIso.inv_hom_app] using hh

/-- The genuine finite-word correction, expressed on the unchanged original negative group. -/
def negativeClassCorrection (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.supportedNegativeKFunctor i).obj
      ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) ≅
      (Bass.supportedNegativeKFunctor i).obj
      ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a) :=
  (finiteNegativeKComparison f i).app a ≪≫
    finiteStageStableIso (ParameterModels.supported f.left) i (specUnder.obj a) (-(i : ℤ)) ≪≫
      ((finiteNegativeKComparison f i).app a).symm

/-- The original current class retains its finite correction through the fine comparison. -/
@[reassoc]
theorem currentNegativeKComparison_fine_correction (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison f i).hom.app a ≫
        (currentIteratedStableIso (ParameterModels.supported f.left)
          (ParameterLaurentTrack.supportedTrack f.left) (specUnder.obj a) (-(i : ℤ))).hom ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison f).app a) =
      (negativeClassCorrection f i a).hom ≫
        (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison f i).hom.app a := by
  have h := currentIteratedStableIso_inclusion (ParameterModels.supported f.left)
    (ParameterLaurentTrack.supportedTrack f.left) i (specUnder.obj a) (-(i : ℤ))
  change (stableHomotopyFunctor (-(i : ℤ))).map
      ((currentStageInclusion f i).app (specUnder.obj a)) ≫ _ =
    (finiteStageStableIso (ParameterModels.supported f.left) i
      (specUnder.obj a) (-(i : ℤ))).hom ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((iteratedStageInclusion f i).app (specUnder.obj a)) at h
  have hh := congrArg (fun z => (finiteNegativeKComparison f i).hom.app a ≫ z ≫
    (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison f).app a)) h
  rw [← finiteNegativeKComparison_iterated_fine f i a]
  simpa only [currentNegativeKComparison_hom_app, negativeClassCorrection,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
    Iso.inv_hom_id_app_assoc] using hh

end GlobalSupportedParameterCoefficient

end AlgebraicGeometry.Scheme.Modules
