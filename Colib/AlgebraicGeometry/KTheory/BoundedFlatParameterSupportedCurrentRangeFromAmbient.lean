/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterSupportedCurrentNegativeClass
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeStageInclusionComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedTelescopeFromAmbient

/-! # Stable range of the original supported parameter stage inclusions

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
ParameterSupportedCurrentStageInclusion.lean`, revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSectionChangeIndex.SupportedTelescope
open GlobalSupportedSection
open KTheory.Bass.SchemeNaturalSeed
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

variable
  (hP : ∀ (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ),
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientAmbientBassTransition P 0).app a)))
  (hQ : ∀ (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ),
    IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedAboveFlatCoefficientAmbientBassTransition Q 0).app a)))
  (hBottom : ∀ (a : Under (CommRingCat.of (ULift.{u} ℤ))) (i : ℕ),
    CategoryTheory.Limits.IsZero (KTheory.Bass.TwoChartStable.bassRightGroup
      (modelDiagramTwoChartSquare (boundedAboveFlatCoefficientSupportedModelFunctor f) i a)
      (-(i : ℤ))))

include hP hQ hBottom in
/-- Original global stage inclusions have the exact fine stable range. -/
theorem globalStageInclusion_isIso_of_le_of_two_ambient (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((Telescope.diagramInclusion (globalDiagram f) (globalTransition f) i).app a)) := by
  let H := stableHomotopyFunctor d
  let : IsIso (H.map ((telescopeRestriction f).app a)) :=
    telescopeRestriction_isStableEquivalence f a d
  let : IsIso (H.map ((finiteRestriction f i).app a)) :=
    finiteRestriction_isStableEquivalence f i a d
  let : IsIso (H.map ((boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f i).app a)) :=
    boundedAboveFlatCoefficientSupportedBassTelescopeInclusion_isIso_of_le_of_two_ambient
      f hP hQ hBottom i a d hd
  have h := congrArg H.map (congrArg (fun η => η.app a)
    (telescopeRestriction_inclusion f i))
  simp only [NatTrans.comp_app, Functor.map_comp] at h
  rw [← isIso_comp_right_iff _ (H.map ((telescopeRestriction f).app a)), h]
  infer_instance

include hP hQ hBottom in
/-- The actual iterated parameter inclusion is invertible in every original finite-stage range. -/
theorem iteratedStageInclusion_isIso_of_le_of_two_ambient (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((iteratedStageInclusion f i).app (specUnder.obj a))) := by
  let H := stableHomotopyFunctor d
  let : IsIso (H.map
      ((Telescope.diagramInclusion (globalDiagram f) (globalTransition f) i).app a)) :=
    globalStageInclusion_isIso_of_le_of_two_ambient f hP hQ hBottom i a d hd
  have h := congrArg H.map (iteratedStageInclusion_telescopeIso f i a)
  simp only [Functor.map_comp] at h
  rw [← isIso_comp_right_iff _ (H.map ((telescopeIso f).hom.app a)), h]
  infer_instance

include hP hQ hBottom in
/-- The independent current inclusion is invertible in the same range without erasing its word. -/
theorem currentStageInclusion_isIso_of_le_of_two_ambient (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((currentStageInclusion f i).app (specUnder.obj a))) :=
  (model_currentInclusion_isIso_iff_iteratedInclusion (ParameterModels.supported f.left)
    (ParameterLaurentTrack.supportedTrack f.left) i (specUnder.obj a) d).mpr
      (iteratedStageInclusion_isIso_of_le_of_two_ambient f hP hQ hBottom i a d hd)

include hP hQ hBottom in
/-- The already constructed current class map is invertible in its original bottom degree. -/
theorem currentNegativeClassMap_isIso_of_two_ambient (i : ℕ) :
    IsIso (currentNegativeClassMap f i) := by
  let : ∀ a, IsIso ((currentNegativeClassMap f i).app a) := fun a => by
    rw [currentNegativeClassMap_app]
    let := currentStageInclusion_isIso_of_le_of_two_ambient f hP hQ hBottom i a (-(i : ℤ)) le_rfl
    infer_instance
  exact NatIso.isIso_of_isIso_app _

include hP hQ hBottom in
/-- Original negative groups in the independent current telescope, with the same class map. -/
def currentNegativeKComparison_of_two_ambient (i : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor i ≅
      (specUnder ⋙ currentTelescope (ParameterLaurentTrack.supportedTrack f.left)) ⋙
        stableHomotopyFunctor (-(i : ℤ)) :=
  let := currentNegativeClassMap_isIso_of_two_ambient f hP hQ hBottom i
  asIso (currentNegativeClassMap f i)

include hP hQ hBottom in
/-- The comparison retains the original class map, hence the same Laurent quotient formula. -/
@[simp]
theorem currentNegativeKComparison_of_two_ambient_hom (i : ℕ) :
    (currentNegativeKComparison_of_two_ambient f hP hQ hBottom i).hom =
      currentNegativeClassMap f i := rfl

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
