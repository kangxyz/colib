/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBottomChartExactness
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterSupportedCurrentRangeFromAmbient
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientConnectiveInvertibility

/-!
# The original supported Bass groups in the current parameter telescope

The class map into the independently defined current telescope is invertible in
the original finite-bottom degree. It retains the original Laurent quotient.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
ParameterSupportedCurrentNegativeComparison.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum
open CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open KTheory.Bass.SchemeNaturalSeed

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSectionChangeIndex.SupportedTelescope

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The actual current stage inclusion is invertible throughout its finite-stage range. -/
theorem currentStageInclusion_isIso_of_le (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((currentStageInclusion f i).app (specUnder.obj a))) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  exact currentStageInclusion_isIso_of_le_of_two_ambient f
    (fun a n => boundedAboveFlatCoefficientAmbientBassTransition_zero_isIso P a n)
    (fun a n => boundedAboveFlatCoefficientAmbientBassTransition_zero_isIso Q a n)
    (fun a i => boundedAboveFlatCoefficientSupportedBottomBassRight_isZero f a i) i a d hd

/-- The original supported negative groups are naturally the stable groups of the actual
current telescope. -/
def currentNegativeKComparison (i : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor i ≅
      (specUnder ⋙ currentTelescope (ParameterLaurentTrack.supportedTrack f.left)) ⋙
        stableHomotopyFunctor (-(i : ℤ)) := by
  let : QuasiSeparatedSpace P.left := f.left.isOpenEmbedding.quasiSeparatedSpace
  exact currentNegativeKComparison_of_two_ambient f
    (fun a n => boundedAboveFlatCoefficientAmbientBassTransition_zero_isIso P a n)
    (fun a n => boundedAboveFlatCoefficientAmbientBassTransition_zero_isIso Q a n)
    (fun a i => boundedAboveFlatCoefficientSupportedBottomBassRight_isZero f a i) i

/-- The comparison retains the original class map and its Laurent quotient formula. -/
@[simp]
theorem currentNegativeKComparison_hom (i : ℕ) :
    (currentNegativeKComparison f i).hom = currentNegativeClassMap f i := rfl

/-- The current class is the original finite class followed by the literal current inclusion. -/
theorem currentNegativeKComparison_hom_app (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison f i).hom.app a =
      (finiteNegativeKComparison f i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((currentStageInclusion f i).app (specUnder.obj a)) := rfl

/-- The original Laurent quotient formula is preserved before entering the current telescope. -/
@[reassoc]
theorem currentNegativeKComparison_π (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.supportedNegativeKFunctor i).map
        ((boundedAboveFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop i ≫
        (currentNegativeKComparison f (i + 1)).hom.app a =
    (boundedAboveFlatCoefficientSupportedNegativeKComparison f i).hom.app
        ((laurentUnderFunctor _).obj a) ≫
      (KTheory.Bass.TwoChart.contractionπ (underToLaurent _) (underToLaurentInvert _)
        (boundedAboveFlatCoefficientSupportedBassDiagram f i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
      (boundedAboveFlatCoefficientSupportedBassBottomContractionIso f i).hom.app a ≫
      inv (I := finiteRestriction_isStableEquivalence f (i + 1) a (-((i + 1 : ℕ) : ℤ)))
        ((stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
          ((finiteRestriction f (i + 1)).app a)) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map ((finiteIso f (i + 1)).inv.app a) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((currentStageInclusion f (i + 1)).app (specUnder.obj a)) := by
  simpa only [currentNegativeKComparison_hom] using currentNegativeClassMap_π f i a

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
