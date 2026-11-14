/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterSupportedCurrentStageInclusion
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedNegativeBottomComparison

/-!
# Original supported negative classes in the current parameter telescope

The original finite-bottom comparison, finite restriction and integral Spec-row isomorphism
give the actual current class map and its Laurent representative. This file does not assert
that the current class map is invertible.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
  ParameterSupportedCurrentNegativeComparison.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex GlobalSectionChangeIndex.SupportedTelescope SchemeNaturalSeed
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- Original finite-bottom classes in the actual parameter finite stage. -/
def finiteNegativeKComparison (i : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor i ≅
      (specUnder ⋙ (strictDiagramIterate squareFunctor i).obj (parameterDiagram f)) ⋙
        stableHomotopyFunctor (-(i : ℤ)) := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  let v := Functor.whiskerRight (finiteRestriction f i) H
  let : ∀ a, IsIso (v.app a) := fun a =>
    finiteRestriction_isStableEquivalence f i a (-(i : ℤ))
  let : IsIso v := NatIso.isIso_of_isIso_app v
  exact boundedAboveFlatCoefficientSupportedNegativeKComparison f i ≪≫
    (asIso v).symm ≪≫ (Functor.isoWhiskerRight (finiteIso f i) H).symm

/-- The finite comparison retains the original bottom map and both actual inverse maps. -/
theorem finiteNegativeKComparison_hom_app (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (finiteNegativeKComparison f i).hom.app a =
      (boundedAboveFlatCoefficientSupportedNegativeKComparison f i).hom.app a ≫
        inv (I := finiteRestriction_isStableEquivalence f i a (-(i : ℤ)))
          ((stableHomotopyFunctor (-(i : ℤ))).map ((finiteRestriction f i).app a)) ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((finiteIso f i).inv.app a) := by
  simp only [finiteNegativeKComparison, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    NatTrans.comp_app, NatIso.isIso_inv_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app]

/-- The actual current class, before proving the inclusion is invertible in this degree. -/
def currentNegativeClassMap (i : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor i ⟶
      (specUnder ⋙ currentTelescope (ParameterLaurentTrack.supportedTrack f.left)) ⋙
        stableHomotopyFunctor (-(i : ℤ)) :=
  (finiteNegativeKComparison f i).hom ≫
    Functor.whiskerRight (Functor.whiskerLeft specUnder (currentStageInclusion f i)) _

/-- The current class is the finite class followed by the literal current inclusion. -/
theorem currentNegativeClassMap_app (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeClassMap f i).app a =
      (finiteNegativeKComparison f i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((currentStageInclusion f i).app (specUnder.obj a)) := rfl

/-- The original Laurent quotient formula is preserved before entering the current telescope. -/
@[reassoc]
theorem currentNegativeClassMap_π (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.supportedNegativeKFunctor i).map
        ((boundedAboveFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop i ≫
        (currentNegativeClassMap f (i + 1)).app a =
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
  rw [currentNegativeClassMap_app, finiteNegativeKComparison_hom_app]
  simpa only [Category.assoc] using
    (boundedAboveFlatCoefficientSupportedNegativeKComparison_π f i a) =≫
      (inv (I := finiteRestriction_isStableEquivalence f (i + 1) a (-((i + 1 : ℕ) : ℤ)))
        ((stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
          ((finiteRestriction f (i + 1)).app a)) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map ((finiteIso f (i + 1)).inv.app a) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((currentStageInclusion f (i + 1)).app (specUnder.obj a)))

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedParameterCoefficient
