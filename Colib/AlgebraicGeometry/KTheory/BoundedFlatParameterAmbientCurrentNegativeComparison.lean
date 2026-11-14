/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAmbientCurrentStageInclusion
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassOriginalNegativeComparison

/-!
# Original negative classes in the current parameter telescope

The original finite-bottom comparison is transported by the actual finite
section restriction and integral Spec-row isomorphism, then followed by the
independent current-stage inclusion. These maps are natural in coefficient
arrows. Their invertibility uses the proved current inclusion range, not an
inverse telescope comparison. The original Laurent quotient formula is retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSectionChangeIndex SchemeNaturalSeed GlobalSupportedSection
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [CompactSpace P.left]

/-- Original finite-bottom classes in the actual parameter finite stage. -/
def finiteNegativeKComparison (i : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i ≅
      (specUnder ⋙ (strictDiagramIterate squareFunctor i).obj (parameterDiagram P)) ⋙
        stableHomotopyFunctor (-(i : ℤ)) := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  let v := Functor.whiskerRight (finiteRestriction P i) H
  let : ∀ a, IsIso (v.app a) := fun a =>
    finiteRestriction_isStableEquivalence P i a (-(i : ℤ))
  let : IsIso v := NatIso.isIso_of_isIso_app v
  exact boundedAboveFlatCoefficientAmbientNegativeKComparison P i ≪≫
    (asIso v).symm ≪≫ (Functor.isoWhiskerRight (finiteIso P i) H).symm

/-- The finite comparison retains the original bottom map and both actual inverse maps. -/
theorem finiteNegativeKComparison_hom_app (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (finiteNegativeKComparison P i).hom.app a =
      (boundedAboveFlatCoefficientAmbientNegativeKComparison P i).hom.app a ≫
        inv (I := finiteRestriction_isStableEquivalence P i a (-(i : ℤ)))
          ((stableHomotopyFunctor (-(i : ℤ))).map ((finiteRestriction P i).app a)) ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((finiteIso P i).inv.app a) := by
  simp only [finiteNegativeKComparison, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    NatTrans.comp_app, NatIso.isIso_inv_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app]

variable [QuasiSeparatedSpace P.left]

/-- Original negative groups, including degree zero, in the independent current telescope. -/
def currentNegativeKComparison (i : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i ≅
      (specUnder ⋙ currentTelescope (ParameterLaurentTrack.ambientTrack P.left)) ⋙
        stableHomotopyFunctor (-(i : ℤ)) := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  let j := Functor.whiskerRight (Functor.whiskerLeft specUnder (currentStageInclusion P i)) H
  let : ∀ a, IsIso (j.app a) := fun a =>
    currentStageInclusion_isIso_of_le P i a (-(i : ℤ)) le_rfl
  let : IsIso j := NatIso.isIso_of_isIso_app j
  exact finiteNegativeKComparison P i ≪≫ asIso j

/-- The current class is the original finite class followed by the literal current inclusion. -/
theorem currentNegativeKComparison_hom_app (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison P i).hom.app a =
      (finiteNegativeKComparison P i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((currentStageInclusion P i).app (specUnder.obj a)) := rfl

/-- The original Laurent quotient formula is preserved before entering the current telescope. -/
@[reassoc]
theorem currentNegativeKComparison_π (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (Bass.negativeKFunctor i).map ((boundedAboveFlatCoefficientLaurentIso P).hom.app a) ≫
      Bass.negativeKπ ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a).unop i ≫
        (currentNegativeKComparison P (i + 1)).hom.app a =
    (boundedAboveFlatCoefficientAmbientNegativeKComparison P i).hom.app
        ((laurentUnderFunctor _).obj a) ≫
      (KTheory.Bass.TwoChart.contractionπ (underToLaurent _) (underToLaurentInvert _)
        (boundedAboveFlatCoefficientAmbientBassDiagram P i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
      (boundedAboveFlatCoefficientAmbientBassBottomContractionIso P i).hom.app a ≫
      inv (I := finiteRestriction_isStableEquivalence P (i + 1) a (-((i + 1 : ℕ) : ℤ)))
        ((stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
          ((finiteRestriction P (i + 1)).app a)) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map ((finiteIso P (i + 1)).inv.app a) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((currentStageInclusion P (i + 1)).app (specUnder.obj a)) := by
  rw [currentNegativeKComparison_hom_app, finiteNegativeKComparison_hom_app]
  simpa only [Category.assoc] using
    (boundedAboveFlatCoefficientAmbientNegativeKComparison_π P i a) =≫
      (inv (I := finiteRestriction_isStableEquivalence P (i + 1) a (-((i + 1 : ℕ) : ℤ)))
        ((stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
          ((finiteRestriction P (i + 1)).app a)) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map ((finiteIso P (i + 1)).inv.app a) ≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((currentStageInclusion P (i + 1)).app (specUnder.obj a)))

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
