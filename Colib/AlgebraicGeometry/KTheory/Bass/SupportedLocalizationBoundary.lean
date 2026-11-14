/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientNegativeLocalizationBoundary
public import Colib.AlgebraicGeometry.KTheory.Bass.SupportedForget

/-!
# The negative localization sequence of the original open pair

The fixed signed fine boundary is transported through the actual identity-base
projection on both legs of the open pair. It sends the original open group in
degree `-i` to the original supported group in degree `-(i+1)`. Both adjacent
positions are exact for the original restriction and forget maps. At `i = 0`
this extends the original K₀ tail, without imposing surjectivity of restriction.
The positive geometric boundary is not identified with the fine boundary here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Bass
open AlgebraicGeometry.Scheme.Modules
variable (A : QuasiCompactOpenPairs.{u}) [CompactSpace A.obj.left]

namespace SupportedLocalization

/-- The removed open over the canonical integral base. -/
abbrev localizationSource : Over (Spec (.of (ULift.{u} ℤ))) :=
  Over.mk (specULiftZIsTerminal.from A.obj.left)

/-- The ambient scheme over the canonical integral base. -/
abbrev localizationTarget : Over (Spec (.of (ULift.{u} ℤ))) :=
  Over.mk (specULiftZIsTerminal.from A.obj.right)

/-- The original open arrow over the canonical integral base. -/
def localizationMap : localizationSource A ⟶ localizationTarget A :=
  Over.homMk A.obj.hom (specULiftZIsTerminal.hom_ext _ _)

local instance localizationSourceCompact : CompactSpace (localizationSource A).left :=
  inferInstanceAs (CompactSpace A.obj.left)

local instance localizationTargetCompact : CompactSpace (localizationTarget A).left :=
  A.property

local instance localizationMapOpen : IsOpenImmersion (localizationMap A).left := A.obj.prop

/-- The identity algebra over the integral base. -/
abbrev identityCoefficient : Under (CommRingCat.of (ULift.{u} ℤ)) :=
  Under.mk (𝟙 _)

/-- Both actual identity projections form an isomorphism of the original open pairs. -/
def identityPairIso :
    ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow (localizationMap A)).obj
      identityCoefficient).unop ≅ A :=
  quasiCompactOpenPairProperty.isoMk (MorphismProperty.Arrow.isoMk
      (identityProjectionIso (localizationSource A))
      (identityProjectionIso (localizationTarget A))
      (identityProjectionIso_schemeMap (localizationMap A)).symm)

/-- The actual identity projection on the compact removed open. -/
def identityOpenIso :
    ((boundedAboveFlatCoefficientQuasiCompactRow (localizationSource A)).obj
      identityCoefficient).unop ≅
        (⟨A.obj.left, inferInstanceAs (CompactSpace A.obj.left)⟩ : QuasiCompactSchemes.{u}) :=
  ObjectProperty.isoMk quasiCompactScheme (identityProjectionIso (localizationSource A))

/-- Original supported groups map along the inverse-direction identity projection square. -/
def identitySupportGroupIso (i : ℕ) :=
  (supportedNegativeKFunctor i).mapIso (identityPairIso A).op

/-- Original ambient groups map along the identity projection. -/
def identityAmbientGroupIso (i : ℕ) :=
  (negativeKFunctor i).mapIso (quasiCompactOpenPairsBase.mapIso (identityPairIso A)).op

/-- Original open groups map along the identity projection. -/
def identityOpenGroupIso (i : ℕ) :=
  (negativeKFunctor i).mapIso (identityOpenIso A).op

omit [CompactSpace A.obj.left] in
/-- The original support forget map retains the identity projection square. -/
theorem identityForget_square (i : ℕ) :
    (supportedNegativeKForgetNat i).app (op A) ≫ (identityAmbientGroupIso A i).hom =
      (identitySupportGroupIso A i).hom ≫
        (supportedNegativeKForgetNat i).app
          ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow (localizationMap A)).obj
            identityCoefficient) :=
  ((supportedNegativeKForgetNat i).naturality (identityPairIso A).hom.op).symm

/-- The original restriction map retains both identity projection legs. -/
theorem identityRestriction_square (i : ℕ) :
    (negativeKFunctor i).map (ObjectProperty.homMk A.obj.hom :
        (⟨A.obj.left, inferInstanceAs (CompactSpace A.obj.left)⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A).op ≫ (identityOpenGroupIso A i).hom =
      (identityAmbientGroupIso A i).hom ≫
        (boundedAboveFlatCoefficientOriginalNegativeKRestriction (localizationMap A) i).app
          identityCoefficient := by
  have hg : (ObjectProperty.homMk (schemeMap (localizationMap A) identityCoefficient) :
      ((boundedAboveFlatCoefficientQuasiCompactRow (localizationSource A)).obj
        identityCoefficient).unop ⟶
      ((boundedAboveFlatCoefficientQuasiCompactRow (localizationTarget A)).obj
        identityCoefficient).unop) ≫ quasiCompactOpenPairsBase.map (identityPairIso A).hom =
      (identityOpenIso A).hom ≫ (ObjectProperty.homMk A.obj.hom :
        (⟨A.obj.left, inferInstanceAs (CompactSpace A.obj.left)⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) := by
    apply ObjectProperty.hom_ext
    change schemeMap (localizationMap A) identityCoefficient ≫
      (identityProjectionIso (localizationTarget A)).hom =
        (identityProjectionIso (localizationSource A)).hom ≫ A.obj.hom
    exact identityProjectionIso_schemeMap (localizationMap A)
  change (negativeKFunctor i).map _ ≫ (negativeKFunctor i).map _ =
    (negativeKFunctor i).map _ ≫ (negativeKFunctor i).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (negativeKFunctor i).map (congrArg Quiver.Hom.op hg.symm)

end SupportedLocalization
open SupportedLocalization

variable [QuasiSeparatedSpace A.obj.right]

local instance supportedLocalizationTargetQuasiSeparated :
    QuasiSeparatedSpace (localizationTarget A).left :=
  inferInstanceAs (QuasiSeparatedSpace A.obj.right)

attribute [local instance] SupportedLocalization.localizationSourceCompact
  SupportedLocalization.localizationTargetCompact SupportedLocalization.localizationMapOpen

/-- The fixed fine signed boundary on the original groups of the actual open pair. -/
def supportedNegativeLocalizationConnecting (i : ℕ) :
    negativeK
      (⟨A.obj.left, inferInstanceAs (CompactSpace A.obj.left)⟩ : QuasiCompactSchemes.{u}) i ⟶
      supportedNegativeK A (i + 1) :=
  (identityOpenGroupIso A i).hom ≫
    boundedAboveFlatCoefficientNegativeLocalizationConnecting (localizationMap A) i
      identityCoefficient ≫ (identitySupportGroupIso A (i + 1)).inv

/-- Restriction to the original open is exact before the fixed signed negative boundary. -/
theorem supportedNegativeLocalizationConnecting_exact_open (i : ℕ) :
    Function.Exact
      ((negativeKFunctor i).map (ObjectProperty.homMk A.obj.hom :
        (⟨A.obj.left, inferInstanceAs (CompactSpace A.obj.left)⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A).op)
      (supportedNegativeLocalizationConnecting A i) := by
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (identityAmbientGroupIso A i).addCommGroupIsoToAddEquiv
    (identityOpenGroupIso A i).addCommGroupIsoToAddEquiv
    (identitySupportGroupIso A (i + 1)).addCommGroupIsoToAddEquiv
    (H := boundedAboveFlatCoefficientNegativeLocalizationConnecting_exact_open
      (localizationMap A) i identityCoefficient)
  · ext x
    exact (ConcreteCategory.congr_hom (identityRestriction_square A i) x).symm
  · ext x
    change _ = (identitySupportGroupIso A (i + 1)).hom
      (supportedNegativeLocalizationConnecting A i x)
    simp [supportedNegativeLocalizationConnecting]

/-- The original support-forgetting map is exact after the fixed signed negative boundary. -/
theorem supportedNegativeLocalizationConnecting_exact_supported (i : ℕ) :
    Function.Exact (supportedNegativeLocalizationConnecting A i)
      ((supportedNegativeKForgetNat (i + 1)).app (op A)) := by
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (identityOpenGroupIso A i).addCommGroupIsoToAddEquiv
    (identitySupportGroupIso A (i + 1)).addCommGroupIsoToAddEquiv
    (identityAmbientGroupIso A (i + 1)).addCommGroupIsoToAddEquiv
    (H := boundedAboveFlatCoefficientNegativeLocalizationConnecting_exact_supported
      (localizationMap A) i identityCoefficient)
  · ext x
    change _ = (identitySupportGroupIso A (i + 1)).hom
      (supportedNegativeLocalizationConnecting A i x)
    simp [supportedNegativeLocalizationConnecting]
  · ext x
    exact (ConcreteCategory.congr_hom (identityForget_square A (i + 1)) x).symm

/-- All recurring positions of the original nonpositive localization sequence are exact. -/
theorem supportedNegativeLocalizationLongExactSequence (i : ℕ) :
    Function.Exact
      ((negativeKFunctor i).map (ObjectProperty.homMk A.obj.hom :
        (⟨A.obj.left, inferInstanceAs (CompactSpace A.obj.left)⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A).op)
      (supportedNegativeLocalizationConnecting A i) ∧
    Function.Exact (supportedNegativeLocalizationConnecting A i)
      ((supportedNegativeKForgetNat (i + 1)).app (op A)) ∧
    Function.Exact ((supportedNegativeKForgetNat (i + 1)).app (op A))
      (negativeKPullback (ObjectProperty.homMk A.obj.hom :
        (⟨A.obj.left, inferInstanceAs (CompactSpace A.obj.left)⟩ : QuasiCompactSchemes.{u}) ⟶
          quasiCompactOpenPairsBase.obj A) (i + 1)) :=
  ⟨supportedNegativeLocalizationConnecting_exact_open A i,
    supportedNegativeLocalizationConnecting_exact_supported A i, by
      apply Function.Exact.of_ladder_addEquiv_of_exact'
        (identitySupportGroupIso A (i + 1)).addCommGroupIsoToAddEquiv
        (identityAmbientGroupIso A (i + 1)).addCommGroupIsoToAddEquiv
        (identityOpenGroupIso A (i + 1)).addCommGroupIsoToAddEquiv
        (H := boundedAboveFlatCoefficientSupportedNegativeK_localization_exact
          (localizationMap A) (i + 1) identityCoefficient)
      · ext x
        exact (ConcreteCategory.congr_hom (identityForget_square A (i + 1)) x).symm
      · ext x
        exact (ConcreteCategory.congr_hom (identityRestriction_square A (i + 1)) x).symm⟩

end AlgebraicGeometry.Scheme.Bass
