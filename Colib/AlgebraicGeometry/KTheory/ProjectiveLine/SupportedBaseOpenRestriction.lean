/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.BaseOpenRestriction
public import Colib.AlgebraicGeometry.KTheory.PerfectSupportedOpenMaps

/-! # Restriction of supported projective-line summands to a base open

The comparisons are on the actual supported full subcategories. The first
uses the equality of the two projection composites; the second also uses
the canonical pullback isomorphism for the negative line.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Waldhausen AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

universe u

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T : X.Opens)

local notation "J" => projectiveSpaceOverMap 1 j
local notation "P" => projectiveSpaceOver 1 X
local notation "Q" => projectiveSpaceOver 1 V
local notation "Tₚ" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom (P ↘ X))))) T
local notation "U" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) T
local notation "Uₚ" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom (Q ↘ V))))) U

local notation "B" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom J)))) Tₚ

/-- Changing the spelling of the same support open changes neither complexes nor maps. -/
def supportedOpenCongr {Y : Scheme.{u}} {A D : Y.Opens} (h : A = D) :
    (perfectSupported A.ι).FullSubcategory ⥤ (perfectSupported D.ι).FullSubcategory := by
  subst D
  exact 𝟭 _

/-- The transport of a support equality is exact. -/
theorem supportedOpenCongr_exact {Y : Scheme.{u}} {A D : Y.Opens} (h : A = D) :
    IsExact (perfectSupportedWaldhausen A.ι).cof (perfectSupportedWaldhausen A.ι).weq
      (perfectSupportedWaldhausen D.ι).cof (perfectSupportedWaldhausen D.ι).weq
      (supportedOpenCongr h) := by
  subst D
  exact IsExact.id _ _

/-- The transport identifies the original underlying perfect complexes by the identity. -/
def supportedOpenCongr_forgetIso {Y : Scheme.{u}} {A D : Y.Opens} (h : A = D) :
    supportedOpenCongr h ⋙ (perfectSupported D.ι).ι ≅ (perfectSupported A.ι).ι := by
  subst D
  exact Functor.leftUnitor _

/-- The actual supported first summand and its base-open restriction commute. -/
def projectiveLineSupportedFirstSummand_baseOpenRestrictIso :
    projectiveLineSupportedFirstSummand X T ⋙ perfectSupportedRestrict J Tₚ ≅
      (perfectSupportedRestrict j T ⋙ projectiveLineSupportedFirstSummand V U) ⋙
        supportedOpenCongr (projectiveLine_preimage_preimage j T).symm := by
  let h := (projectiveLine_preimage_preimage j T).symm
  let e := projectiveLineFirstSummand_baseOpenRestrictIso j
  refine Functor.fullyFaithfulCancelRight ((perfectSupported (Scheme.Opens.ι B)).ι) ?_
  let H : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := (Q).toRingedSpace)) ⥤
      CochainComplex (Q).Modules ℤ := ObjectProperty.ι _
  let I : (perfectSupported T.ι).FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
    perfectSupportedInclusion T.ι
  let e' : I ⋙ (projectiveLineFirstSummand X ⋙ perfectComplexesRestrictOpenImmersion J) ≅
      I ⋙ (perfectComplexesRestrictOpenImmersion j ⋙ projectiveLineFirstSummand V) :=
    Functor.isoWhiskerLeft I e
  exact Functor.isoWhiskerRight e' H ≪≫
    (Functor.isoWhiskerLeft
      (perfectSupportedRestrict j T ⋙ projectiveLineSupportedFirstSummand V U)
      (supportedOpenCongr_forgetIso h)).symm

/-- The actual supported twisted summand and its base-open restriction commute. -/
def projectiveLineSupportedSecondSummand_baseOpenRestrictIso :
    projectiveLineSupportedSecondSummand X T ⋙ perfectSupportedRestrict J Tₚ ≅
      (perfectSupportedRestrict j T ⋙ projectiveLineSupportedSecondSummand V U) ⋙
        supportedOpenCongr (projectiveLine_preimage_preimage j T).symm := by
  let h := (projectiveLine_preimage_preimage j T).symm
  let e := projectiveLineSecondSummand_baseOpenRestrictIso j
  refine Functor.fullyFaithfulCancelRight ((perfectSupported (Scheme.Opens.ι B)).ι) ?_
  let H : ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := (Q).toRingedSpace)) ⥤
      CochainComplex (Q).Modules ℤ := ObjectProperty.ι _
  let I : (perfectSupported T.ι).FullSubcategory ⥤
      ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
    perfectSupportedInclusion T.ι
  let e' : I ⋙ (projectiveLineSecondSummand X ⋙ perfectComplexesRestrictOpenImmersion J) ≅
      I ⋙ (perfectComplexesRestrictOpenImmersion j ⋙ projectiveLineSecondSummand V) :=
    Functor.isoWhiskerLeft I e
  exact Functor.isoWhiskerRight e' H ≪≫
    (Functor.isoWhiskerLeft
      (perfectSupportedRestrict j T ⋙ projectiveLineSupportedSecondSummand V U)
      (supportedOpenCongr_forgetIso h)).symm

end AlgebraicGeometry.Scheme
