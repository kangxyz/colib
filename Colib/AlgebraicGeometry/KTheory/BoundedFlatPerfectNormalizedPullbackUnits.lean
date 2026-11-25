/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumComposition
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackLaws
public import Colib.KTheory.Waldhausen.Iterated.NormalizationCompositionHomotopy

/-! # Unit triangles of the canonically normalized geometric pullback

Both actual geometric pullback units survive the chosen-zero normalization used in the
original prespectrum map. The two normalized routes retain their separate binary composition
and unit transformations, and their composites agree before realization.

Implementation provenance: Quillen `BoundedFlat/NormalizedPullbackCoherence.lean:22-69`,
`BoundedFlat/NormalizedUnitCoherence.lean:22-94` and `BoundedFlat/NormalizedUnitRoutes.lean:71-109`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native bounded-above-flat categories and
pullback functors are unchanged.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The exact chosen-zero normalization used by the original bounded-flat prespectrum map. -/
def boundedAboveFlatPerfectNormalizedPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  CategoryTheory.rebaseFunctor (boundedAboveFlatPerfectPullback f)
    (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).zero
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).zero
    (((boundedAboveFlatPerfectPullback_isExact f).zero
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).isZero).iso
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero)

/-- The actual normalized pullback remains exact for the original Waldhausen structures. -/
theorem boundedAboveFlatPerfectNormalizedPullback_exact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsExact (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).weq
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (boundedAboveFlatPerfectNormalizedPullback f) :=
  (boundedAboveFlatPerfectPullback_isExact f).rebase

/-- Canonical normalization preserves the exact chosen zero on the nose. -/
@[simp] theorem boundedAboveFlatPerfectNormalizedPullback_obj_zero {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (boundedAboveFlatPerfectNormalizedPullback f).obj
        (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).zero =
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).zero :=
  CategoryTheory.rebaseFunctor_obj_base _ _ _ _

/-- The unchanged canonical isomorphism from original to normalized geometric pullback. -/
def boundedAboveFlatPerfectPullbackNormalizationIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedAboveFlatPerfectPullback f ≅ boundedAboveFlatPerfectNormalizedPullback f :=
  CategoryTheory.rebaseFunctorIso _ _ _ _

/-- The actual geometric composition iso followed by the original binary normalizations. -/
def boundedAboveFlatPerfectNormalizedPullbackCompIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedAboveFlatPerfectNormalizedPullback (f ≫ g) ≅
      boundedAboveFlatPerfectNormalizedPullback g ⋙ boundedAboveFlatPerfectNormalizedPullback f :=
  (boundedAboveFlatPerfectPullbackNormalizationIso (f ≫ g)).symm ≪≫
    boundedAboveFlatPerfectPullbackCompIso f g ≪≫
    isoWhiskerRight (boundedAboveFlatPerfectPullbackNormalizationIso g)
      (boundedAboveFlatPerfectPullback f) ≪≫
    isoWhiskerLeft _ (boundedAboveFlatPerfectPullbackNormalizationIso f)

/-- This is precisely the composite of the two original transformations in the geometric
prespectrum composition track, with the intermediate normalization canceled. -/
theorem boundedAboveFlatPerfectNormalizedPullbackCompIso_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (boundedAboveFlatPerfectNormalizedPullbackCompIso f g).hom =
      normalizedWeakTransformation (boundedAboveFlatPerfectPullback_isExact (f ≫ g))
        ((boundedAboveFlatPerfectPullback_isExact g).comp
          (boundedAboveFlatPerfectPullback_isExact f))
        (boundedAboveFlatPerfectPullbackCompIso f g).hom ≫
      (exactNormalizationCompIso (boundedAboveFlatPerfectPullback_isExact g)
        (boundedAboveFlatPerfectPullback_isExact f)).hom := by
  simp [boundedAboveFlatPerfectNormalizedPullbackCompIso,
    boundedAboveFlatPerfectPullbackNormalizationIso, normalizedWeakTransformation,
    exactNormalizationCompIso, Category.assoc]
  rfl

/-- The geometric unit with exactly the normalization used by the original map. -/
def boundedAboveFlatPerfectNormalizedPullbackIdIso (X : Scheme.{u}) :
    boundedAboveFlatPerfectNormalizedPullback (𝟙 X) ≅
      𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  (boundedAboveFlatPerfectPullbackNormalizationIso (𝟙 X)).symm ≪≫
    boundedAboveFlatPerfectPullbackIdIso X

/-- The two transformations in the original identity track compose to this unit. -/
theorem boundedAboveFlatPerfectNormalizedPullbackIdIso_hom (X : Scheme.{u}) :
    (boundedAboveFlatPerfectNormalizedPullbackIdIso X).hom =
      normalizedWeakTransformation (boundedAboveFlatPerfectPullback_isExact (𝟙 X))
        (IsExact.id _ _) (boundedAboveFlatPerfectPullbackIdIso X).hom ≫
      (CategoryTheory.rebaseFunctorIso
        (𝟭 (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory)
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).zero
        (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).zero
        (((IsExact.id (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
          (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq).zero
            (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero).iso
          (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).isZero)).inv := by
  simp [boundedAboveFlatPerfectNormalizedPullbackIdIso,
    boundedAboveFlatPerfectPullbackNormalizationIso, normalizedWeakTransformation,
    Category.assoc]

private theorem normalization_transport {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g) :
    (boundedAboveFlatPerfectPullbackNormalizationIso f).inv ≫
      eqToHom (congrArg boundedAboveFlatPerfectPullback e) ≫
      (boundedAboveFlatPerfectPullbackNormalizationIso g).hom =
        eqToHom (congrArg boundedAboveFlatPerfectNormalizedPullback e) := by
  subst g
  simp

set_option maxHeartbeats 900000 in
-- Reassociating the component compares the native rebased functor and the raw pullback.
/-- The actual right factor unit survives chosen-zero normalization. -/
theorem boundedAboveFlatPerfectNormalizedPullbackCompIso_right_unitality {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (boundedAboveFlatPerfectNormalizedPullbackCompIso (𝟙 X) f).hom ≫
      whiskerLeft (boundedAboveFlatPerfectNormalizedPullback f)
        (boundedAboveFlatPerfectNormalizedPullbackIdIso X).hom ≫
      (Functor.rightUnitor _).hom =
        eqToHom (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.id_comp f)) := by
  apply NatTrans.ext
  funext A
  simp only [boundedAboveFlatPerfectNormalizedPullbackCompIso,
    boundedAboveFlatPerfectNormalizedPullbackIdIso,
    Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, rightUnitor_hom_app,
    Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [(boundedAboveFlatPerfectPullbackIdIso X).hom.naturality_assoc]
  simp only [Functor.id_map]
  have h := congrArg (fun e ↦ e.app A) (boundedAboveFlatPerfectPullbackCompIso_right_unitality f)
  simp only [NatTrans.comp_app, whiskerLeft_app, rightUnitor_hom_app] at h
  erw [Category.comp_id
    ((boundedAboveFlatPerfectPullbackIdIso X).hom.app
      ((boundedAboveFlatPerfectPullback f).obj A))] at h
  erw [Category.comp_id ((boundedAboveFlatPerfectPullbackNormalizationIso f).hom.app A)]
  let rebasing := (boundedAboveFlatPerfectPullbackNormalizationIso f).hom.app A
  erw [← Category.assoc _ _ rebasing]
  erw [h]
  simpa only [NatTrans.comp_app] using
    congrArg (fun k ↦ k.app A) (normalization_transport (Category.id_comp f))

/-- The actual left factor unit survives chosen-zero normalization. -/
theorem boundedAboveFlatPerfectNormalizedPullbackCompIso_left_unitality {X Y : Scheme.{u}}
    (f : X ⟶ Y) :
    (boundedAboveFlatPerfectNormalizedPullbackCompIso f (𝟙 Y)).hom ≫
      whiskerRight (boundedAboveFlatPerfectNormalizedPullbackIdIso Y).hom
        (boundedAboveFlatPerfectNormalizedPullback f) ≫
      (Functor.leftUnitor _).hom =
        eqToHom (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.comp_id f)) := by
  apply NatTrans.ext
  funext A
  simp only [boundedAboveFlatPerfectNormalizedPullbackCompIso,
    boundedAboveFlatPerfectNormalizedPullbackIdIso,
    Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, leftUnitor_hom_app,
    Functor.comp_obj, Category.assoc, Functor.map_comp]
  rw [← (boundedAboveFlatPerfectPullbackNormalizationIso f).hom.naturality_assoc,
    ← (boundedAboveFlatPerfectPullbackNormalizationIso f).hom.naturality_assoc]
  erw [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have h := congrArg (fun e ↦ e.app A) (boundedAboveFlatPerfectPullbackCompIso_left_unitality f)
  simp only [NatTrans.comp_app, whiskerRight_app, leftUnitor_hom_app] at h
  erw [Category.comp_id ((boundedAboveFlatPerfectPullback f).map
    ((boundedAboveFlatPerfectPullbackIdIso Y).hom.app A))] at h
  erw [Category.comp_id ((boundedAboveFlatPerfectPullbackNormalizationIso f).hom.app A)]
  erw [← Category.assoc _ _ ((boundedAboveFlatPerfectPullbackNormalizationIso f).hom.app A), h]
  simpa only [NatTrans.comp_app] using
    congrArg (fun k ↦ k.app A) (normalization_transport (Category.comp_id f))

/-- The actual first component of the right unit triangle, with its scheme transport. -/
def boundedAboveFlatPerfectNormalizedRightUnitFirst {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedAboveFlatPerfectNormalizedPullback f ≅
      boundedAboveFlatPerfectNormalizedPullback f ⋙
      boundedAboveFlatPerfectNormalizedPullback (𝟙 X) :=
  eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.id_comp f).symm) ≪≫
    boundedAboveFlatPerfectNormalizedPullbackCompIso (𝟙 X) f

/-- The actual second component of the right unit triangle. -/
def boundedAboveFlatPerfectNormalizedRightUnitSecond {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedAboveFlatPerfectNormalizedPullback f ⋙
      boundedAboveFlatPerfectNormalizedPullback (𝟙 X) ≅
      boundedAboveFlatPerfectNormalizedPullback f :=
  isoWhiskerLeft (boundedAboveFlatPerfectNormalizedPullback f)
    (boundedAboveFlatPerfectNormalizedPullbackIdIso X) ≪≫
    Functor.rightUnitor _

/-- The actual first component of the left unit triangle, with its scheme transport. -/
def boundedAboveFlatPerfectNormalizedLeftUnitFirst {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedAboveFlatPerfectNormalizedPullback f ≅
      boundedAboveFlatPerfectNormalizedPullback (𝟙 Y) ⋙
      boundedAboveFlatPerfectNormalizedPullback f :=
  eqToIso (congrArg boundedAboveFlatPerfectNormalizedPullback (Category.comp_id f).symm) ≪≫
    boundedAboveFlatPerfectNormalizedPullbackCompIso f (𝟙 Y)

/-- The actual second component of the left unit triangle. -/
def boundedAboveFlatPerfectNormalizedLeftUnitSecond {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedAboveFlatPerfectNormalizedPullback (𝟙 Y) ⋙
      boundedAboveFlatPerfectNormalizedPullback f ≅
      boundedAboveFlatPerfectNormalizedPullback f :=
  isoWhiskerRight (boundedAboveFlatPerfectNormalizedPullbackIdIso Y)
    (boundedAboveFlatPerfectNormalizedPullback f) ≪≫
    Functor.leftUnitor _

/-- Both original normalized unit triangles have the same actual composite transformation. -/
theorem boundedAboveFlatPerfectNormalizedUnitRoutes_equation {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectNormalizedRightUnitFirst f).hom ≫
      (boundedAboveFlatPerfectNormalizedRightUnitSecond f).hom =
        (boundedAboveFlatPerfectNormalizedLeftUnitFirst f).hom ≫
          (boundedAboveFlatPerfectNormalizedLeftUnitSecond f).hom := by
  simp only [boundedAboveFlatPerfectNormalizedRightUnitFirst,
    boundedAboveFlatPerfectNormalizedRightUnitSecond,
    boundedAboveFlatPerfectNormalizedLeftUnitFirst, boundedAboveFlatPerfectNormalizedLeftUnitSecond,
    Iso.trans_hom, eqToIso.hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, Category.assoc]
  rw [boundedAboveFlatPerfectNormalizedPullbackCompIso_right_unitality,
    boundedAboveFlatPerfectNormalizedPullbackCompIso_left_unitality]

end AlgebraicGeometry.Scheme.Modules
