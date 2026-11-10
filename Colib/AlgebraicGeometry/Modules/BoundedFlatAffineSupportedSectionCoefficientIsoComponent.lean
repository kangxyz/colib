/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSupportedSectionCoefficientIso

/-!
# Exact underlying component of the supported coefficient transition

Compute the image of the already constructed coefficient transition under the native
fully faithful supported inclusion. The result is the inverse original cocartesian
evaluation transition, with its actual endpoint transports. This component calculation
is derived from the original construction, not asserted as strict naturality of evaluation.

Adapted from Quillen `SupportedSectionCoefficientIso.lean:31-144` in
`Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.RingedSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

private theorem cancel_whisker_hom_of_eq {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    (F G : A ⥤ B) (H : B ⥤ C) [H.Full] [H.Faithful]
    (e : F ⋙ H ≅ G ⋙ H) (β : F ≅ G)
    (hβ : β = Functor.fullyFaithfulCancelRight H e) :
    Functor.whiskerRight β.hom H = e.hom := by
  subst β
  apply NatTrans.ext
  funext X
  change H.map ((Functor.fullyFaithfulCancelRight H e).hom.app X) = e.hom.app X
  simp only [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]

private theorem glue_hom_of_eq {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    (F G : A ⥤ B) (K : A ⥤ C) (P Q : C ⥤ D) (J : D ⥤ B)
    (hF : F = K ⋙ P ⋙ J) (hG : G = K ⋙ Q ⋙ J) (e : P ≅ Q)
    (α : F ≅ G)
    (hα : α = eqToIso hF ≪≫ Functor.isoWhiskerLeft K (Functor.isoWhiskerRight e J) ≪≫
      eqToIso hG.symm) :
    α.hom = eqToHom hF ≫ Functor.whiskerLeft K (Functor.whiskerRight e.hom J) ≫
      eqToHom hG.symm := by
  subst α
  simp only [Iso.trans_hom, eqToIso.hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]

private theorem supported_glue_app {A B C : Type*}
    [Category* A] [Category* B] [Category* C]
    (Ps : ObjectProperty A) (Pt : ObjectProperty B)
    (F G : Ps.FullSubcategory ⥤ Pt.FullSubcategory)
    (L M : A ⥤ C) (J : C ⥤ B)
    (hF : F ⋙ Pt.ι = Ps.ι ⋙ L ⋙ J) (hG : G ⋙ Pt.ι = Ps.ι ⋙ M ⋙ J)
    (e : L ⟶ M) (β : F ⟶ G)
    (hβ : Functor.whiskerRight β Pt.ι = eqToHom hF ≫
      Functor.whiskerLeft Ps.ι (Functor.whiskerRight e J) ≫ eqToHom hG.symm)
    (s : Ps.FullSubcategory) :
    Pt.ι.map (β.app s) =
      eqToHom (congrArg (fun T : Ps.FullSubcategory ⥤ B ↦ T.obj s) hF) ≫
        J.map (e.app s.obj) ≫
        eqToHom (congrArg (fun T : Ps.FullSubcategory ⥤ B ↦ T.obj s) hG.symm) := by
  have h := congrArg (fun η : F ⋙ Pt.ι ⟶ G ⋙ Pt.ι ↦ η.app s) hβ
  simpa only [NatTrans.comp_app, eqToHom_app, Functor.comp_obj, ObjectProperty.ι_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app] using h

private theorem identity_ends {C : Type*} [Category* C] {X Y : C}
    (p : X ⟶ X) (q : X ⟶ Y) (r : Y ⟶ Y) (hp : p = 𝟙 X) (hr : r = 𝟙 Y) :
    p ≫ q ≫ r = q := by
  rw [hp, hr, Category.id_comp, Category.comp_id]

variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}

attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation
  boundedAboveFlatAffineEvaluationAt

variable (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)

section

attribute [local irreducible] boundedAboveFlatAffineSupportedSectionsMap
  boundedAboveFlatAffineSupportedEvaluation boundedAboveFlatPerfectSupportedPullback
  boundedAboveFlatPerfectPullback

private theorem supportedCoefficientIso_eq :
    boundedAboveFlatAffineSupportedSectionCoefficientIso j j' f l h =
      Functor.fullyFaithfulCancelRight
        (F := boundedAboveFlatAffineSupportedSectionsMap j j' f l h ⋙
          boundedAboveFlatAffineSupportedEvaluation j')
        (G := boundedAboveFlatAffineSupportedEvaluation j ⋙
          boundedAboveFlatPerfectSupportedPullback
            (boundedAboveFlatAffineSupportedPairSquare j j' f l h))
        (boundedAboveFlatPerfectSupported j').ι
        (eqToIso (boundedAboveFlatAffineSupportedReindexEvaluation_forget j j' f l h) ≪≫
      Functor.isoWhiskerLeft (boundedAboveFlatAffineSectionSupported j).ι
        (Functor.isoWhiskerRight
          (eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
            (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm)
          (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι) ≪≫
      eqToIso (boundedAboveFlatAffineSupportedEvaluationPullback_forget j j' f l h).symm) := rfl

private theorem supportedCoefficientIso_whisker_hom :
    Functor.whiskerRight
        (boundedAboveFlatAffineSupportedSectionCoefficientIso j j' f l h).hom
        (boundedAboveFlatPerfectSupported j').ι =
    (eqToIso (boundedAboveFlatAffineSupportedReindexEvaluation_forget j j' f l h) ≪≫
      Functor.isoWhiskerLeft (boundedAboveFlatAffineSectionSupported j).ι
        (Functor.isoWhiskerRight
          (eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
            (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm)
          (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι) ≪≫
      eqToIso (boundedAboveFlatAffineSupportedEvaluationPullback_forget j j' f l h).symm).hom :=
  cancel_whisker_hom_of_eq
    (boundedAboveFlatAffineSupportedSectionsMap j j' f l h ⋙
      boundedAboveFlatAffineSupportedEvaluation j')
    (boundedAboveFlatAffineSupportedEvaluation j ⋙ boundedAboveFlatPerfectSupportedPullback
      (boundedAboveFlatAffineSupportedPairSquare j j' f l h))
    (boundedAboveFlatPerfectSupported j').ι
    (eqToIso (boundedAboveFlatAffineSupportedReindexEvaluation_forget j j' f l h) ≪≫
      Functor.isoWhiskerLeft (boundedAboveFlatAffineSectionSupported j).ι
        (Functor.isoWhiskerRight
          (eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
            (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm)
          (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι) ≪≫
      eqToIso (boundedAboveFlatAffineSupportedEvaluationPullback_forget j j' f l h).symm)
    (boundedAboveFlatAffineSupportedSectionCoefficientIso j j' f l h)
    (supportedCoefficientIso_eq j j' f l h)

private theorem supportedCoefficientGlue_hom :
    (eqToIso (boundedAboveFlatAffineSupportedReindexEvaluation_forget j j' f l h) ≪≫
      Functor.isoWhiskerLeft (boundedAboveFlatAffineSectionSupported j).ι
        (Functor.isoWhiskerRight
          (eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
            (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm)
          (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι) ≪≫
      eqToIso (boundedAboveFlatAffineSupportedEvaluationPullback_forget j j' f l h).symm).hom =
      eqToHom (boundedAboveFlatAffineSupportedReindexEvaluation_forget j j' f l h) ≫
      Functor.whiskerLeft (boundedAboveFlatAffineSectionSupported j).ι
        (Functor.whiskerRight
          ((eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
            (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm).hom)
          (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι) ≫
      eqToHom (boundedAboveFlatAffineSupportedEvaluationPullback_forget j j' f l h).symm :=
  glue_hom_of_eq
    ((boundedAboveFlatAffineSupportedSectionsMap j j' f l h ⋙
      boundedAboveFlatAffineSupportedEvaluation j') ⋙ (boundedAboveFlatPerfectSupported j').ι)
    ((boundedAboveFlatAffineSupportedEvaluation j ⋙ boundedAboveFlatPerfectSupportedPullback
      (boundedAboveFlatAffineSupportedPairSquare j j' f l h)) ⋙
        (boundedAboveFlatPerfectSupported j').ι)
    (boundedAboveFlatAffineSectionSupported j).ι
    (boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineOriginalEvaluation S)
    (boundedAboveFlatAffineOriginalEvaluation R ⋙ boundedAboveFlatPerfectPullback (Spec.map f))
    (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι
    (boundedAboveFlatAffineSupportedReindexEvaluation_forget j j' f l h)
    (boundedAboveFlatAffineSupportedEvaluationPullback_forget j j' f l h)
    (eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
      (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm)
    (eqToIso (boundedAboveFlatAffineSupportedReindexEvaluation_forget j j' f l h) ≪≫
      Functor.isoWhiskerLeft (boundedAboveFlatAffineSectionSupported j).ι
        (Functor.isoWhiskerRight
          (eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
            (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm)
          (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι) ≪≫
      eqToIso (boundedAboveFlatAffineSupportedEvaluationPullback_forget j j' f l h).symm) rfl

private theorem supportedCoefficientIso_hom_with_transports
    (s : BoundedAboveFlatAffineSupportedSections j) :
    (boundedAboveFlatPerfectSupported j').ι.map
      ((boundedAboveFlatAffineSupportedSectionCoefficientIso j j' f l h).hom.app s) =
      eqToHom (congrArg (fun T : BoundedAboveFlatAffineSupportedSections j ⥤
        CochainComplex (Spec S).Modules ℤ ↦ T.obj s)
        (boundedAboveFlatAffineSupportedReindexEvaluation_forget j j' f l h)) ≫
      (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι.map
        ((eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
          (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm).hom.app s.obj) ≫
      eqToHom (congrArg (fun T : BoundedAboveFlatAffineSupportedSections j ⥤
        CochainComplex (Spec S).Modules ℤ ↦ T.obj s)
        (boundedAboveFlatAffineSupportedEvaluationPullback_forget j j' f l h).symm) :=
  supported_glue_app
    (boundedAboveFlatAffineSectionSupported j) (boundedAboveFlatPerfectSupported j')
    (boundedAboveFlatAffineSupportedSectionsMap j j' f l h ⋙
      boundedAboveFlatAffineSupportedEvaluation j')
    (boundedAboveFlatAffineSupportedEvaluation j ⋙ boundedAboveFlatPerfectSupportedPullback
      (boundedAboveFlatAffineSupportedPairSquare j j' f l h))
    (boundedAboveFlatAffineSectionsMap f ⋙ boundedAboveFlatAffineOriginalEvaluation S)
    (boundedAboveFlatAffineOriginalEvaluation R ⋙ boundedAboveFlatPerfectPullback (Spec.map f))
    (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι
    (boundedAboveFlatAffineSupportedReindexEvaluation_forget j j' f l h)
    (boundedAboveFlatAffineSupportedEvaluationPullback_forget j j' f l h)
    (eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
      (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm).hom
    (boundedAboveFlatAffineSupportedSectionCoefficientIso j j' f l h).hom
    ((supportedCoefficientIso_whisker_hom j j' f l h).trans
      (supportedCoefficientGlue_hom j j' f l h)) s

end

/-- After forgetting support the coefficient comparison is exactly the original transition,
with its genuine reindex-evaluation endpoint transport and the inverse orientation. -/
theorem boundedAboveFlatAffineSupportedSectionCoefficientIso_hom_app
    (s : BoundedAboveFlatAffineSupportedSections j) :
    (boundedAboveFlatPerfectSupported j').ι.map
        ((boundedAboveFlatAffineSupportedSectionCoefficientIso j j' f l h).hom.app s) =
      (boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι.map
        ((eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
          (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm).hom.app s.obj) :=
  (supportedCoefficientIso_hom_with_transports j j' f l h s).trans
    (identity_ends (C := CochainComplex (Spec S).Modules ℤ)
      (X := (((boundedAboveFlatAffineOriginalEvaluation S).obj
        ((boundedAboveFlatAffineSectionsMap f).obj s.obj)).obj))
      (Y := (((boundedAboveFlatPerfectPullback (Spec.map f)).obj
        ((boundedAboveFlatAffineOriginalEvaluation R).obj s.obj)).obj))
      (eqToHom (congrArg (fun T : BoundedAboveFlatAffineSupportedSections j ⥤
        CochainComplex (Spec S).Modules ℤ ↦ T.obj s)
        (boundedAboveFlatAffineSupportedReindexEvaluation_forget j j' f l h)))
      ((boundedAboveFlatPerfectComplex (Spec S).toRingedSpace).ι.map
        ((eqToIso (boundedAboveFlatAffineSectionsMap_comp_evaluation f) ≪≫
          (boundedAboveFlatAffineEvaluationPullbackIso R (Under.mk f)).symm).hom.app s.obj))
      (eqToHom (congrArg (fun T : BoundedAboveFlatAffineSupportedSections j ⥤
        CochainComplex (Spec S).Modules ℤ ↦ T.obj s)
        (boundedAboveFlatAffineSupportedEvaluationPullback_forget j j' f l h).symm))
      (boundedAboveFlatAffineSupportedReindexEvaluation_forget_eqToHom j j' f l h s)
      (boundedAboveFlatAffineSupportedEvaluationPullback_forget_eqToHom j j' f l h s))

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0501", colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    SupportedSectionCoefficientIso.lean:31-144"
  "adaptation"
  "Exact chain-map projection derived from the actual supported coefficient construction"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSupportedSectionCoefficientIso_hom_app
