/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionLaurentEvaluationUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationCoefficients
public import Colib.CategoryTheory.Waldhausen.NormalizedWeakTransformation

/-! # The actual Laurent-unit square after normalization and the native small lift -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.GrothendieckSections
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.RingedSpace
universe u v₁ u₁ v₂ u₂
namespace AlgebraicGeometry.Scheme.Modules


/- Generic normalization and explicit whole-isomorphism transport boundaries. -/
private theorem normalizedScalarSquare
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (a : C ⥤ D) (e₁ : D ⥤ F) (e₀ : C ⥤ E) (p q : E ⥤ F)
    (α : a ⋙ e₁ ≅ e₀ ⋙ p) (ν : p ≅ q)
    (β : a ⋙ e₁ ≅ e₀ ⋙ q) (hβ : β = α ≪≫ isoWhiskerLeft e₀ ν)
    (σ : a ⟶ a) (τ : p ⟶ p) (δ : q ⟶ q)
    (hδ : δ = ν.inv ≫ τ ≫ ν.hom)
    (h : whiskerRight σ e₁ ≫ α.hom = α.hom ≫ whiskerLeft e₀ τ) :
    whiskerRight σ e₁ ≫ β.hom = β.hom ≫ whiskerLeft e₀ δ := by
  subst β
  subst δ
  apply NatTrans.ext
  funext x
  have hx := congrArg (fun η => η.app x) h
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] at hx
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, hx, Category.assoc]

private theorem smallScalarSquare
    {C D : Type u₁} [Category.{v₁} C] [Category.{v₁} D]
    {E F : Type u₂} [Category.{v₂} E] [Category.{v₂} F]
    (a : C ⥤ D) (e₁ : D ⥤ F) (e₀ : C ⥤ E) (p : E ⥤ F)
    (α : a ⋙ e₁ ≅ e₀ ⋙ p) (σ : a ⟶ a) (τ : p ⟶ p)
    (h : whiskerRight σ e₁ ≫ α.hom = α.hom ≫ whiskerLeft e₀ τ)
    {A : C ⥤ D} {E₁ : D ⥤ AsSmall.{0} F} {E₀ : C ⥤ AsSmall.{0} E}
    {P : AsSmall.{0} E ⥤ AsSmall.{0} F}
    (hA : A = a) (hE₁ : E₁ = e₁ ⋙ AsSmall.up)
    (hE₀ : E₀ = e₀ ⋙ AsSmall.up) (hP : P = asSmallFunctor p)
    (s : A ⋙ E₁ = a ⋙ (e₁ ⋙ AsSmall.up))
    (t : E₀ ⋙ P = (e₀ ⋙ AsSmall.up) ⋙ asSmallFunctor p)
    (β : A ⋙ E₁ ≅ E₀ ⋙ P)
    (hβ : β = Functor.transportIso s t (asSmallEvaluationWhiskerIso a e₁ e₀ p α))
    (sigmaSmall : A ⟶ A) (tauSmall : P ⟶ P)
    (hsigmaSmall : HEq sigmaSmall σ)
    (htauSmall : HEq tauSmall (whiskerLeft (AsSmall.down : AsSmall.{0} E ⥤ E)
      (whiskerRight τ (AsSmall.up : F ⥤ AsSmall.{0} F)))) :
    whiskerRight sigmaSmall E₁ ≫ β.hom = β.hom ≫ whiskerLeft E₀ tauSmall := by
  subst A
  subst E₁
  subst E₀
  subst P
  have hsigmaSmall' := eq_of_heq hsigmaSmall
  have htauSmall' := eq_of_heq htauSmall
  subst sigmaSmall
  subst tauSmall
  subst β
  simp only [Functor.transportIso_hom, eqToHom_refl, Category.id_comp, Category.comp_id]
  apply NatTrans.ext
  funext x
  have hx := congrArg (fun η => η.app x) h
  have hy := congrArg (AsSmall.up : F ⥤ AsSmall.{0} F).map hx
  change (AsSmall.up : F ⥤ AsSmall.{0} F).map (e₁.map (σ.app x)) ≫
      AsSmall.up.map (α.hom.app x) =
    AsSmall.up.map (α.hom.app x) ≫ AsSmall.up.map (τ.app (e₀.obj x))
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.comp_obj, Functor.map_comp] at hy
  exact hy


/-- Model-composite endpoints are exposed only with abstract model arrows. -/
private theorem modelScalarSquare
    {E F : Type u₂} [Category.{v₂} E] [Category.{v₂} F]
    {V₀ V₁ : WideSubcategory
      SmallWaldhausenCategory.preservesZero.{max u₂ v₂}}
    (W₀ : Structure E) (W₁ : Structure F)
    (A : V₀ ⟶ V₁) (E₀ : V₀ ⟶ asSmallCategory W₀)
    (E₁ : V₁ ⟶ asSmallCategory W₁)
    (P : asSmallCategory W₀ ⟶ asSmallCategory W₁)
    (a : V₀.obj.Obj ⥤ V₁.obj.Obj) (e₁ : V₁.obj.Obj ⥤ F)
    (e₀ : V₀.obj.Obj ⥤ E) (p : E ⥤ F)
    (α : a ⋙ e₁ ≅ e₀ ⋙ p) (σ : a ⟶ a) (τ : p ⟶ p)
    (h : whiskerRight σ e₁ ≫ α.hom = α.hom ≫ whiskerLeft e₀ τ)
    (hA : A.hom.toFunctor = a) (hE₁ : E₁.hom.toFunctor = e₁ ⋙ AsSmall.up)
    (hE₀ : E₀.hom.toFunctor = e₀ ⋙ AsSmall.up)
    (hP : P.hom.toFunctor = asSmallFunctor p)
    (s : (A ≫ E₁).hom.toFunctor = a ⋙ (e₁ ⋙ AsSmall.up))
    (t : (E₀ ≫ P).hom.toFunctor = (e₀ ⋙ AsSmall.up) ⋙ asSmallFunctor p)
    (β : (A ≫ E₁).hom.toFunctor ≅ (E₀ ≫ P).hom.toFunctor)
    (hβ : β = modelAsSmallEvaluationIso W₀ W₁ A E₀ E₁ P a e₁ e₀ p α s t)
    (sigmaSmall : A.hom.toFunctor ⟶ A.hom.toFunctor)
    (tauSmall : P.hom.toFunctor ⟶ P.hom.toFunctor)
    (hsigmaSmall : HEq sigmaSmall σ)
    (htauSmall : HEq tauSmall (whiskerLeft (AsSmall.down : AsSmall.{0} E ⥤ E)
      (whiskerRight τ (AsSmall.up : F ⥤ AsSmall.{0} F)))) :
    whiskerRight sigmaSmall E₁.hom.toFunctor ≫ β.hom =
      β.hom ≫ whiskerLeft E₀.hom.toFunctor tauSmall := by
  exact smallScalarSquare a e₁ e₀ p α σ τ h hA hE₁ hE₀ hP s t β
    hβ
    sigmaSmall tauSmall hsigmaSmall htauSmall

/-- The actual strict action at its original section model endpoint. -/
def boundedAboveFlatAffineSectionLaurentModelUnit (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R)).hom.toFunctor ⟶
      (boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R)).hom.toFunctor :=
  (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom

/-- The actual raw action, conjugated by the canonical zero normalization and lifted once. -/
def boundedAboveFlatAffineOriginalLaurentModelUnit (R : CommRingCat.{u}) :
    (boundedAboveFlatAffinePullbackModelMap (laurentCoefficientInclusion R)).hom.toFunctor ⟶
      (boundedAboveFlatAffinePullbackModelMap (laurentCoefficientInclusion R)).hom.toFunctor :=
  whiskerLeft AsSmall.down (whiskerRight
    (normalizedWeakTransformation
      (boundedAboveFlatPerfectPullback_isExact (laurentProjection R))
      (boundedAboveFlatPerfectPullback_isExact (laurentProjection R))
      (boundedAboveFlatPerfectPullbackUnitIso
          (laurentProjection R) (laurentCoordinate R)).hom)
    AsSmall.up)

/-- The coefficient comparison retains its original scalar square after zero normalization. -/
theorem boundedAboveFlatAffineSectionLaurentNormalizedUnitSquare (R : CommRingCat.{u}) :
    whiskerRight (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom
        (boundedAboveFlatAffineOriginalEvaluation (.of (LaurentPolynomial R))) ≫
      (boundedAboveFlatAffineEvaluationCoefficientIso (laurentCoefficientInclusion R)).hom =
    (boundedAboveFlatAffineEvaluationCoefficientIso (laurentCoefficientInclusion R)).hom ≫
      whiskerLeft (boundedAboveFlatAffineOriginalEvaluation R)
        (normalizedWeakTransformation
          (boundedAboveFlatPerfectPullback_isExact (laurentProjection R))
          (boundedAboveFlatPerfectPullback_isExact (laurentProjection R))
          (boundedAboveFlatPerfectPullbackUnitIso
          (laurentProjection R) (laurentCoordinate R)).hom) := by
  exact normalizedScalarSquare
    (boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineOriginalEvaluation (.of (LaurentPolynomial R)))
    (boundedAboveFlatAffineOriginalEvaluation R)
    (boundedAboveFlatPerfectPullback (laurentProjection R))
    (boundedAboveFlatAffineNormalizedPullback (laurentCoefficientInclusion R))
    (originalCoefficientIso boundedAboveFlatAffinePseudofunctor (laurentCoefficientInclusion R))
    (boundedAboveFlatAffinePullbackNormalization (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineEvaluationCoefficientIso (laurentCoefficientInclusion R))
    (by rfl)
    (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom
    (boundedAboveFlatPerfectPullbackUnitIso (laurentProjection R) (laurentCoordinate R)).hom
    _ (by rfl) (boundedAboveFlatAffineSectionLaurentCoefficientUnitSquare R)

/-- The same original scalar square survives the literal native small-model lift. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentModelUnit.lean:34-85"
  "adaptation" "Actual strict and geometric Laurent actions through normalization and `AsSmall`"]
theorem boundedAboveFlatAffineSectionLaurentModelEvaluationUnitSquare (R : CommRingCat.{u}) :
    whiskerRight (boundedAboveFlatAffineSectionLaurentModelUnit R)
        (boundedAboveFlatAffineEvaluationModelMap (.of (LaurentPolynomial R))).hom.toFunctor ≫
      (boundedAboveFlatAffineEvaluationModelIso (laurentCoefficientInclusion R)).hom =
    (boundedAboveFlatAffineEvaluationModelIso (laurentCoefficientInclusion R)).hom ≫
      whiskerLeft (boundedAboveFlatAffineEvaluationModelMap R).hom.toFunctor
        (boundedAboveFlatAffineOriginalLaurentModelUnit R) := by
  exact modelScalarSquare
    (boundedAboveFlatPerfectWaldhausen (Spec R).toRingedSpace)
    (boundedAboveFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))).toRingedSpace)
    (boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineEvaluationModelMap R)
    (boundedAboveFlatAffineEvaluationModelMap (.of (LaurentPolynomial R)))
    (boundedAboveFlatAffinePullbackModelMap (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineOriginalEvaluation (.of (LaurentPolynomial R)))
    (boundedAboveFlatAffineOriginalEvaluation R)
    (boundedAboveFlatAffineNormalizedPullback (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineEvaluationCoefficientIso (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom
    (normalizedWeakTransformation
      (boundedAboveFlatPerfectPullback_isExact (laurentProjection R))
      (boundedAboveFlatPerfectPullback_isExact (laurentProjection R))
      (boundedAboveFlatPerfectPullbackUnitIso (laurentProjection R) (laurentCoordinate R)).hom)
    (boundedAboveFlatAffineSectionLaurentNormalizedUnitSquare R)
    (boundedAboveFlatAffineSectionModelMap_toFunctor (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineEvaluationModelMap_toFunctor (.of (LaurentPolynomial R)))
    (boundedAboveFlatAffineEvaluationModelMap_toFunctor R)
    (boundedAboveFlatAffinePullbackModelMap_toFunctor (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineEvaluationModelIso_source (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineEvaluationModelIso_target (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineEvaluationModelIso (laurentCoefficientInclusion R))
    (by rfl)
    (boundedAboveFlatAffineSectionLaurentModelUnit R)
    (boundedAboveFlatAffineOriginalLaurentModelUnit R) (by rfl) (by rfl)

end AlgebraicGeometry.Scheme.Modules
