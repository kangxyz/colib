/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.NormalizationCompositionHomotopy
public import Colib.KTheory.Waldhausen.Iterated.SmallModelCompositionHomotopy

/-!
# The actual lifted normalization constraint and its geometric split

A normalized composition isomorphism whose forward transformation is the proved
canonical factorization gives the original normalization triangle on every level.
Its actual small-model source and target projections, original geometric isomorphism,
canonical chosen-zero witnesses and prespectrum composition cast are all retained.
The comparison is relative to the endpoints and basepoint line and preserves the
independent prespectrum structure coordinate.
-/
@[expose] public noncomputable section

open CategoryTheory Topology.LoopPrespectrum

universe u v

namespace CategoryTheory.Waldhausen.IteratedS

private theorem originalTransformationCast_congr_level
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (W : Structure C) (V : Structure D) {F G : C ⥤ D}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact W.cof W.weq V.cof V.weq G)
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (η θ : F ⟶ G) (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (e : η = θ) {f g : originalPrespectrum W ⟶ originalPrespectrum V}
    (hf : originalPrespectrumMap W V hF h0F = f)
    (hg : originalPrespectrumMap W V hG h0G = g) (n : ℕ) :
    ((originalPrespectrumTransformationHomotopy W V hF hG h0F h0G η hη).cast
      hf hg).level n =
    ((originalPrespectrumTransformationHomotopy W V hF hG h0F h0G θ hθ).cast
      hf hg).level n := by
  cases e
  rfl

private theorem ofLevels_level_toContinuousMap
    {X Y : Topology.LoopPrespectrum.{u}}
    {f g f' g' : X ⟶ Y} {H K : Homotopy f g}
    (J : H.RelHomotopy K) (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n)
    (hK : ∀ n, K'.level n = K.level n) (n : ℕ) :
    ((J.ofLevels H' K' hH hK).level n).toContinuousMap =
      (J.level n).toContinuousMap := by
  rfl

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {V : Structure D} {U : Structure E}
  {H : C ⥤ E} {F : C ⥤ D} {G : D ⥤ E}
  (hH : IsExact W.cof W.weq U.cof U.weq H)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact V.cof V.weq U.cof U.weq G)

variable (i : H ≅ F ⋙ G)
  (i' : CategoryTheory.rebaseFunctor H W.zero U.zero
      ((hH.zero W.isZero).iso U.isZero) ≅
    CategoryTheory.rebaseFunctor F W.zero V.zero
      ((hF.zero W.isZero).iso V.isZero) ⋙
    CategoryTheory.rebaseFunctor G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero))
  (hcomp : i'.hom = normalizedWeakTransformation hH (hF.comp hG) i.hom ≫
    (exactNormalizationCompIso hF hG).hom)
  (hSource : (asSmallCategoryMap W U hH.rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).hom.toFunctor =
      asSmallFunctor (CategoryTheory.rebaseFunctor H W.zero U.zero
        ((hH.zero W.isZero).iso U.isZero)))
  (hTarget : (asSmallCategoryMap W V hF.rebase
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) ≫
    asSmallCategoryMap V U hG.rebase
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).hom.toFunctor =
        asSmallFunctor (CategoryTheory.rebaseFunctor F W.zero V.zero
          ((hF.zero W.isZero).iso V.isZero)) ⋙
        asSmallFunctor (CategoryTheory.rebaseFunctor G V.zero U.zero
          ((hG.zero V.isZero).iso U.isZero)))

/-- The actual lifted normalized constraint is relatively compared with the geometric
iso track followed by canonical binary normalization, using its proved factorization. -/
@[no_expose]
def modelAsSmallNormalizationCompTrackComparison
    (hcomp : i'.hom = normalizedWeakTransformation hH (hF.comp hG) i.hom ≫
      (exactNormalizationCompIso hF hG).hom) :
    ((prespectrumTransformationHomotopy
      (F := asSmallCategoryMap W U hH.rebase
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
      (G := asSmallCategoryMap W V hF.rebase
          (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) ≫
        asSmallCategoryMap V U hG.rebase
          (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
      (modelAsSmallCompositionIso W U
        (CategoryTheory.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero))
        (CategoryTheory.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero))
        (CategoryTheory.rebaseFunctor H W.zero U.zero ((hH.zero W.isZero).iso U.isZero))
        i' hSource hTarget).hom
      (fun x ↦ U.asSmall.weq_iso _ (by
        change IsIso
          ((modelAsSmallCompositionIso W U
            (CategoryTheory.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero))
            (CategoryTheory.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero))
            (CategoryTheory.rebaseFunctor H W.zero U.zero ((hH.zero W.isZero).iso U.isZero))
            i' hSource hTarget).hom.app x)
        infer_instance))).cast rfl (prespectrumFunctor.map_comp _ _)).RelHomotopy
      ((exactOriginalPrespectrumIsoHomotopy W U hH (hF.comp hG) i).trans
        (exactOriginalPrespectrumMapCompHomotopy W V U hF hG)) := by
  refine (exactNormalizationCompTrackComparison hH hF hG i).ofLevels _ _
    ?_ (fun _ ↦ rfl)
  intro n
  have hmodel := modelAsSmallCompositionIso_prespectrumHomotopy_level W V U
    hH.rebase hF.rebase hG.rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    i' hSource hTarget n
  have hraw := originalTransformationCast_congr_level W U
    hH.rebase (hF.rebase.comp hG.rebase)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    ((congrArg (CategoryTheory.rebaseFunctor G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero)).obj
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).trans
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
    i'.hom
    (normalizedWeakTransformation hH (hF.comp hG) i.hom ≫
      (exactNormalizationCompIso hF hG).hom)
    (fun _ ↦ U.weq_iso _ inferInstance)
    (fun A ↦ U.weq.comp_mem _ _
      (normalizedWeakTransformation_weak hH (hF.comp hG) i.hom
        (fun _ ↦ U.weq_iso _ inferInstance) A)
      (U.weq_iso _ inferInstance))
    hcomp rfl
    (originalPrespectrumMap_comp W V U hF.rebase hG.rebase
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)) n
  dsimp only [originalPrespectrum] at hraw ⊢
  exact hmodel.trans hraw

/-- Every complete two-time level is the actual canonical normalization triangle. -/
theorem modelAsSmallNormalizationCompTrackComparison_level (n : ℕ) :
    ((modelAsSmallNormalizationCompTrackComparison
      (hH := hH) (hF := hF) (hG := hG) (i := i) (i' := i')
      (hcomp := hcomp) (hSource := hSource) (hTarget := hTarget)).level n).toContinuousMap =
      ((exactNormalizationCompTrackComparison hH hF hG i).level n).toContinuousMap := by
  exact ofLevels_level_toContinuousMap
    (exactNormalizationCompTrackComparison hH hF hG i) _ _ _ _ n

end CategoryTheory.Waldhausen.IteratedS
