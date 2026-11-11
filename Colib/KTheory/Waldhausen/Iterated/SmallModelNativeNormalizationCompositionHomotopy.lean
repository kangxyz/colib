/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SmallModelNormalizationCompositionHomotopy

/-!
# Native model arrows and the canonical normalization comparison

The native model arrows are retained together with equalities to their specified
canonical chosen-zero constructors. The native composition isomorphism is retained
with its constructor equality and its actual functor projections. Substitution takes
place in abstract Waldhausen categories, before any geometric specialization.

The supplied endpoint casts are honest equalities of the complete prespectrum maps.
Neither a profile of pointwise values nor a replacement normalization is assumed.
-/
@[expose] public noncomputable section

open CategoryTheory Topology.LoopPrespectrum

universe u v

namespace CategoryTheory.Waldhausen.IteratedS

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {V : Structure D} {U : Structure E}
  {H : C ⥤ E} {F : C ⥤ D} {G : D ⥤ E}
  (hH : IsExact W.cof W.weq U.cof U.weq H)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact V.cof V.weq U.cof U.weq G)

variable
  (i' : CategoryTheory.rebaseFunctor H W.zero U.zero
      ((hH.zero W.isZero).iso U.isZero) ≅
    CategoryTheory.rebaseFunctor F W.zero V.zero
      ((hF.zero W.isZero).iso V.isZero) ⋙
    CategoryTheory.rebaseFunctor G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero))
  (A : asSmallCategory W ⟶ asSmallCategory V)
  (B : asSmallCategory V ⟶ asSmallCategory U)
  (K : asSmallCategory W ⟶ asSmallCategory U)
  (hA : A = asSmallCategoryMap W V hF.rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
  (hB : B = asSmallCategoryMap V U hG.rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
  (hK : K = asSmallCategoryMap W U hH.rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
  (hSource : K.hom.toFunctor =
    asSmallFunctor (CategoryTheory.rebaseFunctor H W.zero U.zero
      ((hH.zero W.isZero).iso U.isZero)))
  (hTarget : (A ≫ B).hom.toFunctor =
    asSmallFunctor (CategoryTheory.rebaseFunctor F W.zero V.zero
      ((hF.zero W.isZero).iso V.isZero)) ⋙
    asSmallFunctor (CategoryTheory.rebaseFunctor G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero)))
  (μ : K.hom.toFunctor ≅ (A ≫ B).hom.toFunctor)
  (hμ : μ = modelAsSmallCompositionIso W U
    (CategoryTheory.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero))
    (CategoryTheory.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero))
    (CategoryTheory.rebaseFunctor H W.zero U.zero ((hH.zero W.isZero).iso U.isZero))
    i' hSource hTarget)
  (hweak : ∀ x, U.asSmall.weq (μ.hom.app x))
  (hf : prespectrumMap K = exactOriginalPrespectrumMap W U hH)
  (hg : prespectrumMap (A ≫ B) =
    exactOriginalPrespectrumMap W V hF ≫ exactOriginalPrespectrumMap V U hG)

include hA hB hK hμ

/-- Constructor equalities of complete native arrows and the native isomorphism
identify the whole original track. Its weak witness and endpoint casts remain explicit. -/
theorem nativeModelAsSmallNormalizedCompHomotopy_level (n : ℕ) :
    ((prespectrumTransformationHomotopy (F := K) (G := A ≫ B) μ.hom hweak).cast
      hf hg).level n =
    ((originalPrespectrumTransformationHomotopy W U hH.rebase
      (hF.rebase.comp hG.rebase)
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
      ((congrArg (CategoryTheory.rebaseFunctor G V.zero U.zero
        ((hG.zero V.isZero).iso U.isZero)).obj
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).trans
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
      i'.hom (fun _ ↦ U.weq_iso _ inferInstance)).cast rfl
      (originalPrespectrumMap_comp W V U hF.rebase hG.rebase
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))).level n := by
  subst A
  subst B
  subst K
  subst μ
  exact modelAsSmallCompositionIso_prespectrumHomotopy_level W V U
    hH.rebase hF.rebase hG.rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    i' hSource hTarget n

variable (i : H ≅ F ⋙ G)
  (hcomp : i'.hom = normalizedWeakTransformation hH (hF.comp hG) i.hom ≫
    (exactNormalizationCompIso hF hG).hom)

include hcomp

/-- The actual native total track has the canonical relative comparison to the
original geometric track followed by binary normalization. No native model is unfolded. -/
@[no_expose]
def nativeModelAsSmallNormalizationCompTrackComparison :
    ((prespectrumTransformationHomotopy (F := K) (G := A ≫ B) μ.hom hweak).cast
      hf hg).RelHomotopy
      ((exactOriginalPrespectrumIsoHomotopy W U hH (hF.comp hG) i).trans
        (exactOriginalPrespectrumMapCompHomotopy W V U hF hG)) := by
  subst A
  subst B
  subst K
  subst μ
  exact (modelAsSmallNormalizationCompTrackComparison
    (hH := hH) (hF := hF) (hG := hG) (i := i) (i' := i')
    (hcomp := hcomp) (hSource := hSource) (hTarget := hTarget)).ofLevels _ _
      (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The complete two-time level is exactly the existing canonical normalization
triangle, including the independent prespectrum structure coordinate. -/
theorem nativeModelAsSmallNormalizationCompTrackComparison_level (n : ℕ) :
    ((nativeModelAsSmallNormalizationCompTrackComparison
      (hH := hH) (hF := hF) (hG := hG) (i' := i')
      (A := A) (B := B) (K := K) (hA := hA) (hB := hB) (hK := hK)
      (hSource := hSource) (hTarget := hTarget) (μ := μ) (hμ := hμ)
      (hweak := hweak) (hf := hf) (hg := hg)
      (i := i) (hcomp := hcomp)).level n).toContinuousMap =
      ((exactNormalizationCompTrackComparison hH hF hG i).level n).toContinuousMap := by
  subst A
  subst B
  subst K
  subst μ
  exact modelAsSmallNormalizationCompTrackComparison_level
    (hH := hH) (hF := hF) (hG := hG) (i := i) (i' := i')
    (hcomp := hcomp) (hSource := hSource) (hTarget := hTarget) n

end CategoryTheory.Waldhausen.IteratedS
