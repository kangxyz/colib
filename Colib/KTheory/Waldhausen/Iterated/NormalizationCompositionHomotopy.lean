/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.ExactCompositionHomotopy
public import Colib.KTheory.Waldhausen.Iterated.NormalizationNaturality
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# The total normalization track and its geometric split

The actual transformation to a composite functor is normalized once. Its composite with
binary normalization gives a total track. The original transformation-composition triangle
compares that track with the geometric transformation followed by binary normalization.
The comparison fixes both endpoint maps and the basepoint line, and retains independent
comparison, original-homotopy, and prespectrum-structure coordinates.

Implementation provenance: the general-category argument of
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CompositionTrack.lean:81-131`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor Topology.LoopPrespectrum

universe u v

namespace CategoryTheory.Waldhausen.IteratedS

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {V : Structure D} {U : Structure E}
  {H : C ⥤ E} {F : C ⥤ D} {G : D ⥤ E}
  (hH : IsExact W.cof W.weq U.cof U.weq H)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact V.cof V.weq U.cof U.weq G)


/-- Only the middle canonical normalization cancels in the total transformation. -/
theorem normalizedWeakTransformation_comp_exactNormalizationCompIso (η : H ⟶ F ⋙ G) :
    normalizedWeakTransformation hH (hF.comp hG) η ≫
        (exactNormalizationCompIso hF hG).hom =
      (CategoryTheory.rebaseFunctorIso H W.zero U.zero
        ((hH.zero W.isZero).iso U.isZero)).inv ≫ η ≫
        whiskerRight (CategoryTheory.rebaseFunctorIso F W.zero V.zero
          ((hF.zero W.isZero).iso V.isZero)).hom G ≫
        whiskerLeft (CategoryTheory.rebaseFunctor F W.zero V.zero
          ((hF.zero W.isZero).iso V.isZero))
          (CategoryTheory.rebaseFunctorIso G V.zero U.zero
            ((hG.zero V.isZero).iso U.isZero)).hom := by
  simp [normalizedWeakTransformation, exactNormalizationCompIso, Category.assoc]

/-- The total normalized track is relatively homotopic to the original geometric track
followed by the canonical binary normalization track. -/
def exactNormalizationCompTrackComparison (i : H ≅ F ⋙ G) :
    ((originalPrespectrumTransformationHomotopy W U hH.rebase
      (hF.rebase.comp hG.rebase)
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
      ((congrArg (CategoryTheory.rebaseFunctor G V.zero U.zero
        ((hG.zero V.isZero).iso U.isZero)).obj
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).trans
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
      (normalizedWeakTransformation hH (hF.comp hG) i.hom ≫
        (exactNormalizationCompIso hF hG).hom)
      (fun A ↦ U.weq.comp_mem _ _
        (normalizedWeakTransformation_weak hH (hF.comp hG) i.hom
          (fun _ ↦ U.weq_iso _ inferInstance) A)
        (U.weq_iso _ inferInstance))).cast rfl
      (originalPrespectrumMap_comp W V U hF.rebase hG.rebase
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))).RelHomotopy
      ((exactOriginalPrespectrumIsoHomotopy W U hH (hF.comp hG) i).trans
        (exactOriginalPrespectrumMapCompHomotopy W V U hF hG)) := by
  refine (originalPrespectrumTransformationCompositionHomotopy W U
    hH.rebase (hF.comp hG).rebase (hF.rebase.comp hG.rebase)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    ((congrArg (CategoryTheory.rebaseFunctor G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero)).obj
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).trans
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
    (normalizedWeakTransformation hH (hF.comp hG) i.hom)
    (exactNormalizationCompIso hF hG).hom
    (normalizedWeakTransformation_weak hH (hF.comp hG) i.hom
      (fun _ ↦ U.weq_iso _ inferInstance))
    (fun _ ↦ U.weq_iso _ inferInstance)).ofLevels _ _ (fun _ ↦ rfl) ?_
  intro n
  apply Homotopy.trans_level_congr
  · rfl
  · exact exactOriginalPrespectrumMapCompHomotopy_level hF hG n

/-- Every complete two-time level is the original transformation-composition triangle. -/
theorem exactNormalizationCompTrackComparison_level (i : H ≅ F ⋙ G) (n : ℕ) :
    ((exactNormalizationCompTrackComparison hH hF hG i).level n).toContinuousMap =
      ((originalPrespectrumTransformationCompositionHomotopy W U
        hH.rebase (hF.comp hG).rebase (hF.rebase.comp hG.rebase)
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
        ((congrArg (CategoryTheory.rebaseFunctor G V.zero U.zero
          ((hG.zero V.isZero).iso U.isZero)).obj
          (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).trans
          (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
        (normalizedWeakTransformation hH (hF.comp hG) i.hom)
        (exactNormalizationCompIso hF hG).hom
        (normalizedWeakTransformation_weak hH (hF.comp hG) i.hom
          (fun _ ↦ U.weq_iso _ inferInstance))
        (fun _ ↦ U.weq_iso _ inferInstance)).level n).toContinuousMap := rfl

end CategoryTheory.Waldhausen.IteratedS

namespace CategoryTheory.Waldhausen.IteratedS

/-- Source equality transport preserves the entire canonically normalized iso track. -/
theorem exactOriginalPrespectrumIsoHomotopy_eqToIso_trans_level
    {C E : Type u} [Category.{v} C] [Category.{v} E]
    (W : Structure C) (U : Structure E) {H H' K : C ⥤ E}
    (hH : IsExact W.cof W.weq U.cof U.weq H)
    (hH' : IsExact W.cof W.weq U.cof U.weq H')
    (hK : IsExact W.cof W.weq U.cof U.weq K)
    (e : H = H') (i : H' ≅ K) (n : ℕ) :
    (exactOriginalPrespectrumIsoHomotopy W U hH hK (eqToIso e ≪≫ i)).level n =
      (exactOriginalPrespectrumIsoHomotopy W U hH' hK i).level n := by
  cases e
  simp only [eqToIso_refl, Iso.refl_trans]

end CategoryTheory.Waldhausen.IteratedS
