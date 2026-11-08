/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.KTheory.Waldhausen.Iterated.NormalizationNaturality
public import Colib.KTheory.Waldhausen.Iterated.ExactPastingHomotopy
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopyNaturality

/-!
# Actual relative pasting for binary normalization squares

These comparisons use the original zero-preserving transformation tracks. In particular they
introduce no second normalization of the already normalized functors. The binary squares are
proved categorical equalities; their relative realization is supplied by the actual triangles.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/NormalizationPasting.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology SSet CategoryTheory.Functor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
universe u v
namespace CategoryTheory.Waldhausen.IteratedS


/-- The literal source-equality transport in the existing original pasting. -/
def originalPastingTransport {E F : Topology.LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H H' K : Topology.LoopPrespectrum.Homotopy f g} (e : H = H') (J : H.RelHomotopy K) :
    H'.RelHomotopy K := (congrArg (fun A ↦ A.RelHomotopy K) e).mp J

/-- Full value agreement with every certificate of the very same original type equality. -/
theorem originalPastingTransport_eq_original {E F : Topology.LoopPrespectrum.{u}}
    {f g : E ⟶ F} {H H' K : Topology.LoopPrespectrum.Homotopy f g}
    (e : H = H') (J : H.RelHomotopy K) (p : H.RelHomotopy K = H'.RelHomotopy K) :
    originalPastingTransport e J = p.mp J := by
  subst H'
  rfl

/-- The named original source transport preserves the full two-time continuous map. -/
theorem originalPastingTransport_level {E F : Topology.LoopPrespectrum.{u}}
    {f g : E ⟶ F} {H H' K : Topology.LoopPrespectrum.Homotopy f g}
    (e : H = H') (J : H.RelHomotopy K) (n : ℕ) :
    ((originalPastingTransport e J).level n).toContinuousMap =
      (J.level n).toContinuousMap := by
  subst H'
  rfl

/-- The literal reversed relative concatenation used by original pasting. -/
def originalPastingSplice {E F : Topology.LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H K L : Topology.LoopPrespectrum.Homotopy f g}
    (J : K.RelHomotopy H) (J' : K.RelHomotopy L) : H.RelHomotopy L := J.symm.trans J'

/-- Full value equality to the unchanged native operation, for arbitrary actual arguments. -/
theorem originalPastingSplice_eq_original {E F : Topology.LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H K L : Topology.LoopPrespectrum.Homotopy f g}
    (J : K.RelHomotopy H) (J' : K.RelHomotopy L) :
    originalPastingSplice J J' = J.symm.trans J' := rfl

/-- Project only the stored right transport; the original dyadic parameters are literal. -/
theorem originalPastingSplice_replace_level {E F : Topology.LoopPrespectrum.{u}}
    {f g f' g' : E ⟶ F} {H K L : Topology.LoopPrespectrum.Homotopy f g}
    {H' K' : Topology.LoopPrespectrum.Homotopy f' g'}
    (J : K.RelHomotopy H) (J' : K.RelHomotopy L) (J'' : H'.RelHomotopy K') (n : ℕ)
    (e : (J'.level n).toContinuousMap = (J''.level n).toContinuousMap)
    (r s : unitInterval) (x : E.space n) :
    (originalPastingSplice J J').level n (r, (s, x)) =
      if hr : (r : ℝ) ≤ 1 / 2 then
        J.level n (unitInterval.symm ⟨2 * r, (unitInterval.mul_pos_mem_iff zero_lt_two).2
          ⟨r.2.1, hr⟩⟩, (s, x))
      else J''.level n (⟨2 * r - 1, unitInterval.two_mul_sub_one_mem_iff.2
        ⟨(not_le.1 hr).le, r.2.2⟩⟩, (s, x)) := by
  change ((J.level n).symm.trans (J'.level n)) (r, (s, x)) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · rfl
  · exact DFunLike.congr_fun e _

section Original
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F G G' H : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)
  (hG' : IsExact W.cof W.weq V.cof V.weq G')
  (hH : IsExact W.cof W.weq V.cof V.weq H)

/-- Equal composites compare the original based tracks, without an additional normalization. -/
def originalPrespectrumPastingHomotopy
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (h0G' : G'.obj W.zero = V.zero) (h0H : H.obj W.zero = V.zero)
    (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
    (hcomp : η ≫ θ = η' ≫ θ') :
    ((originalPrespectrumTransformationHomotopy W V hF hG h0F h0G η hη).trans
      (originalPrespectrumTransformationHomotopy W V hG hH h0G h0H θ hθ)).RelHomotopy
      ((originalPrespectrumTransformationHomotopy W V hF hG' h0F h0G' η' hη').trans
        (originalPrespectrumTransformationHomotopy W V hG' hH h0G' h0H θ' hθ')) := by
  have he : originalPrespectrumTransformationHomotopy W V hF hH h0F h0H (η ≫ θ)
      (fun A ↦ V.weq.comp_mem _ _ (hη A) (hθ A)) =
    originalPrespectrumTransformationHomotopy W V hF hH h0F h0H (η' ≫ θ')
      (fun A ↦ V.weq.comp_mem _ _ (hη' A) (hθ' A)) := by
    congr 1
  have J := originalPrespectrumTransformationCompositionHomotopy W V hF hG' hH
    h0F h0G' h0H η' θ' hη' hθ'
  let J := originalPastingTransport he.symm J
  exact originalPastingSplice
    (originalPrespectrumTransformationCompositionHomotopy W V hF hG hH
      h0F h0G h0H η θ hη hθ) J
end Original

section Binary
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {V : Structure D} {U : Structure E}

/-- In the original universes, postwhiskering preserves the complete based homotopy track. -/
theorem originalPrespectrumTransformationHomotopy_postcomp_level
    {F F' : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hF' : IsExact W.cof W.weq V.cof V.weq F')
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (h0F : F.obj W.zero = V.zero) (h0F' : F'.obj W.zero = V.zero)
    (h0G : G.obj V.zero = U.zero) (η : F ⟶ F')
    (hη : ∀ A, V.weq (η.app A)) (n : ℕ) :
    (originalPrespectrumTransformationHomotopy W U (hF.comp hG) (hF'.comp hG)
      ((congrArg G.obj h0F).trans h0G) ((congrArg G.obj h0F').trans h0G)
      (whiskerRight η G) (fun A ↦ hG.weak _ (hη A))).level n =
      ((originalPrespectrumTransformationHomotopy W V hF hF' h0F h0F' η hη).postcomp
        (originalPrespectrumMap V U hG h0G)).level n := by
  exact prespectrumTransformationHomotopy_postcomp_level
    (F := asSmallCategoryMap W V hF h0F) (G := asSmallCategoryMap W V hF' h0F')
    (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (fun A ↦ hη (AsSmall.down.obj A)) (asSmallCategoryMap V U hG h0G) n

/-- In the original universes, prewhiskering preserves the complete based homotopy track. -/
theorem originalPrespectrumTransformationHomotopy_precomp_level
    {F : C ⥤ D} {G G' : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (hG' : IsExact V.cof V.weq U.cof U.weq G')
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj V.zero = U.zero)
    (h0G' : G'.obj V.zero = U.zero) (θ : G ⟶ G')
    (hθ : ∀ A, U.weq (θ.app A)) (n : ℕ) :
    (originalPrespectrumTransformationHomotopy W U (hF.comp hG) (hF.comp hG')
      ((congrArg G.obj h0F).trans h0G) ((congrArg G'.obj h0F).trans h0G')
      (whiskerLeft F θ) (fun A ↦ hθ (F.obj A))).level n =
      (Topology.LoopPrespectrum.Homotopy.precomp (originalPrespectrumMap W V hF h0F)
        (originalPrespectrumTransformationHomotopy V U hG hG' h0G h0G' θ hθ)).level n := by
  exact prespectrumTransformationHomotopy_precomp_level
    (F := asSmallCategoryMap V U hG h0G) (G := asSmallCategoryMap V U hG' h0G')
    (whiskerLeft AsSmall.down (whiskerRight θ AsSmall.up))
    (fun A ↦ hθ (AsSmall.down.obj A)) (asSmallCategoryMap W V hF h0F) n

/-- The original first-factor normalization square has an actual whole relative pasting.
Its first route normalizes the whiskered transformation and then compares composites; its second
route compares composites and then postwhiskers the normalized transformation. -/
def exactNormalizationLeftPasting {F F' : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hF' : IsExact W.cof W.weq V.cof V.weq F')
    (hG : IsExact V.cof V.weq U.cof U.weq G) (η : F ⟶ F')
    (hη : ∀ A, V.weq (η.app A)) :=
  originalPrespectrumPastingHomotopy W U
    (hF.comp hG).rebase (hF'.comp hG).rebase
    (hF.rebase.comp hG.rebase) (hF'.rebase.comp hG.rebase)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    ((congrArg (CategoryTheory.rebaseFunctor G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero)).obj
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).trans
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
    ((congrArg (CategoryTheory.rebaseFunctor G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero)).obj
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).trans
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
    (normalizedWeakTransformation (hF.comp hG) (hF'.comp hG) (whiskerRight η G))
    (exactNormalizationCompIso hF' hG).hom
    (exactNormalizationCompIso hF hG).hom
    (whiskerRight (normalizedWeakTransformation hF hF' η)
      (CategoryTheory.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero)))
    (normalizedWeakTransformation_weak _ _ _ (fun A ↦ hG.weak _ (hη A)))
    (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
    (fun A ↦ hG.rebase.weak _ (normalizedWeakTransformation_weak hF hF' η hη A))
    (exactNormalizationCompIso_natural_left hF hF' hG η)

/-- The original second-factor normalization square has an actual whole relative pasting.
Both routes retain the original normalized transformation and the actual binary comparison. -/
def exactNormalizationRightPasting {F : C ⥤ D} {G G' : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (hG' : IsExact V.cof V.weq U.cof U.weq G') (θ : G ⟶ G')
    (hθ : ∀ A, U.weq (θ.app A)) :=
  originalPrespectrumPastingHomotopy W U
    (hF.comp hG).rebase (hF.comp hG').rebase
    (hF.rebase.comp hG.rebase) (hF.rebase.comp hG'.rebase)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    ((congrArg (CategoryTheory.rebaseFunctor G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero)).obj
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).trans
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
    ((congrArg (CategoryTheory.rebaseFunctor G' V.zero U.zero
      ((hG'.zero V.isZero).iso U.isZero)).obj
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).trans
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
    (normalizedWeakTransformation (hF.comp hG) (hF.comp hG') (whiskerLeft F θ))
    (exactNormalizationCompIso hF hG').hom
    (exactNormalizationCompIso hF hG).hom
    (whiskerLeft (CategoryTheory.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero))
      (normalizedWeakTransformation hG hG' θ))
    (normalizedWeakTransformation_weak _ _ _ (fun A ↦ hθ (F.obj A)))
    (fun _ ↦ U.weq_iso _ inferInstance) (fun _ ↦ U.weq_iso _ inferInstance)
    (fun _A ↦ normalizedWeakTransformation_weak hG hG' θ hθ _)
    (exactNormalizationCompIso_natural_right hF hG hG' θ)
end Binary

end CategoryTheory.Waldhausen.IteratedS

namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy
private theorem pasting_transport_projection {E F : LoopPrespectrum.{u}} {f g : E ⟶ F}
    {H H' K : Homotopy f g} (e : H = H')
    (p : H.RelHomotopy K = H'.RelHomotopy K) (J : H.RelHomotopy K) (n : ℕ) :
    ((p.mp J).level n).toContinuousMap = (J.level n).toContinuousMap := by
  subst H'
  rfl
end Topology.LoopPrespectrum.Homotopy.RelHomotopy

namespace CategoryTheory.Waldhausen.IteratedS
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F G G' H : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)
  (hG' : IsExact W.cof W.weq V.cof V.weq G')
  (hH : IsExact W.cof W.weq V.cof V.weq H)
  (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
  (h0G' : G'.obj W.zero = V.zero) (h0H : H.obj W.zero = V.zero)
  (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
  (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
  (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
  (hcomp : η ≫ θ = η' ≫ θ')

/-- Projection through the native pasting's stored initial-track transport. -/
theorem originalPrespectrumPastingHomotopy_whole_level (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum W).space n) :
    (originalPrespectrumPastingHomotopy W V hF hG hG' hH h0F h0G h0G' h0H
      η θ η' θ' hη hθ hη' hθ' hcomp).level n (r, (s, x)) =
      if hr : (r : ℝ) ≤ 1 / 2 then
        (originalPrespectrumTransformationCompositionHomotopy W V hF hG hH
          h0F h0G h0H η θ hη hθ).level n
          (unitInterval.symm ⟨2 * r,
            (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨r.2.1, hr⟩⟩, (s, x))
      else
        (originalPrespectrumTransformationCompositionHomotopy W V hF hG' hH
          h0F h0G' h0H η' θ' hη' hθ').level n
          (⟨2 * r - 1, unitInterval.two_mul_sub_one_mem_iff.2
            ⟨(not_le.1 hr).le, r.2.2⟩⟩, (s, x)) := by
  unfold originalPrespectrumPastingHomotopy
  apply originalPastingSplice_replace_level
  exact originalPastingTransport_level _ _ _

end CategoryTheory.Waldhausen.IteratedS

-- COL-0324 references
attribute [colib_ref "quillen"
  "Iterated/NormalizationPasting.lean:1-259"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  CategoryTheory.Waldhausen.IteratedS.originalPastingTransport
  CategoryTheory.Waldhausen.IteratedS.originalPastingTransport_eq_original
  CategoryTheory.Waldhausen.IteratedS.originalPastingTransport_level
  CategoryTheory.Waldhausen.IteratedS.originalPastingSplice
  CategoryTheory.Waldhausen.IteratedS.originalPastingSplice_eq_original
  CategoryTheory.Waldhausen.IteratedS.originalPastingSplice_replace_level
  CategoryTheory.Waldhausen.IteratedS.originalPrespectrumPastingHomotopy
  CategoryTheory.Waldhausen.IteratedS.originalPrespectrumTransformationHomotopy_postcomp_level
  CategoryTheory.Waldhausen.IteratedS.originalPrespectrumTransformationHomotopy_precomp_level
  CategoryTheory.Waldhausen.IteratedS.exactNormalizationLeftPasting
  CategoryTheory.Waldhausen.IteratedS.exactNormalizationRightPasting
  CategoryTheory.Waldhausen.IteratedS.originalPrespectrumPastingHomotopy_whole_level
