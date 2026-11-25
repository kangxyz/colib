/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.UnitPrismParameters
public import Colib.KTheory.Waldhausen.Iterated.NormalizationTrackPasting
public import Colib.KTheory.Waldhausen.Iterated.SimplexTriangleLift

/-!
# Whole original pasting lifts on the six-reference unit prism

These abstract helpers preserve the stored source equality transport of the exact composition
triangle and the original two triangle halves. Native clients must supply their actual complete
normalized faces; no native lift or geometric commuting equation is assumed by those clients.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Convexity
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.UnitPrismOriginalPastingLift

open SmallWaldhausenCategory
private theorem id_mpr_heq {A B : Sort u} (p : A = B) (x : B) :
    HEq (id (p.mpr x)) x := by
  cases p
  rfl

private def originalPastingTemplate {E F : Topology.LoopPrespectrum.{u}} {f g : E ⟶ F}
    {A B C D : Homotopy f g} (e : A = B)
    (J : A.RelHomotopy C) (K : B.RelHomotopy D) : C.RelHomotopy D :=
  J.symm.trans ((congrArg (fun H ↦ H.RelHomotopy D) e.symm).mp K)

private theorem originalPastingTemplate_lift {V W : WideSubcategory preservesZero.{u}}
    (S : ModelSimplex V W 5) {f g : prespectrum V ⟶ prespectrum W}
    {A B C D : Homotopy f g} (e : A = B) (J : A.RelHomotopy C) (K : B.RelHomotopy D)
    (hJ : HomotopyLift S (triangle UnitPrismNodes.geometricFirst) J)
    (hK : HomotopyLift S (triangle UnitPrismNodes.geometricSecond) K) :
    HomotopyLift S UnitPrismParameters.geometric (originalPastingTemplate e J K) := by
  have hK' : HomotopyLift S (triangle UnitPrismNodes.geometricSecond)
      ((congrArg (fun H ↦ H.RelHomotopy D) e.symm).mp K) := by
    subst B
    exact hK
  exact HomotopyLift.trans S (HomotopyLift.symm S hJ) hK'

private theorem homotopyLift_of_apply {V W : WideSubcategory preservesZero.{u}}
    (S : ModelSimplex V W 5)
    {a b : StdSimplex ℝ (Fin 6)} {p q : Path a b} (P : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g} (J : H.RelHomotopy K)
    (h : ∀ n r s x, prespectrumSimplexFamily S n (P (r, s), x) =
      J.level n (r, (s, x))) : HomotopyLift S P J := h

private theorem homotopyLift_heq {V W : WideSubcategory preservesZero.{u}} (S : ModelSimplex V W 5)
    {a b : StdSimplex ℝ (Fin 6)} {p q : Path a b} (P : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H H' K : Homotopy f g} (e : H = H')
    (J : H.RelHomotopy K) (J' : H'.RelHomotopy K) (hJ : HEq J' J)
    (h : HomotopyLift S P J) : HomotopyLift S P J' := by
  subst H'
  cases eq_of_heq hJ
  exact h

private theorem homotopyLift_eq {V W : WideSubcategory preservesZero.{u}} (S : ModelSimplex V W 5)
    {a b : StdSimplex ℝ (Fin 6)} {p q : Path a b} (P : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g}
    {J J' : H.RelHomotopy K} (e : J = J') (h : HomotopyLift S P J') :
    HomotopyLift S P J := by
  cases e
  exact h

section OriginalLevels
universe v
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Waldhausen.Structure C) (V : Waldhausen.Structure D) {F G G' H : C ⥤ D}
  (hF : Waldhausen.IsExact W.cof W.weq V.cof V.weq F)
  (hG : Waldhausen.IsExact W.cof W.weq V.cof V.weq G)
  (hG' : Waldhausen.IsExact W.cof W.weq V.cof V.weq G')
  (hH : Waldhausen.IsExact W.cof W.weq V.cof V.weq H)

private theorem exact_triangle_source_eq (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A)) :
    originalPrespectrumTransformationHomotopy W V hF.rebase hH.rebase
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
      (Waldhausen.normalizedWeakTransformation hF hG η ≫
        Waldhausen.normalizedWeakTransformation hG hH θ)
      (fun A ↦ V.weq.comp_mem _ _
        (Waldhausen.normalizedWeakTransformation_weak hF hG η hη A)
        (Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ A)) =
    exactOriginalPrespectrumHomotopy W V hF hH (η ≫ θ)
      (fun A ↦ V.weq.comp_mem _ _ (hη A) (hθ A)) := by
  have hcomp := normalizedWeakTransformation_comp W V hF hG hH η θ
  unfold exactOriginalPrespectrumHomotopy
  congr 1
  exact hcomp.symm

private theorem exact_triangle_heq (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A)) :
    HEq (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ)
    (originalPrespectrumTransformationCompositionHomotopy W V hF.rebase hG.rebase hH.rebase
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
      (Waldhausen.normalizedWeakTransformation hF hG η)
      (Waldhausen.normalizedWeakTransformation hG hH θ)
      (Waldhausen.normalizedWeakTransformation_weak hF hG η hη)
      (Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ)) := by
  unfold exactOriginalPrespectrumCompositionHomotopy
  exact id_mpr_heq _ _

private theorem exact_composite_track_eq
    (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
    (he : η ≫ θ = η' ≫ θ') :
    exactOriginalPrespectrumHomotopy W V hF hH (η ≫ θ)
      (fun A ↦ V.weq.comp_mem _ _ (hη A) (hθ A)) =
      exactOriginalPrespectrumHomotopy W V hF hH (η' ≫ θ')
        (fun A ↦ V.weq.comp_mem _ _ (hη' A) (hθ' A)) := by
  congr 1

private theorem exact_pasting_eq_template
    (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
    (he : η ≫ θ = η' ≫ θ') :
    exactOriginalPrespectrumPastingHomotopy W V hF hG hG' hH
      η θ η' θ' hη hθ hη' hθ' he =
    originalPastingTemplate (exact_composite_track_eq W V hF hH
      η θ η' θ' hη hθ hη' hθ' he)
      (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ)
      (exactOriginalPrespectrumCompositionHomotopy W V hF hG' hH η' θ' hη' hθ') := rfl

private theorem original_triangle_lift
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (h0H : H.obj W.zero = V.zero) (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (S : ModelSimplex (asSmallCategory W) (asSmallCategory V) 5) (α : ⦋2⦌ ⟶ ⦋5⦌)
    (hface : S.face α = ModelSimplex.triangle
      (F := asSmallCategoryMap W V hF h0F) (G := asSmallCategoryMap W V hG h0G)
      (H := asSmallCategoryMap W V hH h0H)
      (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
      (whiskerLeft AsSmall.down (whiskerRight θ AsSmall.up))
      (fun A ↦ hη (AsSmall.down.obj A)) (fun A ↦ hθ (AsSmall.down.obj A)))
    (n : ℕ) (r s : unitInterval) (x : (originalPrespectrum W).space n) :
    prespectrumSimplexFamily S n (triangle α (r, s), x) =
      (originalPrespectrumTransformationCompositionHomotopy W V hF hG hH
        h0F h0G h0H η θ hη hθ).level n (r, (s, x)) :=
  triangle_lift S α _ _ _ _ hface n r s x

private theorem normalized_triangle_lift_whole (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (S : ModelSimplex (asSmallCategory W) (asSmallCategory V) 5) (α : ⦋2⦌ ⟶ ⦋5⦌)
    (hface : S.face α = ModelSimplex.triangle
      (F := asSmallCategoryMap W V hF.rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
      (G := asSmallCategoryMap W V hG.rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
      (H := asSmallCategoryMap W V hH.rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
      (whiskerLeft AsSmall.down
        (whiskerRight (Waldhausen.normalizedWeakTransformation hF hG η) AsSmall.up))
      (whiskerLeft AsSmall.down
        (whiskerRight (Waldhausen.normalizedWeakTransformation hG hH θ) AsSmall.up))
      (fun A ↦ Waldhausen.normalizedWeakTransformation_weak hF hG η hη (AsSmall.down.obj A))
      (fun A ↦ Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ (AsSmall.down.obj A)))
    : HomotopyLift S (triangle α)
      (originalPrespectrumTransformationCompositionHomotopy W V hF.rebase hG.rebase hH.rebase
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
        (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
        (Waldhausen.normalizedWeakTransformation hF hG η)
        (Waldhausen.normalizedWeakTransformation hG hH θ)
        (Waldhausen.normalizedWeakTransformation_weak hF hG η hη)
        (Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ)) :=
  homotopyLift_of_apply S (triangle α) _
    (original_triangle_lift W V hF.rebase hG.rebase hH.rebase _ _ _
      (Waldhausen.normalizedWeakTransformation hF hG η)
      (Waldhausen.normalizedWeakTransformation hG hH θ)
      (Waldhausen.normalizedWeakTransformation_weak hF hG η hη)
      (Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ) S α hface)

/-- The whole exact original triangle is lifted from its actual normalized small-model face. -/
theorem exact_triangle_lift (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (S : ModelSimplex (asSmallCategory W) (asSmallCategory V) 5) (α : ⦋2⦌ ⟶ ⦋5⦌)
    (hface : S.face α = ModelSimplex.triangle
      (F := asSmallCategoryMap W V hF.rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
      (G := asSmallCategoryMap W V hG.rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
      (H := asSmallCategoryMap W V hH.rebase (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
      (whiskerLeft AsSmall.down
        (whiskerRight (Waldhausen.normalizedWeakTransformation hF hG η) AsSmall.up))
      (whiskerLeft AsSmall.down
        (whiskerRight (Waldhausen.normalizedWeakTransformation hG hH θ) AsSmall.up))
      (fun A ↦ Waldhausen.normalizedWeakTransformation_weak hF hG η hη (AsSmall.down.obj A))
      (fun A ↦ Waldhausen.normalizedWeakTransformation_weak hG hH θ hθ (AsSmall.down.obj A)))
    : HomotopyLift S (triangle α)
      (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ) :=
  homotopyLift_heq S (triangle α) (exact_triangle_source_eq W V hF hG hH η θ hη hθ)
    _ _ (exact_triangle_heq W V hF hG hH η θ hη hθ)
    (normalized_triangle_lift_whole W V hF hG hH η θ hη hθ S α hface)

/-- Both ordered normalization faces lift the complete original two-triangle pasting. -/
theorem normalization_original_lift
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (h0G' : G'.obj W.zero = V.zero) (h0H : H.obj W.zero = V.zero)
    (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
    (he : η ≫ θ = η' ≫ θ') (S : ModelSimplex (asSmallCategory W) (asSmallCategory V) 5)
    (hfirst : S.face UnitPrismNodes.normalizationFirst = ModelSimplex.triangle
      (F := asSmallCategoryMap W V hF h0F) (G := asSmallCategoryMap W V hG h0G)
      (H := asSmallCategoryMap W V hH h0H)
      (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
      (whiskerLeft AsSmall.down (whiskerRight θ AsSmall.up))
      (fun A ↦ hη (AsSmall.down.obj A)) (fun A ↦ hθ (AsSmall.down.obj A)))
    (hsecond : S.face UnitPrismNodes.normalizationSecond = ModelSimplex.triangle
      (F := asSmallCategoryMap W V hF h0F) (G := asSmallCategoryMap W V hG' h0G')
      (H := asSmallCategoryMap W V hH h0H)
      (whiskerLeft AsSmall.down (whiskerRight η' AsSmall.up))
      (whiskerLeft AsSmall.down (whiskerRight θ' AsSmall.up))
      (fun A ↦ hη' (AsSmall.down.obj A)) (fun A ↦ hθ' (AsSmall.down.obj A))) :
    HomotopyLift S UnitPrismParameters.normalization
      (originalPrespectrumPastingHomotopy W V hF hG hG' hH h0F h0G h0G' h0H
        η θ η' θ' hη hθ hη' hθ' he) := by
  intro n r s x
  have h := originalPrespectrumPastingHomotopy_whole_level W V hF hG hG' hH
    h0F h0G h0G' h0H η θ η' θ' hη hθ hη' hθ' he n r s x
  refine Eq.trans ?_ h.symm
  rw [UnitPrismParameters.normalization, Path.Homotopy.trans_apply]
  split
  · exact original_triangle_lift W V hF hG hH h0F h0G h0H η θ hη hθ S
      UnitPrismNodes.normalizationFirst hfirst n _ s x
  · exact original_triangle_lift W V hF hG' hH h0F h0G' h0H η' θ' hη' hθ' S
      UnitPrismNodes.normalizationSecond hsecond n _ s x

/-- Whole lifts of both actual exact triangles retain the original stored pasting transport. -/
theorem exact_pasting_lift
    (η : F ⟶ G) (θ : G ⟶ H) (η' : F ⟶ G') (θ' : G' ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A))
    (hη' : ∀ A, V.weq (η'.app A)) (hθ' : ∀ A, V.weq (θ'.app A))
    (he : η ≫ θ = η' ≫ θ') (S : ModelSimplex (asSmallCategory W) (asSmallCategory V) 5)
    (hfirst : HomotopyLift S (triangle UnitPrismNodes.geometricFirst)
      (exactOriginalPrespectrumCompositionHomotopy W V hF hG hH η θ hη hθ))
    (hsecond : HomotopyLift S (triangle UnitPrismNodes.geometricSecond)
      (exactOriginalPrespectrumCompositionHomotopy W V hF hG' hH η' θ' hη' hθ')) :
    HomotopyLift S UnitPrismParameters.geometric
      (exactOriginalPrespectrumPastingHomotopy W V hF hG hG' hH
        η θ η' θ' hη hθ hη' hθ' he) :=
  homotopyLift_eq S UnitPrismParameters.geometric
    (exact_pasting_eq_template W V hF hG hG' hH η θ η' θ' hη hθ hη' hθ' he)
    (originalPastingTemplate_lift S
      (exact_composite_track_eq W V hF hH η θ η' θ' hη hθ hη' hθ' he) _ _ hfirst hsecond)

end OriginalLevels

section NormalizationRight
universe v
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Waldhausen.Structure C} {V : Waldhausen.Structure D} {U : Waldhausen.Structure E}

/-- The original right-factor ofLevels wrapper preserves the whole lifted family. -/
theorem normalization_right_track_lift {F : C ⥤ D} {G G' : D ⥤ E}
    (hF : Waldhausen.IsExact W.cof W.weq V.cof V.weq F)
    (hG : Waldhausen.IsExact V.cof V.weq U.cof U.weq G)
    (hG' : Waldhausen.IsExact V.cof V.weq U.cof U.weq G') (θ : G ⟶ G')
    (hθ : ∀ A, U.weq (θ.app A)) (S : ModelSimplex (asSmallCategory W) (asSmallCategory U) 5)
    (h : HomotopyLift S UnitPrismParameters.normalization
      (exactNormalizationRightPasting hF hG hG' θ hθ)) :
    HomotopyLift S UnitPrismParameters.normalization
      (exactNormalizationRightTrackPasting hF hG hG' θ hθ) := by
  unfold exactNormalizationRightTrackPasting
  exact HomotopyLift.ofLevels S h _ _ _ _

/-- The original left-factor level wrapper retains all points of the lifted family. -/
theorem normalization_left_track_lift {F F' : C ⥤ D} {G : D ⥤ E}
    (hF : Waldhausen.IsExact W.cof W.weq V.cof V.weq F)
    (hF' : Waldhausen.IsExact W.cof W.weq V.cof V.weq F')
    (hG : Waldhausen.IsExact V.cof V.weq U.cof U.weq G) (η : F ⟶ F')
    (hη : ∀ A, V.weq (η.app A)) (S : ModelSimplex (asSmallCategory W) (asSmallCategory U) 5)
    (h : HomotopyLift S UnitPrismParameters.normalization
      (exactNormalizationLeftPasting hF hF' hG η hη)) :
    HomotopyLift S UnitPrismParameters.normalization
      (exactNormalizationLeftTrackPasting hF hF' hG η hη) := by
  unfold exactNormalizationLeftTrackPasting
  exact HomotopyLift.ofLevels S h _ _ _ _

end NormalizationRight
end CategoryTheory.Waldhausen.IteratedS.UnitPrismOriginalPastingLift
