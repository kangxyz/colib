/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ReducedHypercohomology
public import Colib.CategoryTheory.Sites.Simplicial.UniverseLift

import Colib.CategoryTheory.Sites.Simplicial.AbelianPresheaf
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Reduced cochains of a pointed collapse pushout

A monomorphic inclusion collapsed to a point gives a short exact sequence
of the original reduced cochains. The comparison uses reduced free
abelianization, the chosen sheafification and Dold–Kan normalization.
Extension to nonpositive cochain degrees preserves exactness degreewise.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w' w v u

namespace CategoryTheory.PointedSimplicialPresheaf

private theorem shortExact_map_extendFunctor {A : Type u} [Category.{v} A] [Abelian A]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (S : ShortComplex (HomologicalComplex A c)) (hS : S.ShortExact) :
    (S.map (e.extendFunctor A)).ShortExact := by
  apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).2
  intro j
  change (S.map (e.extendFunctor A ⋙ HomologicalComplex.eval A c' j)).ShortExact
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj
    exact (ShortComplex.shortExact_iff_of_iso
      (S.mapNatIso (e.extendFunctorCompEvalIso A hi))).2
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS i)
  · have h (i : ι) : e.f i ≠ j := fun hi => hj ⟨i, hi⟩
    exact
      { mono_f := (S.X₁.isZero_extend_X e j h).mono _
        epi_g := (S.X₃.isZero_extend_X e j h).epi _
        exact := ShortComplex.exact_of_isZero_X₂ _ (S.X₂.isZero_extend_X e j h) }

private theorem shortExact_of_isPushout_of_isZero {A : Type u} [Category.{v} A] [Abelian A]
    {X Y Z W : A} {i : X ⟶ Y} {l : X ⟶ Z} {q : Y ⟶ W} {r : Z ⟶ W}
    (sq : IsPushout i l q r) (hZ : IsZero Z) [Mono i] (w : i ≫ q = 0) :
    (ShortComplex.mk i q w).ShortExact := by
  have hq : IsColimit (CokernelCofork.ofπ q w) := by
    refine CokernelCofork.IsColimit.ofπ q w
      (fun a ha => sq.desc a 0 (by simpa only [comp_zero] using ha))
      (fun _ _ => sq.inl_desc _ _ _) ?_
    intro T a ha g hg
    exact sq.hom_ext (hg.trans (sq.inl_desc _ _ _).symm) (hZ.eq_of_src _ _)
  exact
    { mono_f := inferInstance
      epi_g := ⟨fun _ _ h => Cofork.IsColimit.hom_ext hq h⟩
      exact := ShortComplex.exact_of_g_is_cokernel _ hq }

variable {C : Type u} [Category.{v} C]

/-- Reduced free abelianization preserves a map whose underlying pointed
presheaf morphism is a monomorphism. -/
theorem mono_reducedFreeAbelian_map_of_mono_right {X Y : PointedSimplicialPresheaf.{w} C}
    (f : X ⟶ Y) [Mono f.right] : Mono ((reducedFreeAbelian C).map f) := by
  let F := freeAbelian.{w} C
  let : F.PreservesMonomorphisms := by
    dsimp only [F, freeAbelian]
    infer_instance
  let : Mono (F.map f.right) := F.map_mono f.right
  have sq : IsPullback (F.map X.hom) (𝟙 _) (F.map f.right) (F.map Y.hom) :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, ← F.map_comp, Under.w f]⟩
  change Mono (cokernel.map (F.map X.hom) (F.map Y.hom) (𝟙 _) (F.map f.right) sq.w)
  exact Abelian.mono_cokernel_map_of_isPullback sq

section Sheafification

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{w}]

private theorem sheafifiedReducedChains_isLeftAdjoint :
    (sheafifiedReducedChains.{w} C J).IsLeftAdjoint := by
  let A := Sheaf J AddCommGrpCat.{w}
  let R := reducedFreeAbelian.{w} C
  let G := (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj
    (presheafToSheaf J AddCommGrpCat.{w})
  let N := (CategoryTheory.Abelian.DoldKan.equivalence (A := A)).functor
  let : R.IsLeftAdjoint := (reducedFreeForgetAdjunction C).isLeftAdjoint
  let : G.IsLeftAdjoint :=
    ((sheafificationAdjunction J AddCommGrpCat.{w}).whiskerRight SimplexCategoryᵒᵖ).isLeftAdjoint
  change (R ⋙ G ⋙ N).IsLeftAdjoint
  infer_instance

/-- Reduced cochains of a zero pointed presheaf form a zero complex. -/
theorem isZero_reducedCochains_obj_of_isZero (X : PointedSimplicialPresheaf.{w} C)
    (hX : IsZero X) : IsZero ((reducedCochains C J).obj X) := by
  let A := Sheaf J AddCommGrpCat.{w}
  let F := sheafifiedReducedChains.{w} C J
  let E := (ComplexShape.embeddingUpIntLE 0).extendFunctor A
  let : F.IsLeftAdjoint := sheafifiedReducedChains_isLeftAdjoint J
  exact E.map_isZero ((hX.isInitial.isInitialObj F _).isZero)

/-- The two actual reduced-cochain maps of a pointed collapse pushout
are the maps of a short exact sequence. -/
theorem exists_reducedCochains_shortExact_of_isPushout_isZero
    {X Y Z W : PointedSimplicialPresheaf.{w} C}
    {i : X ⟶ Y} {l : X ⟶ Z} {q : Y ⟶ W} {r : Z ⟶ W}
    (sq : IsPushout i l q r) (hZ : IsZero Z) [Mono i.right] :
    ∃ h : (reducedCochains C J).map i ≫ (reducedCochains C J).map q = 0,
      (ShortComplex.mk ((reducedCochains C J).map i)
        ((reducedCochains C J).map q) h).ShortExact := by
  let A := Sheaf J AddCommGrpCat.{w}
  let R := reducedFreeAbelian.{w} C
  let G := (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj
    (presheafToSheaf J AddCommGrpCat.{w})
  let N := (CategoryTheory.Abelian.DoldKan.equivalence (A := A)).functor
  let F := R ⋙ G ⋙ N
  let : F.IsLeftAdjoint := sheafifiedReducedChains_isLeftAdjoint J
  let : Mono (R.map i) := mono_reducedFreeAbelian_map_of_mono_right i
  let : G.PreservesMonomorphisms := by
    dsimp only [G]
    infer_instance
  let : Mono (F.map i) := N.map_mono (G.map (R.map i))
  let hF : PreservesColimitsOfShape WalkingSpan F :=
    (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits.preservesColimitsOfShape
  let : PreservesColimit (span i l) F := hF.preservesColimit
  let sqF := F.map_isPushout sq
  have h0 : IsZero (F.obj Z) := (hZ.isInitial.isInitialObj F _).isZero
  have hz : F.map i ≫ F.map q = 0 := by
    rw [sqF.w, h0.eq_of_tgt (F.map l) 0, zero_comp]
  let T := ShortComplex.mk (F.map i) (F.map q) hz
  have hT : T.ShortExact := shortExact_of_isPushout_of_isZero sqF h0 hz
  let e := ComplexShape.embeddingUpIntLE 0
  let S := T.map (e.extendFunctor A)
  exact ⟨S.zero, shortExact_map_extendFunctor e T hT⟩

end Sheafification

/-- The original universe lift preserves pointed pushout squares. -/
theorem uliftPointed_map_isPushout
    {X Y Z W : PointedSimplicialPresheaf.{w} C}
    {i : X ⟶ Y} {l : X ⟶ Z} {q : Y ⟶ W} {r : Z ⟶ W}
    (sq : IsPushout i l q r) :
    IsPushout ((uliftPointed.{w', w} C).map i) ((uliftPointed.{w', w} C).map l)
      ((uliftPointed.{w', w} C).map q) ((uliftPointed.{w', w} C).map r) := by
  let F := uliftPresheaf.{w', w} C
  let : PreservesFiniteColimits F := by
    dsimp only [F, uliftPresheaf, SSet.uliftFunctor]
    exact ⟨fun _ _ _ => inferInstance⟩
  let : PreservesColimitsOfShape WalkingSpan (uliftPointed.{w', w} C) := by
    dsimp only [uliftPointed]
    infer_instance
  exact (uliftPointed.{w', w} C).map_isPushout sq

/-- Universe lift preserves a monomorphism of underlying presheaves. -/
theorem mono_uliftPointed_map_right
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y) [Mono f.right] :
    Mono ((uliftPointed.{w', w} C).map f).right := by
  let F := uliftPresheaf.{w', w} C
  let : PreservesFiniteLimits F := by
    dsimp only [F, uliftPresheaf, SSet.uliftFunctor]
    exact ⟨fun _ _ _ => inferInstance⟩
  exact preserves_mono_of_preservesLimit F f.right

/-- The original lifted point is a zero object in the lifted pointed category. -/
theorem isZero_uliftPointed_point :
    IsZero ((uliftPointed.{w', w} C).obj (point.{w} C)) := by
  let e := uliftPresheafTerminalIso.{w', w} C
  have he : ((uliftPointed.{w', w} C).obj (point.{w} C)).hom ≫ e.hom =
      (point.{max w w'} C).hom := by
    simp only [uliftPointed_obj_hom, point, Under.mk_hom, Functor.map_id, Category.comp_id]
    exact e.inv_hom_id
  exact (point_isZero.{max w w'} C).of_iso (Under.isoMk e he)

end CategoryTheory.PointedSimplicialPresheaf
