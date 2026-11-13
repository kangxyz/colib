/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.MappingCofiber

import Colib.CategoryTheory.Sites.Simplicial.ReducedCylinderChains

/-!
# Monomorphisms from the original inclusion into a reduced cone

Evaluation in a simplex degree sends the native cone pushout to a
pushout of sets. Selecting the first vertex zero gives a retraction
of the evaluated inclusion. The two collapsed axes have the actual
basepoint as their value.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

open ReducedCylinderChains

variable {C : Type u} [Category.{v} C] (X : PointedSimplicialPresheaf.{w} C)

private abbrev simplexEval (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    (Cᵒᵖ ⥤ SSet.{w}) ⥤ Type w :=
  (CategoryTheory.evaluation _ _).obj U ⋙ (CategoryTheory.evaluation _ _).obj n

private theorem mono_simplexEval_map_reducedConeInclusion
    (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    Mono ((simplexEval U n).map (reducedConeInclusion X).right) := by
  let I := interval.{w} C
  let E := simplexEval U n
  let b := basepointSimplex C X n U
  let a : X.right ⨿ I ⟶ X.right ⨯ I := Under.axesToProduct X (basedInterval C)
  let q : X.right ⨯ I ⟶ (reducedCone X).right := Under.toSmash X (basedInterval C)
  let p := E.map X.hom
  let g : E.obj (X.right ⨯ I) ⟶ E.obj X.right :=
    ↾fun z => if SSet.stdSimplex.asOrderHom
      (((prod.snd : X.right ⨯ I ⟶ I).app U).app n z) 0 = 0 then
      ((prod.fst : X.right ⨯ I ⟶ X.right).app U).app n z
    else b
  let : Unique (E.obj (⊤_ (Cᵒᵖ ⥤ SSet.{w}))) := terminalSimplexUnique C n U
  have hp {Z : Cᵒᵖ ⥤ SSet.{w}} (z : E.obj Z) :
      p (E.map (terminal.from Z) z) = b :=
    congrArg (fun y => p y) (Subsingleton.elim _ _)
  have h : E.map a ≫ g = E.map (terminal.from (X.right ⨿ I)) ≫ p := by
    apply BinaryCofan.IsColimit.hom_ext
      (isColimitOfHasBinaryCoproductOfPreservesColimit E X.right I)
    · change E.map (coprod.inl : X.right ⟶ X.right ⨿ I) ≫ E.map a ≫ g =
        E.map (coprod.inl : X.right ⟶ X.right ⨿ I) ≫
          E.map (terminal.from (X.right ⨿ I)) ≫ p
      rw [← E.map_comp_assoc, ← E.map_comp_assoc, terminal.comp_from]
      have ha : (coprod.inl : X.right ⟶ X.right ⨿ I) ≫ a = productSection X (0 : Fin 2) :=
        coprod.inl_desc _ _
      rw [ha]
      apply ConcreteCategory.hom_ext
      intro x
      change (if SSet.stdSimplex.asOrderHom
        (((prod.snd : X.right ⨯ I ⟶ I).app U).app n
          (((productSection X (0 : Fin 2)).app U).app n x)) 0 = 0 then _ else b) =
        p (E.map (terminal.from X.right) x)
      rw [productSection_snd_apply, endpoint_one_firstVertex,
        ite_eq_right (by decide : (1 : Fin 2) ≠ 0), hp]
    · change E.map (coprod.inr : I ⟶ X.right ⨿ I) ≫ E.map a ≫ g =
        E.map (coprod.inr : I ⟶ X.right ⨿ I) ≫ E.map (terminal.from (X.right ⨿ I)) ≫ p
      rw [← E.map_comp_assoc, ← E.map_comp_assoc, terminal.comp_from]
      have ha : (coprod.inr : I ⟶ X.right ⨿ I) ≫ a = intervalAxis X I :=
        coprod.inr_desc _ _
      rw [ha]
      apply ConcreteCategory.hom_ext
      intro x
      change (if SSet.stdSimplex.asOrderHom
        (((prod.snd : X.right ⨯ I ⟶ I).app U).app n
          (((intervalAxis X I).app U).app n x)) 0 = 0 then
        ((prod.fst : X.right ⨯ I ⟶ X.right).app U).app n
          (((intervalAxis X I).app U).app n x) else b) =
        p (E.map (terminal.from I) x)
      rw [intervalAxis_fst_apply, ite_self, hp]
  let sq : IsPushout (E.map a) (E.map (terminal.from (X.right ⨿ I)))
      (E.map q) (E.map (reducedCone X).hom) :=
    E.map_isPushout (ReducedConeContraction.isPushout X)
  let r := sq.desc g p h
  have hi : E.map (reducedConeInclusion X).right ≫ r = 𝟙 _ := by
    change E.map (productSection X (1 : Fin 2) ≫ q) ≫ r = 𝟙 _
    rw [E.map_comp, Category.assoc, sq.inl_desc]
    apply ConcreteCategory.hom_ext
    intro x
    change (if SSet.stdSimplex.asOrderHom
      (((prod.snd : X.right ⨯ I ⟶ I).app U).app n
        (((productSection X (1 : Fin 2)).app U).app n x)) 0 = 0 then
      ((prod.fst : X.right ⨯ I ⟶ X.right).app U).app n
        (((productSection X (1 : Fin 2)).app U).app n x) else b) = x
    rw [productSection_snd_apply, endpoint_zero_firstVertex, ite_eq_left rfl,
      productSection_fst_apply]
  exact mono_of_mono_fac hi

/-- The actual inclusion at vertex zero of the reduced cone is monomorphic. -/
theorem mono_reducedConeInclusion_right :
    Mono (reducedConeInclusion X).right := by
  apply (NatTrans.mono_iff_mono_app _).2
  intro U
  apply (NatTrans.mono_iff_mono_app _).2
  intro n
  exact mono_simplexEval_map_reducedConeInclusion X U n

end CategoryTheory.PointedSimplicialPresheaf
