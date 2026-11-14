/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ReducedChains
public import StacksFrontier.CategoryTheory.Sites.PresheafTensorFunctor
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Free abelianization of products of simplicial presheaves

A free generator on the chosen product is sent to the pure tensor
of its two projected generators. The comparison uses the integral tensor
product and respects both the site and simplicial variables.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct CategoryTheory.MonoidalCategory

attribute [local instance] AddCommGrpCat.monoidalCategory

universe u v w

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]


private abbrev evaluateSimplex (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    (Cᵒᵖ ⥤ SSet.{w + 1}) ⥤ Type (w + 1) :=
  (CategoryTheory.evaluation Cᵒᵖ SSet.{w + 1}).obj U ⋙
    (CategoryTheory.evaluation SimplexCategoryᵒᵖ (Type (w + 1))).obj n

private def productCoordinates (X Y : Cᵒᵖ ⥤ SSet.{w + 1}) (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    ((X ⨯ Y).obj U).obj n ≃ (X.obj U).obj n × (Y.obj U).obj n :=
  ((PreservesLimitPair.iso (evaluateSimplex U n) X Y) ≪≫ Types.binaryProductIso _ _).toEquiv

private theorem productCoordinates_fst (X Y : Cᵒᵖ ⥤ SSet.{w + 1})
    (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (z : ((X ⨯ Y).obj U).obj n) :
    (productCoordinates X Y U n z).1 = ((prod.fst : X ⨯ Y ⟶ X).app U).app n z := by
  have h : ((PreservesLimitPair.iso (evaluateSimplex U n) X Y) ≪≫ Types.binaryProductIso _ _).hom ≫
      ↾_root_.Prod.fst = (evaluateSimplex U n).map prod.fst := by
    simp only [Iso.trans_hom, Category.assoc, Types.binaryProductIso_hom_comp_fst,
      PreservesLimitPair.iso_hom, prodComparison_fst]
  exact ConcreteCategory.congr_hom h z

private theorem productCoordinates_snd (X Y : Cᵒᵖ ⥤ SSet.{w + 1})
    (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (z : ((X ⨯ Y).obj U).obj n) :
    (productCoordinates X Y U n z).2 = ((prod.snd : X ⨯ Y ⟶ Y).app U).app n z := by
  have h : ((PreservesLimitPair.iso (evaluateSimplex U n) X Y) ≪≫ Types.binaryProductIso _ _).hom ≫
      ↾_root_.Prod.snd = (evaluateSimplex U n).map prod.snd := by
    simp only [Iso.trans_hom, Category.assoc, Types.binaryProductIso_hom_comp_snd,
      PreservesLimitPair.iso_hom, prodComparison_snd]
  exact ConcreteCategory.congr_hom h z

private def tensorApp (X Y : Cᵒᵖ ⥤ SSet.{w + 1}) (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) :
    (((freeAbelian.{w + 1} C).obj (X ⨯ Y)).obj n).obj U ≅
      (AddCommGrpCat.presheafTensor (((freeAbelian.{w + 1} C).obj X).obj n)
        (((freeAbelian.{w + 1} C).obj Y).obj n)).obj U :=
  ((FreeAbelianGroup.equivOfEquiv (productCoordinates X Y U n)).trans
    (AddCommGrpCat.freeProdTensorEquiv _ _).symm).toAddCommGrpIso

private theorem tensorApp_hom_of (X Y : Cᵒᵖ ⥤ SSet.{w + 1})
    (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (z : ((X ⨯ Y).obj U).obj n) :
    (tensorApp X Y U n).hom (FreeAbelianGroup.of z) =
      FreeAbelianGroup.of (((prod.fst : X ⨯ Y ⟶ X).app U).app n z) ⊗ₜ[ℤ]
      FreeAbelianGroup.of (((prod.snd : X ⨯ Y ⟶ Y).app U).app n z) := by
  change AddCommGrpCat.freeProdTensorBackward _ _
    (FreeAbelianGroup.map (productCoordinates X Y U n) (FreeAbelianGroup.of z)) = _
  rw [FreeAbelianGroup.map_of_apply, AddCommGrpCat.freeProdTensorBackward_of,
    productCoordinates_fst, productCoordinates_snd]

private theorem tensorApp_naturality {X Y X' Y' : Cᵒᵖ ⥤ SSet.{w + 1}}
    {U U' : Cᵒᵖ} {n n' : SimplexCategoryᵒᵖ}
    (f : (X.obj U).obj n ⟶ (X'.obj U').obj n')
    (g : (Y.obj U).obj n ⟶ (Y'.obj U').obj n')
    (h : ((X ⨯ Y).obj U).obj n ⟶ ((X' ⨯ Y').obj U').obj n')
    (hf : ∀ z, ((prod.fst : X' ⨯ Y' ⟶ X').app U').app n' (h z) =
      f (((prod.fst : X ⨯ Y ⟶ X).app U).app n z))
    (hg : ∀ z, ((prod.snd : X' ⨯ Y' ⟶ Y').app U').app n' (h z) =
      g (((prod.snd : X ⨯ Y ⟶ Y).app U).app n z)) :
    AddCommGrpCat.free.map h ≫ (tensorApp X' Y' U' n').hom =
      (tensorApp X Y U n).hom ≫ AddCommGrpCat.ofHom
        ((TensorProduct.map (AddCommGrpCat.free.map f).hom.toIntLinearMap
          (AddCommGrpCat.free.map g).hom.toIntLinearMap).toAddMonoidHom) := by
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro z
  change (tensorApp X' Y' U' n').hom
      (AddCommGrpCat.free.map h (FreeAbelianGroup.of z)) =
    (TensorProduct.map (AddCommGrpCat.free.map f).hom.toIntLinearMap
      (AddCommGrpCat.free.map g).hom.toIntLinearMap)
      ((tensorApp X Y U n).hom (FreeAbelianGroup.of z))
  rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of, tensorApp_hom_of, tensorApp_hom_of]
  let x := ((prod.fst : X ⨯ Y ⟶ X).app U).app n z
  let y := ((prod.snd : X ⨯ Y ⟶ Y).app U).app n z
  change FreeAbelianGroup.of (((prod.fst : X' ⨯ Y' ⟶ X').app U').app n' (h z)) ⊗ₜ[ℤ]
      FreeAbelianGroup.of (((prod.snd : X' ⨯ Y' ⟶ Y').app U').app n' (h z)) =
    TensorProduct.map (FreeAbelianGroup.map f).toIntLinearMap
      (FreeAbelianGroup.map g).toIntLinearMap
      (FreeAbelianGroup.of x ⊗ₜ[ℤ] FreeAbelianGroup.of y)
  rw [TensorProduct.map_tmul, hf, hg]
  simp only [AddMonoidHom.coe_toIntLinearMap, FreeAbelianGroup.map_of_apply]
  rfl

private def tensorDegree (X Y : Cᵒᵖ ⥤ SSet.{w + 1}) (n : SimplexCategoryᵒᵖ) :
    ((freeAbelian.{w + 1} C).obj (X ⨯ Y)).obj n ≅
      AddCommGrpCat.presheafTensor (((freeAbelian.{w + 1} C).obj X).obj n)
        (((freeAbelian.{w + 1} C).obj Y).obj n) :=
  NatIso.ofComponents (fun U => tensorApp X Y U n) (by
    intro U U' f
    exact tensorApp_naturality ((X.map f).app n) ((Y.map f).app n) (((X ⨯ Y).map f).app n)
      (fun z => congrArg (fun t => t.app n z) ((prod.fst : X ⨯ Y ⟶ X).naturality f))
      (fun z => congrArg (fun t => t.app n z) ((prod.snd : X ⨯ Y ⟶ Y).naturality f)))

private theorem tensorDegree_naturality {X Y X' Y' : Cᵒᵖ ⥤ SSet.{w + 1}}
    {n n' : SimplexCategoryᵒᵖ}
    (f : ((freeAbelian.{w + 1} C).obj X).obj n ⟶ ((freeAbelian.{w + 1} C).obj X').obj n')
    (g : ((freeAbelian.{w + 1} C).obj Y).obj n ⟶ ((freeAbelian.{w + 1} C).obj Y').obj n')
    (h : ((freeAbelian.{w + 1} C).obj (X ⨯ Y)).obj n ⟶
      ((freeAbelian.{w + 1} C).obj (X' ⨯ Y')).obj n')
    (a : ∀ U, (X.obj U).obj n ⟶ (X'.obj U).obj n')
    (b : ∀ U, (Y.obj U).obj n ⟶ (Y'.obj U).obj n')
    (c : ∀ U, ((X ⨯ Y).obj U).obj n ⟶ ((X' ⨯ Y').obj U).obj n')
    (ha : ∀ U, f.app U = AddCommGrpCat.free.map (a U))
    (hb : ∀ U, g.app U = AddCommGrpCat.free.map (b U))
    (hc : ∀ U, h.app U = AddCommGrpCat.free.map (c U))
    (hf : ∀ U z, ((prod.fst : X' ⨯ Y' ⟶ X').app U).app n' (c U z) =
      a U (((prod.fst : X ⨯ Y ⟶ X).app U).app n z))
    (hg : ∀ U z, ((prod.snd : X' ⨯ Y' ⟶ Y').app U).app n' (c U z) =
      b U (((prod.snd : X ⨯ Y ⟶ Y).app U).app n z)) :
    h ≫ (tensorDegree X' Y' n').hom ≫ (AddCommGrpCat.presheafTensorIso _ _).hom =
      ((tensorDegree X Y n).hom ≫ (AddCommGrpCat.presheafTensorIso _ _).hom) ≫ (f ⊗ₘ g) := by
  have hh : h ≫ (tensorDegree X' Y' n').hom =
      (tensorDegree X Y n).hom ≫ AddCommGrpCat.presheafTensorMap f g := by
    apply NatTrans.ext
    funext U
    change h.app U ≫ (tensorApp X' Y' U n').hom =
      (tensorApp X Y U n).hom ≫ (AddCommGrpCat.presheafTensorMap f g).app U
    -- Compare on pure tensors, using the computation for the actual presheaf tensor map.
    have hm : (AddCommGrpCat.presheafTensorMap f g).app U = AddCommGrpCat.ofHom
        ((TensorProduct.map (f.app U).hom.toIntLinearMap
          (g.app U).hom.toIntLinearMap).toAddMonoidHom) := by
      apply AddCommGrpCat.hom_ext
      ext z
      induction z using AddCommGrpCat.presheafTensor_induction_on with
      | gen x y => exact AddCommGrpCat.presheafTensorMap_tensorGen f g U x y
      | add x y hx hy =>
        simp only [map_add, hx, hy]
    rw [hm, ha U, hb U, hc U]
    exact tensorApp_naturality (a U) (b U) (c U) (hf U) (hg U)
  rw [← Category.assoc h, hh, AddCommGrpCat.presheafTensorMap]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Free abelianization sends the chosen binary product to the degreewise tensor. -/
@[no_expose]
def freeAbelianProductTensorIso (X Y : Cᵒᵖ ⥤ SSet.{w + 1}) :
    (freeAbelian.{w + 1} C).obj (X ⨯ Y) ≅
      (freeAbelian.{w + 1} C).obj X ⊗ (freeAbelian.{w + 1} C).obj Y :=
  NatIso.ofComponents (fun n =>
    tensorDegree X Y n ≪≫ AddCommGrpCat.presheafTensorIso _ _) (by
    intro n n' f
    exact tensorDegree_naturality (((freeAbelian.{w + 1} C).obj X).map f)
      (((freeAbelian.{w + 1} C).obj Y).map f) (((freeAbelian.{w + 1} C).obj (X ⨯ Y)).map f)
      (fun U => (X.obj U).map f) (fun U => (Y.obj U).map f) (fun U => ((X ⨯ Y).obj U).map f)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (fun U z => ConcreteCategory.congr_hom (((prod.fst : X ⨯ Y ⟶ X).app U).naturality f) z)
      (fun U z => ConcreteCategory.congr_hom (((prod.snd : X ⨯ Y ⟶ Y).app U).naturality f) z))

/-- The two factors of a product generator are the original simplex projections. -/
theorem freeAbelianProductTensorIso_hom_of (X Y : Cᵒᵖ ⥤ SSet.{w + 1})
    (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (z : ((X ⨯ Y).obj U).obj n) :
    ((freeAbelianProductTensorIso X Y).hom.app n).app U (FreeAbelianGroup.of z) =
      (AddCommGrpCat.presheafTensorIso (((freeAbelian.{w + 1} C).obj X).obj n)
        (((freeAbelian.{w + 1} C).obj Y).obj n)).hom.app U
        (FreeAbelianGroup.of (((prod.fst : X ⨯ Y ⟶ X).app U).app n z) ⊗ₜ[ℤ]
          FreeAbelianGroup.of (((prod.snd : X ⨯ Y ⟶ Y).app U).app n z)) := by
  change (AddCommGrpCat.presheafTensorIso (((freeAbelian.{w + 1} C).obj X).obj n)
    (((freeAbelian.{w + 1} C).obj Y).obj n)).hom.app U
    ((tensorApp X Y U n).hom (FreeAbelianGroup.of z)) = _
  rw [tensorApp_hom_of]
  rfl

/-- The free-abelian product comparison respects actual maps of both factors. -/
@[reassoc]
theorem freeAbelianProductTensorIso_naturality {X Y X' Y' : Cᵒᵖ ⥤ SSet.{w + 1}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (freeAbelian.{w + 1} C).map (prod.map f g) ≫ (freeAbelianProductTensorIso X' Y').hom =
      (freeAbelianProductTensorIso X Y).hom ≫
        ((freeAbelian.{w + 1} C).map f ⊗ₘ (freeAbelian.{w + 1} C).map g) := by
  apply NatTrans.ext
  funext n
  exact tensorDegree_naturality (((freeAbelian.{w + 1} C).map f).app n)
    (((freeAbelian.{w + 1} C).map g).app n)
    (((freeAbelian.{w + 1} C).map (prod.map f g)).app n)
    (fun U => (f.app U).app n) (fun U => (g.app U).app n)
    (fun U => ((prod.map f g).app U).app n)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun U z => congrArg (fun t : X ⨯ Y ⟶ X' => (t.app U).app n z) (prod.map_fst f g))
    (fun U z => congrArg (fun t : X ⨯ Y ⟶ Y' => (t.app U).app n z) (prod.map_snd f g))

end CategoryTheory.PointedSimplicialPresheaf
