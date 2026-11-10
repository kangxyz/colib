/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ReducedChains

/-!
# The pointed underlying presheaf of a simplicial abelian presheaf

Forget the abelian group structure in every degree and point the result at
zero. The adjunction with reduced free abelianization uses the cokernel of
the supplied basepoint and the ordinary free-forgetful adjunction.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C]

/-- Forget abelian group structure and put the site variable first. -/
def underlyingAbelian : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤ Cᵒᵖ ⥤ SSet.{w} :=
  (Functor.whiskeringRight _ _ _).obj
    ((Functor.whiskeringRight Cᵒᵖ _ _).obj (CategoryTheory.forget AddCommGrpCat.{w})) ⋙
    flipFunctor SimplexCategoryᵒᵖ Cᵒᵖ (Type w)

/-- The ordinary adjunction in every site object and simplicial degree. -/
def freeAbelianForgetAdjunction : freeAbelian.{w} C ⊣ underlyingAbelian C :=
  (Functor.flipping (C := Cᵒᵖ) (D := SimplexCategoryᵒᵖ) (E := Type w)).toAdjunction.comp
    ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).whiskerRight SimplexCategoryᵒᵖ)

/-- The zero elements supply a global point of the underlying presheaf. -/
def abelianZeroSection (A : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w})) :
    ⊤_ (Cᵒᵖ ⥤ SSet.{w}) ⟶ (underlyingAbelian C).obj A where
  app U :=
    { app := fun n ↦ ↾fun _ ↦ (0 : (A.obj n).obj U)
      naturality := by
        intro n m f
        apply ConcreteCategory.hom_ext
        intro _
        exact ((A.map f).app U).hom.map_zero.symm }
  naturality := by
    intro U V f
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro _
    exact ((A.obj n).map f).hom.map_zero.symm

/-- The underlying simplicial presheaf pointed at its actual zero. -/
def pointedUnderlyingAbelian : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ⥤
    PointedSimplicialPresheaf.{w} C where
  obj A := Under.mk (abelianZeroSection C A)
  map f := Under.homMk ((underlyingAbelian C).map f) (by
    apply NatTrans.ext
    funext U
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro _
    exact ((f.app n).app U).hom.map_zero)
  map_id A := Under.UnderMorphism.ext ((underlyingAbelian C).map_id A)
  map_comp f g := Under.UnderMorphism.ext ((underlyingAbelian C).map_comp f g)

@[simp]
theorem pointedUnderlyingAbelian_obj_right (A : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w})) :
    ((pointedUnderlyingAbelian C).obj A).right = (underlyingAbelian C).obj A := rfl

@[simp]
theorem pointedUnderlyingAbelian_map_right {A B : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w})}
    (f : A ⟶ B) : ((pointedUnderlyingAbelian C).map f).right = (underlyingAbelian C).map f := rfl

@[simp]
theorem pointedUnderlyingAbelian_map_app_app {A B : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w})}
    (f : A ⟶ B) (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ) (x : (A.obj n).obj U) :
    ((((pointedUnderlyingAbelian C).map f).right.app U).app n) x = (f.app n).app U x := rfl

@[simp]
theorem pointedUnderlyingAbelian_basepoint (A : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w}))
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    basepointSimplex C ((pointedUnderlyingAbelian C).obj A) n U = (0 : (A.obj n).obj U) := rfl

theorem freeAbelianForgetAdjunction_homEquiv_zero
    (A : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w})) :
    (freeAbelianForgetAdjunction C).homEquiv (⊤_ (Cᵒᵖ ⥤ SSet.{w})) A 0 =
      abelianZeroSection C A := by
  rw [Adjunction.homEquiv_unit]
  apply NatTrans.ext
  funext U
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro _
  rfl

/-- Maps out of the reduced free abelian presheaf are exactly pointed maps
to the underlying presheaf of the abelian target. -/
def reducedFreeAbelianHomEquiv (F : PointedSimplicialPresheaf.{w} C)
    (A : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w})) :
    ((reducedFreeAbelian C).obj F ⟶ A) ≃ (F ⟶ (pointedUnderlyingAbelian C).obj A) where
  toFun f := Under.homMk ((freeAbelianForgetAdjunction C).homEquiv F.right A (reduction C F ≫ f))
    (by
      change F.hom ≫ _ = abelianZeroSection C A
      rw [← (freeAbelianForgetAdjunction C).homEquiv_naturality_left, ← Category.assoc,
        basepoint_reduction, zero_comp, freeAbelianForgetAdjunction_homEquiv_zero])
  invFun f := by
    let g : F.right ⟶ (underlyingAbelian C).obj A := f.right
    refine reductionDesc C F (((freeAbelianForgetAdjunction C).homEquiv F.right A).symm g) ?_
    apply ((freeAbelianForgetAdjunction C).homEquiv _ A).injective
    rw [(freeAbelianForgetAdjunction C).homEquiv_naturality_left, Equiv.apply_symm_apply,
      freeAbelianForgetAdjunction_homEquiv_zero]
    exact Under.w f
  left_inv f := by
    apply reduction_hom_ext C
    simp only [reduction_reductionDesc]
    exact ((freeAbelianForgetAdjunction C).homEquiv F.right A).symm_apply_apply (reduction C F ≫ f)
  right_inv f := by
    apply Under.UnderMorphism.ext
    simp only [reduction_reductionDesc]
    let g : F.right ⟶ (underlyingAbelian C).obj A := f.right
    exact ((freeAbelianForgetAdjunction C).homEquiv F.right A).apply_symm_apply g

@[simp]
theorem reducedFreeAbelianHomEquiv_apply_right (F : PointedSimplicialPresheaf.{w} C)
    (A : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w})) (f : (reducedFreeAbelian C).obj F ⟶ A) :
    (reducedFreeAbelianHomEquiv C F A f).right =
      (freeAbelianForgetAdjunction C).homEquiv F.right A (reduction C F ≫ f) := rfl

theorem reducedFreeAbelianHomEquiv_naturality_left {F G : PointedSimplicialPresheaf.{w} C}
    (f : F ⟶ G) {A : SimplicialObject (Cᵒᵖ ⥤ AddCommGrpCat.{w})}
    (g : (reducedFreeAbelian C).obj G ⟶ A) :
    reducedFreeAbelianHomEquiv C F A ((reducedFreeAbelian C).map f ≫ g) =
      f ≫ reducedFreeAbelianHomEquiv C G A g := by
  apply Under.UnderMorphism.ext
  change (freeAbelianForgetAdjunction C).homEquiv F.right A
      (reduction C F ≫ (reducedFreeAbelian C).map f ≫ g) =
    f.right ≫ (freeAbelianForgetAdjunction C).homEquiv G.right A (reduction C G ≫ g)
  rw [reduction_naturality_assoc, (freeAbelianForgetAdjunction C).homEquiv_naturality_left]

/-- Reduced free abelianization is left adjoint to forgetting to the
simplicial presheaf pointed at zero. -/
def reducedFreeForgetAdjunction : reducedFreeAbelian.{w} C ⊣ pointedUnderlyingAbelian C :=
  Adjunction.mkOfHomEquiv {
    homEquiv := reducedFreeAbelianHomEquiv C
    homEquiv_naturality_left_symm := by
      intro F G A f g
      apply (reducedFreeAbelianHomEquiv C F A).injective
      rw [Equiv.apply_symm_apply, reducedFreeAbelianHomEquiv_naturality_left,
        Equiv.apply_symm_apply]
    homEquiv_naturality_right := by
      intro F A B f g
      apply Under.UnderMorphism.ext
      change (freeAbelianForgetAdjunction C).homEquiv F.right B (reduction C F ≫ f ≫ g) =
        (freeAbelianForgetAdjunction C).homEquiv F.right A (reduction C F ≫ f) ≫
          (underlyingAbelian C).map g
      rw [← Category.assoc, (freeAbelianForgetAdjunction C).homEquiv_naturality_right] }

end CategoryTheory.PointedSimplicialPresheaf
