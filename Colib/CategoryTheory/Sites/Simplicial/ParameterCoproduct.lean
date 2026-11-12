/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Slice.PresheafExtension
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The coproduct of coefficients indexed by a representable interval

At a site object `U`, the coproduct has one copy of the coefficients for each map `U ⟶ V`.
Its right adjoint is precomposition by product with `V`. The fold on the actual summands
transposes to restriction along the first projection.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe z w v u

namespace CategoryTheory.PointedSimplicialPresheaf.ParameterCoproduct

variable {C : Type u} [Category.{v} C] (V : C)
  (A : Type z) [Category.{w} A] [HasCoproducts.{v} A]

/-- Sum the coefficients over the maps to the parameter using the actual slice extension. -/
abbrev functor : (Cᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ A :=
  SlicePresheaf.restriction V ⋙ SlicePresheaf.extension V

/-- The inclusion of the summand labelled by a map to the parameter. -/
def ι (P : Cᵒᵖ ⥤ A) (U : Cᵒᵖ) (g : U.unop ⟶ V) :
    P.obj U ⟶ ((functor V A).obj P).obj U :=
  Sigma.ι (fun _ : U.unop ⟶ V => P.obj U) g

@[reassoc]
theorem ι_restriction (P : Cᵒᵖ ⥤ A) {U W : Cᵒᵖ} (f : U ⟶ W) (g : U.unop ⟶ V) :
    ι V A P U g ≫ ((functor V A).obj P).map f = P.map f ≫ ι V A P W (f.unop ≫ g) := by
  change Sigma.ι _ g ≫ Sigma.desc _ = _
  exact Sigma.ι_comp_desc _ _

@[reassoc]
theorem ι_map_app {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) (U : Cᵒᵖ) (g : U.unop ⟶ V) :
    ι V A P U g ≫ ((functor V A).map f).app U = f.app U ≫ ι V A Q U g := by
  change Sigma.ι _ g ≫ Sigma.desc _ = _
  exact Sigma.ι_comp_desc _ _

/-- The fold induced by the counit of slice extension. -/
def fold : functor V A ⟶ 𝟭 (Cᵒᵖ ⥤ A) :=
  (SlicePresheaf.adjunction V).counit

@[reassoc (attr := simp)]
theorem ι_fold_app (P : Cᵒᵖ ⥤ A) (U : Cᵒᵖ) (g : U.unop ⟶ V) :
    ι V A P U g ≫ ((fold V A).app P).app U = 𝟙 (P.obj U) := by
  change Sigma.ι _ g ≫ Sigma.desc _ = _
  exact Sigma.ι_comp_desc _ _

instance [HasFiniteLimits A] [AB4OfSize.{v} A] : PreservesFiniteLimits (functor V A) :=
  inferInstance

instance [Preadditive A] : (functor V A).Additive where
  map_add {P Q} f g := by
    apply NatTrans.ext
    funext U
    apply Sigma.hom_ext
    intro a
    change ι V A P U a ≫ ((functor V A).map (f + g)).app U =
      ι V A P U a ≫ (((functor V A).map f).app U + ((functor V A).map g).app U)
    simp only [Preadditive.comp_add, ι_map_app, NatTrans.app_add, Preadditive.add_comp]

private theorem ι_app_comp_map {P Q : Cᵒᵖ ⥤ A} (a : (functor V A).obj P ⟶ Q)
    {U W : Cᵒᵖ} (f : U ⟶ W) (g : U.unop ⟶ V) :
    ι V A P U g ≫ a.app U ≫ Q.map f = P.map f ≫ ι V A P W (f.unop ≫ g) ≫ a.app W := calc
  _ = (ι V A P U g ≫ ((functor V A).obj P).map f) ≫ a.app W :=
    (congrArg (ι V A P U g ≫ ·) (a.naturality f).symm).trans (Category.assoc _ _ _).symm
  _ = (P.map f ≫ ι V A P W (f.unop ≫ g)) ≫ a.app W :=
    congrArg (· ≫ a.app W) (ι_restriction V A P f g)
  _ = _ := Category.assoc _ _ _

variable [HasBinaryProducts C]

/-- Precompose by the opposite of the product with the parameter on the right. -/
abbrev reindex : (Cᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ A :=
  (Functor.whiskeringLeft Cᵒᵖ Cᵒᵖ A).obj (prod.functor.flip.obj V).op

/-- The natural first projection from the product with the parameter. -/
def productProjection : prod.functor.flip.obj V ⟶ 𝟭 C where
  app _ := prod.fst
  naturality _ _ f := by
    change prod.map f (𝟙 V) ≫ prod.fst = prod.fst ≫ f
    simp

/-- Pullback of coefficients by the first projection. -/
def projectionPullback : 𝟭 (Cᵒᵖ ⥤ A) ⟶ reindex V A :=
  (Functor.whiskeringLeft Cᵒᵖ Cᵒᵖ A).map (NatTrans.op (productProjection V))

omit [HasCoproducts.{v} A] in
@[simp]
theorem projectionPullback_app_app (P : Cᵒᵖ ⥤ A) (U : C) :
    ((projectionPullback V A).app P).app (op U) =
      P.map (prod.fst : U ⨯ V ⟶ U).op := rfl

private def starProductIso : prod.functor.flip.obj V ≅ Over.star V ⋙ Over.forget V :=
  NatIso.ofComponents (fun U => prod.braiding U V) (by
    intro U W f
    change prod.map f (𝟙 V) ≫ (prod.braiding W V).hom =
      (prod.braiding U V).hom ≫ prod.map (𝟙 V) f
    exact braid_natural f (𝟙 V))

private def starAdjunction : functor V A ⊣
    (Functor.whiskeringLeft Cᵒᵖ Cᵒᵖ A).obj (Over.star V ⋙ Over.forget V).op :=
  ((Over.forgetAdjStar V).op.whiskerLeft A).comp (SlicePresheaf.adjunction V)

/-- The parameter-indexed coproduct is left adjoint to product precomposition. -/
@[no_expose]
def adjunction : functor V A ⊣ reindex V A :=
  (starAdjunction V A).ofNatIsoRight
    ((Functor.whiskeringLeft Cᵒᵖ Cᵒᵖ A).mapIso (NatIso.op (starProductIso V)))

instance : (functor V A).IsLeftAdjoint := (adjunction V A).isLeftAdjoint

private theorem starHomEquiv_app {P Q : Cᵒᵖ ⥤ A} (a : (functor V A).obj P ⟶ Q) (U : C) :
    ((starAdjunction V A).homEquiv P Q a).app (op U) =
      P.map (prod.snd : V ⨯ U ⟶ U).op ≫
        ι V A P (op (V ⨯ U)) (prod.fst : V ⨯ U ⟶ V) ≫ a.app (op (V ⨯ U)) := by
  have hs : (SlicePresheaf.adjunction V).homEquiv ((SlicePresheaf.restriction V).obj P) Q a =
      SlicePresheaf.homTo V a := by
    simp [SlicePresheaf.adjunction, SlicePresheaf.homEquiv]
  rw [starAdjunction, Adjunction.comp_homEquiv, Equiv.trans_apply, hs]
  simp only [Adjunction.homEquiv_unit, NatTrans.comp_app, Adjunction.whiskerLeft_unit_app_app,
    Adjunction.op_unit_app, unop_op, Over.forgetAdjStar_counit_app,
    Functor.whiskeringLeft_obj_map, Functor.whiskerLeft_app]
  change P.map (prod.snd : V ⨯ U ⟶ U).op ≫
    ι V A P (op ((Over.star V).obj U).left) ((Over.star V).obj U).hom ≫
      a.app (op ((Over.star V).obj U).left) = _
  exact congrArg (fun g : V ⨯ U ⟶ V ↦ P.map (prod.snd : V ⨯ U ⟶ U).op ≫
    ι V A P (op (V ⨯ U)) g ≫ a.app (op (V ⨯ U))) (Over.star_obj_hom V U)

/-- The adjunct restricts the coefficient along the first projection and applies the given map
to the summand labelled by the parameter projection. -/
theorem homEquiv_app {P Q : Cᵒᵖ ⥤ A} (a : (functor V A).obj P ⟶ Q) (U : C) :
    ((adjunction V A).homEquiv P Q a).app (op U) =
      P.map (prod.fst : U ⨯ V ⟶ U).op ≫
        ι V A P (op (U ⨯ V)) (prod.snd : U ⨯ V ⟶ V) ≫ a.app (op (U ⨯ V)) := by
  rw [adjunction, Adjunction.homEquiv_ofNatIsoRight_apply, NatTrans.comp_app, starHomEquiv_app]
  let f : op (V ⨯ U) ⟶ op (U ⨯ V) := (prod.braiding U V).hom.op
  change (P.map (prod.snd : V ⨯ U ⟶ U).op ≫
    ι V A P (op (V ⨯ U)) (prod.fst : V ⨯ U ⟶ V) ≫ a.app (op (V ⨯ U))) ≫
      Q.map f = _
  calc
    _ = P.map (prod.snd : V ⨯ U ⟶ U).op ≫
        (ι V A P (op (V ⨯ U)) prod.fst ≫ a.app (op (V ⨯ U)) ≫ Q.map f) := by
      simp only [Category.assoc]
    _ = P.map (prod.snd : V ⨯ U ⟶ U).op ≫
        P.map f ≫ ι V A P (op (U ⨯ V)) (f.unop ≫ prod.fst) ≫ a.app (op (U ⨯ V)) :=
      congrArg (P.map (prod.snd : V ⨯ U ⟶ U).op ≫ ·) (ι_app_comp_map V A a f prod.fst)
    _ = _ := by
      rw [← P.map_comp_assoc]
      change P.map ((prod.braiding U V).hom ≫ (prod.snd : V ⨯ U ⟶ U)).op ≫
        ι V A P (op (U ⨯ V)) ((prod.braiding U V).hom ≫ prod.fst) ≫ _ = _
      simp [prod.braiding_hom]

/-- The inverse adjunct on a summand restricts along the graph of its parameter map. -/
@[reassoc]
theorem ι_homEquiv_symm_app {P Q : Cᵒᵖ ⥤ A} (b : P ⟶ (reindex V A).obj Q)
    (U : C) (g : U ⟶ V) :
    ι V A P (op U) g ≫ (((adjunction V A).homEquiv P Q).symm b).app (op U) =
      b.app (op U) ≫ Q.map (prod.lift (𝟙 U) g).op := by
  let a := ((adjunction V A).homEquiv P Q).symm b
  have h : ((adjunction V A).homEquiv P Q a).app (op U) = b.app (op U) :=
    congrArg (fun η => η.app (op U)) (Equiv.apply_symm_apply ((adjunction V A).homEquiv P Q) b)
  rw [homEquiv_app] at h
  let f : op (U ⨯ V) ⟶ op U := (prod.lift (𝟙 U) g).op
  change ι V A P (op U) g ≫ a.app (op U) = b.app (op U) ≫ Q.map f
  rw [← h]
  symm
  calc
    _ = P.map (prod.fst : U ⨯ V ⟶ U).op ≫
        (ι V A P (op (U ⨯ V)) prod.snd ≫ a.app (op (U ⨯ V)) ≫ Q.map f) := by
      simp only [Category.assoc]
    _ = P.map (prod.fst : U ⨯ V ⟶ U).op ≫
        P.map f ≫ ι V A P (op U) (f.unop ≫ prod.snd) ≫ a.app (op U) :=
      congrArg (P.map (prod.fst : U ⨯ V ⟶ U).op ≫ ·) (ι_app_comp_map V A a f prod.snd)
    _ = _ := by
      rw [← P.map_comp_assoc]
      change P.map (prod.lift (𝟙 U) g ≫ (prod.fst : U ⨯ V ⟶ U)).op ≫
        ι V A P (op U) (prod.lift (𝟙 U) g ≫ prod.snd) ≫ a.app (op U) = _
      simp

/-- The adjunct of the fold is pullback by the actual first projection. -/
theorem homEquiv_fold (P : Cᵒᵖ ⥤ A) :
    (adjunction V A).homEquiv P P ((fold V A).app P) = (projectionPullback V A).app P := by
  apply NatTrans.ext
  funext U
  change ((adjunction V A).homEquiv P P ((fold V A).app P)).app (op U.unop) =
    P.map (prod.fst : U.unop ⨯ V ⟶ U.unop).op
  simp only [homEquiv_app, ι_fold_app, Category.comp_id]

end CategoryTheory.PointedSimplicialPresheaf.ParameterCoproduct
