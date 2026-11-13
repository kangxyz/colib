/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ParameterCoproduct
public import Colib.CategoryTheory.Sites.Simplicial.ReducedChains
public import Colib.CategoryTheory.Sites.Simplicial.UniverseLift
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Free abelianization of a product with a discrete representable

The free generator of a paired simplex belongs to the summand labelled by the
parameter coordinate. This comparison respects restriction and simplicial
operators, and the first projection gives the fold on the summands.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe z a w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C]

/-- The discrete Yoneda presheaf with its actual lifted simplex types. -/
abbrev liftedRepresentableInterval (V : C) : Cᵒᵖ ⥤ SSet.{max v w} :=
  (uliftPresheaf.{w, v} C).obj ((simplicialYoneda C).obj V)

namespace ParameterCoproduct

variable (V : C) (A : Type z) [Category.{a} A] [HasCoproducts.{v} A]

/-- The parameter coproduct applied in every simplicial degree. -/
abbrev simplicialFunctor : SimplicialObject (Cᵒᵖ ⥤ A) ⥤ SimplicialObject (Cᵒᵖ ⥤ A) :=
  (SimplicialObject.whiskering _ _).obj (functor V A)

/-- The original fold applied in every simplicial degree. -/
def simplicialFold : simplicialFunctor V A ⟶ 𝟭 (SimplicialObject (Cᵒᵖ ⥤ A)) :=
  (SimplicialObject.whiskering _ _).map (fold V A)

end ParameterCoproduct

variable (V : C)

local notation "I" => liftedRepresentableInterval V

private abbrev simplexEvaluation (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    (Cᵒᵖ ⥤ SSet.{max v w}) ⥤ Type (max v w) :=
  (CategoryTheory.evaluation _ _).obj U ⋙ (CategoryTheory.evaluation _ _).obj n

/-- The two coordinates of an actual simplex of the product. -/
private def productCoordinates (F : Cᵒᵖ ⥤ SSet.{max v w}) (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    ((F ⨯ I).obj U).obj n ≃ (F.obj U).obj n × (U.unop ⟶ V) :=
  ((PreservesLimitPair.iso (simplexEvaluation n U) F I) ≪≫ Types.binaryProductIso _ _).toEquiv.trans
    (Equiv.prodCongr (Equiv.refl _) Equiv.ulift)

private theorem productCoordinates_fst (F : Cᵒᵖ ⥤ SSet.{max v w}) (n : SimplexCategoryᵒᵖ)
    (U : Cᵒᵖ) (x : ((F ⨯ I).obj U).obj n) :
    (productCoordinates V F n U x).1 = ((prod.fst : F ⨯ I ⟶ F).app U).app n x := by
  let E : (Cᵒᵖ ⥤ SSet.{max v w}) ⥤ Type (max v w) := simplexEvaluation n U
  have h : ((PreservesLimitPair.iso E F I) ≪≫ Types.binaryProductIso _ _).hom ≫
      ↾_root_.Prod.fst = E.map prod.fst := by
    simp only [Iso.trans_hom, Category.assoc, Types.binaryProductIso_hom_comp_fst,
      PreservesLimitPair.iso_hom, prodComparison_fst]
  exact ConcreteCategory.congr_hom h x

private theorem productCoordinates_snd (F : Cᵒᵖ ⥤ SSet.{max v w}) (n : SimplexCategoryᵒᵖ)
    (U : Cᵒᵖ) (x : ((F ⨯ I).obj U).obj n) :
    (productCoordinates V F n U x).2 = (((prod.snd : F ⨯ I ⟶ I).app U).app n x).down := by
  let E : (Cᵒᵖ ⥤ SSet.{max v w}) ⥤ Type (max v w) := simplexEvaluation n U
  have h : ((PreservesLimitPair.iso E F I) ≪≫ Types.binaryProductIso _ _).hom ≫
      ↾_root_.Prod.snd = E.map prod.snd := by
    simp only [Iso.trans_hom, Category.assoc, Types.binaryProductIso_hom_comp_snd,
      PreservesLimitPair.iso_hom, prodComparison_snd]
  exact congrArg ULift.down (ConcreteCategory.congr_hom h x)

private theorem productCoordinates_map_site (F : Cᵒᵖ ⥤ SSet.{max v w}) (n : SimplexCategoryᵒᵖ)
    {U W : Cᵒᵖ} (f : U ⟶ W) (x : ((F ⨯ I).obj U).obj n) :
    productCoordinates V F n W (((F ⨯ I).map f).app n x) =
      ⟨(F.map f).app n (productCoordinates V F n U x).1,
        f.unop ≫ (productCoordinates V F n U x).2⟩ := by
  apply Prod.ext
  · simp only [productCoordinates_fst]
    exact congrArg (fun t => t.app n x) ((prod.fst : F ⨯ I ⟶ F).naturality f)
  · simp only [productCoordinates_snd]
    exact congrArg (fun t => (t.app n x).down) ((prod.snd : F ⨯ I ⟶ I).naturality f)

private theorem productCoordinates_map_simplex (F : Cᵒᵖ ⥤ SSet.{max v w}) (U : Cᵒᵖ)
    {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) (x : ((F ⨯ I).obj U).obj n) :
    productCoordinates V F m U (((F ⨯ I).obj U).map f x) =
      ⟨(F.obj U).map f (productCoordinates V F n U x).1, (productCoordinates V F n U x).2⟩ := by
  apply Prod.ext
  · simp only [productCoordinates_fst]
    exact ConcreteCategory.congr_hom (((prod.fst : F ⨯ I ⟶ F).app U).naturality f) x
  · simp only [productCoordinates_snd]
    exact congrArg ULift.down
      (ConcreteCategory.congr_hom (((prod.snd : F ⨯ I ⟶ I).app U).naturality f) x)

private theorem productCoordinates_map {F G : Cᵒᵖ ⥤ SSet.{max v w}} (f : F ⟶ G)
    (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) (x : ((F ⨯ I).obj U).obj n) :
    productCoordinates V G n U (((prod.map f (𝟙 I)).app U).app n x) =
      ⟨(f.app U).app n (productCoordinates V F n U x).1, (productCoordinates V F n U x).2⟩ := by
  apply Prod.ext
  · simp only [productCoordinates_fst]
    exact congrArg (fun t : F ⨯ I ⟶ G => (t.app U).app n x) (prod.map_fst f (𝟙 I))
  · simp only [productCoordinates_snd]
    have h : prod.map f (𝟙 I) ≫ (prod.snd : G ⨯ I ⟶ I) =
        (prod.snd : F ⨯ I ⟶ I) := by simp
    exact congrArg (fun t : F ⨯ I ⟶ I => ((t.app U).app n x).down) h

private def freeAbelianIndexIso {X Y : Type (max v w)} {J : Type v} (e : Y ≃ X × J) :
    AddCommGrpCat.free.obj Y ≅ ∐ fun _ : J => AddCommGrpCat.free.obj X := by
  let P (_ : J) := AddCommGrpCat.free.obj X
  let h : AddCommGrpCat.free.obj Y ⟶ ∐ P :=
    AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun y =>
      Sigma.ι P (e y).2 (FreeAbelianGroup.of (e y).1))
  let k : (∐ P) ⟶ AddCommGrpCat.free.obj Y :=
    Sigma.desc fun j => AddCommGrpCat.free.map (↾fun x => e.symm (x, j))
  have hh (y : Y) : h (FreeAbelianGroup.of y) = Sigma.ι P (e y).2 (FreeAbelianGroup.of (e y).1) :=
    FreeAbelianGroup.lift_apply_of _ _
  have hk (j : J) : Sigma.ι P j ≫ k = AddCommGrpCat.free.map (↾fun x => e.symm (x, j)) :=
    Sigma.ι_comp_desc _ _
  refine ⟨h, k, ?_, ?_⟩
  · apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro y
    change k (h (FreeAbelianGroup.of y)) = FreeAbelianGroup.of y
    rw [hh]
    have he := ConcreteCategory.congr_hom (hk (e y).2) (FreeAbelianGroup.of (e y).1)
    change k (Sigma.ι P (e y).2 (FreeAbelianGroup.of (e y).1)) = _ at he
    rw [he, AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of]
    exact congrArg FreeAbelianGroup.of (e.symm_apply_apply y)
  · apply Sigma.hom_ext
    intro j
    rw [← Category.assoc, hk, Category.comp_id]
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro x
    change h (AddCommGrpCat.free.map (↾fun x => e.symm (x, j)) (FreeAbelianGroup.of x)) = _
    rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of]
    change h (FreeAbelianGroup.of (e.symm (x, j))) = Sigma.ι P j (FreeAbelianGroup.of x)
    rw [hh, e.apply_symm_apply]

private def comparisonApp (F : Cᵒᵖ ⥤ SSet.{max v w}) (n : SimplexCategoryᵒᵖ) (U : Cᵒᵖ) :
    (((freeAbelian C).obj (F ⨯ I)).obj n).obj U ≅
      ((ParameterCoproduct.functor V AddCommGrpCat.{max v w}).obj
        (((freeAbelian C).obj F).obj n)).obj U :=
  freeAbelianIndexIso (productCoordinates V F n U)

private theorem comparisonApp_hom_of (F : Cᵒᵖ ⥤ SSet.{max v w}) (n : SimplexCategoryᵒᵖ)
    (U : Cᵒᵖ) (x : ((F ⨯ I).obj U).obj n) :
    (comparisonApp V F n U).hom (FreeAbelianGroup.of x) =
      ParameterCoproduct.ι V _ (((freeAbelian C).obj F).obj n) U (productCoordinates V F n U x).2
        (FreeAbelianGroup.of (productCoordinates V F n U x).1) :=
  FreeAbelianGroup.lift_apply_of _ _

private def comparisonDegree (F : Cᵒᵖ ⥤ SSet.{max v w}) (n : SimplexCategoryᵒᵖ) :
    ((freeAbelian C).obj (F ⨯ I)).obj n ≅
      (ParameterCoproduct.functor V AddCommGrpCat.{max v w}).obj (((freeAbelian C).obj F).obj n) :=
  NatIso.ofComponents (comparisonApp V F n) (by
    intro U W f
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro x
    let P := ((freeAbelian C).obj F).obj n
    let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
    let y := productCoordinates V F n U x
    change (comparisonApp V F n W).hom
        (AddCommGrpCat.free.map (((F ⨯ I).map f).app n) (FreeAbelianGroup.of x)) =
      (Φ.obj P).map f ((comparisonApp V F n U).hom (FreeAbelianGroup.of x))
    rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of, comparisonApp_hom_of,
      comparisonApp_hom_of, productCoordinates_map_site]
    have h := ConcreteCategory.congr_hom (ParameterCoproduct.ι_restriction V _ P f y.2)
      (FreeAbelianGroup.of y.1)
    change (Φ.obj P).map f (ParameterCoproduct.ι V _ P U y.2 (FreeAbelianGroup.of y.1)) =
      ParameterCoproduct.ι V _ P W (f.unop ≫ y.2)
        (AddCommGrpCat.free.map ((F.map f).app n) (FreeAbelianGroup.of y.1)) at h
    rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of] at h
    exact h.symm)

private theorem comparisonApp_naturality {F G : Cᵒᵖ ⥤ SSet.{max v w}}
    {n m : SimplexCategoryᵒᵖ} (U : Cᵒᵖ)
    (f : ((freeAbelian C).obj F).obj n ⟶ ((freeAbelian C).obj G).obj m)
    (g : ((freeAbelian C).obj (F ⨯ I)).obj n ⟶ ((freeAbelian C).obj (G ⨯ I)).obj m)
    (p : (F.obj U).obj n ⟶ (G.obj U).obj m)
    (q : ((F ⨯ I).obj U).obj n ⟶ ((G ⨯ I).obj U).obj m)
    (hf : f.app U = AddCommGrpCat.free.map p) (hg : g.app U = AddCommGrpCat.free.map q)
    (h : ∀ x, productCoordinates V G m U (q x) =
      ⟨p (productCoordinates V F n U x).1, (productCoordinates V F n U x).2⟩) :
    g.app U ≫ (comparisonApp V G m U).hom =
      (comparisonApp V F n U).hom ≫
        ((ParameterCoproduct.functor V AddCommGrpCat.{max v w}).map f).app U := by
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro x
  let P := ((freeAbelian C).obj F).obj n
  let Q := ((freeAbelian C).obj G).obj m
  let Φ := ParameterCoproduct.functor V AddCommGrpCat.{max v w}
  let y := productCoordinates V F n U x
  have hgx : g.app U (FreeAbelianGroup.of x) = FreeAbelianGroup.of (q x) := calc
    _ = AddCommGrpCat.free.map q (FreeAbelianGroup.of x) :=
      ConcreteCategory.congr_hom hg _
    _ = _ := by rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of]
  have hfy : f.app U (FreeAbelianGroup.of y.1) = FreeAbelianGroup.of (p y.1) := calc
    _ = AddCommGrpCat.free.map p (FreeAbelianGroup.of y.1) :=
      ConcreteCategory.congr_hom hf _
    _ = _ := by rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of]
  change (comparisonApp V G m U).hom (g.app U (FreeAbelianGroup.of x)) =
    (Φ.map f).app U ((comparisonApp V F n U).hom (FreeAbelianGroup.of x))
  rw [hgx, comparisonApp_hom_of, comparisonApp_hom_of, h]
  have hi := ConcreteCategory.congr_hom (ParameterCoproduct.ι_map_app V _ f U y.2)
    (FreeAbelianGroup.of y.1)
  change (Φ.map f).app U (ParameterCoproduct.ι V _ P U y.2 (FreeAbelianGroup.of y.1)) =
    ParameterCoproduct.ι V _ Q U y.2 (f.app U (FreeAbelianGroup.of y.1)) at hi
  rw [hfy] at hi
  exact hi.symm

private def comparisonObj (F : Cᵒᵖ ⥤ SSet.{max v w}) :
    (freeAbelian C).obj (F ⨯ I) ≅
      (ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w}).obj
        ((freeAbelian C).obj F) :=
  NatIso.ofComponents (comparisonDegree V F) (by
    intro n m f
    apply NatTrans.ext
    funext U
    exact comparisonApp_naturality V U (((freeAbelian C).obj F).map f)
      (((freeAbelian C).obj (F ⨯ I)).map f) ((F.obj U).map f) (((F ⨯ I).obj U).map f)
      rfl rfl (productCoordinates_map_simplex V F U f))

/-- Free abelianization of the actual product with the lifted representable
is degreewise the parameter-indexed coproduct. -/
@[no_expose]
def freeAbelianParameterProductIso :
    prod.functor.flip.obj (liftedRepresentableInterval.{w} V) ⋙ freeAbelian C ≅
      freeAbelian C ⋙ ParameterCoproduct.simplicialFunctor V AddCommGrpCat.{max v w} :=
  NatIso.ofComponents (comparisonObj V) (by
    intro F G f
    apply NatTrans.ext
    funext n
    apply NatTrans.ext
    funext U
    exact comparisonApp_naturality V U (((freeAbelian C).map f).app n)
      (((freeAbelian C).map (prod.map f (𝟙 I))).app n) ((f.app U).app n)
      (((prod.map f (𝟙 I)).app U).app n) rfl rfl (productCoordinates_map V f n U))

/-- The image of a free generator retains both original product coordinates. -/
theorem freeAbelianParameterProductIso_hom_of (F : Cᵒᵖ ⥤ SSet.{max v w}) (n : SimplexCategoryᵒᵖ)
    (U : Cᵒᵖ) (x : ((F ⨯ I).obj U).obj n) :
    (((freeAbelianParameterProductIso.{w} V).hom.app F).app n).app U (FreeAbelianGroup.of x) =
      ParameterCoproduct.ι V _ (((freeAbelian C).obj F).obj n) U
        (((prod.snd : F ⨯ I ⟶ I).app U).app n x).down
        (FreeAbelianGroup.of (((prod.fst : F ⨯ I ⟶ F).app U).app n x)) := by
  change (comparisonApp V F n U).hom (FreeAbelianGroup.of x) = _
  simpa only [productCoordinates_fst, productCoordinates_snd] using comparisonApp_hom_of V F n U x

/-- The comparison sends the first projection of the actual product to the degreewise fold. -/
@[reassoc]
theorem freeAbelianParameterProductIso_hom_fold (F : Cᵒᵖ ⥤ SSet.{max v w}) :
    (freeAbelianParameterProductIso.{w} V).hom.app F ≫
      (ParameterCoproduct.simplicialFold V _).app ((freeAbelian C).obj F) =
        (freeAbelian C).map (prod.fst : F ⨯ I ⟶ F) := by
  apply NatTrans.ext
  funext n
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro x
  let P := ((freeAbelian C).obj F).obj n
  change ((ParameterCoproduct.fold V _).app P).app U
      ((((freeAbelianParameterProductIso.{w} V).hom.app F).app n).app U (FreeAbelianGroup.of x)) =
    AddCommGrpCat.free.map (((prod.fst : F ⨯ I ⟶ F).app U).app n) (FreeAbelianGroup.of x)
  rw [freeAbelianParameterProductIso_hom_of, AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of]
  exact ConcreteCategory.congr_hom (ParameterCoproduct.ι_fold_app V _ P U
    (((prod.snd : F ⨯ I ⟶ I).app U).app n x).down) _

end CategoryTheory.PointedSimplicialPresheaf
