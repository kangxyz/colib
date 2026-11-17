/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Preadditive.IntegralConvolutionPresheaf
public import Colib.CategoryTheory.Preadditive.ConvolutionLinearity
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-!
# Integral convolution as an ordinary pointwise left Kan extension

The coend with the actual additive Hom group has the ordinary Day universal
property once the source category has binary biproducts, the first coefficient
presheaf is additive, and the indexing bifunctor is additive in its first
variable. The linearity lemma supplies the missing additive Hom relation.
Mathlib's existing pointwise Kan-extension interface is used directly.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct MonoidalCategory.ExternalProduct

universe u v w

namespace CategoryTheory.Preadditive.Convolution

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (F : C ⥤ C ⥤ C)

set_option quotPrecheck false in
local notation "L(" H ")" => (prodOpEquiv _).inverse ⋙ (Functor.uncurry.obj H).op

/-- A bilinear additive pairing has a descent to the actual integral tensor product. -/
def liftAddHom {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module ℤ A] [Module ℤ B] (f : A →+ B →+ C) : A ⊗[ℤ] B →+ C :=
  TensorProduct.liftAddHom f (fun n a b => by
    change f ((inferInstance : Module ℤ A).smul n a) b =
      f a ((inferInstance : Module ℤ B).smul n b)
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul, f.map_zsmul, (f a).map_zsmul]
    rfl)

/-- Convert an additive map to a linear map for the original integral module structures. -/
def integralModuleMap (A B : ModuleCat.{u} ℤ) (f : A →+ B) : A ⟶ B :=
  (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).preimage (AddCommGrpCat.ofHom f)

/-- The conversion preserves the actual pointwise map. -/
theorem integralModuleMap_apply (A B : ModuleCat.{u} ℤ) (f : A →+ B) (a : A) :
    integralModuleMap A B f a = f a :=
  ConcreteCategory.congr_hom ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map_preimage
    (AddCommGrpCat.ofHom f)) a

/-- The external product of the original coefficient modules. -/
def externalProduct (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    (C)ᵒᵖ × (C)ᵒᵖ ⥤ (ModuleCat.{max u v w} ℤ) :=
  (P ⋙ integerModuleFunctor) ⊠ (Q ⋙ integerModuleFunctor)

/-- The Day extension unit on a pair of input indices. -/
def kanExtensionUnitApp (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (U V : C) :
    ModuleCat.of ℤ ((P.obj (op U)) ⊗[ℤ] (Q.obj (op V))) ⟶
      integerModuleFunctor.obj ((presheaf F P Q).obj.obj
        (op ((F.obj U).obj V))) := by
  let X := (F.obj U).obj V
  let A := ModuleCat.of ℤ ((P.obj (op U)) ⊗[ℤ] (Q.obj (op V)))
  let B := integerModuleFunctor.obj ((presheaf F P Q).obj.obj (op X))
  let h (s : (P.obj (op U))) : (Q.obj (op V)) →+ B :=
    AddMonoidHom.mk' (fun t => generator F P Q X U V s t (𝟙 X))
      (fun t t' => generator_add_right F P Q s t t' (𝟙 X))
  let h' : (P.obj (op U)) →+ ((Q.obj (op V)) →+ B) :=
    AddMonoidHom.mk' h (fun s s' => by
      apply AddMonoidHom.ext
      intro t
      exact generator_add_left F P Q s s' t (𝟙 X))
  let m : A →+ B := liftAddHom h'
  exact integralModuleMap A B m

/-- The Day unit inserts the identity label into the coend. -/
theorem kanExtensionUnitApp_tmul (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (U V : C)
    (s : (P.obj (op U))) (t : (Q.obj (op V))) :
    kanExtensionUnitApp F P Q U V (s ⊗ₜ[ℤ] t) =
      generator F P Q ((F.obj U).obj V) U V s t (𝟙 _) := by
  unfold kanExtensionUnitApp
  exact (integralModuleMap_apply _ _ _ _).trans rfl

/-- The extension unit inserts the identity correspondence in the convolution generator. -/
def kanExtensionUnit (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    externalProduct P Q ⟶
      (L(F)) ⋙ (presheaf F P Q).obj ⋙ integerModuleFunctor where
  app YZ := kanExtensionUnitApp F P Q YZ.1.unop YZ.2.unop
  naturality YZ YZ' f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s t
    change kanExtensionUnitApp F P Q YZ'.1.unop YZ'.2.unop
        ((P.map (f.1.unop).op s) ⊗ₜ[ℤ] (Q.map (f.2.unop).op t)) =
      transfer F P Q (bifunctorMap F f.1.unop f.2.unop)
        (kanExtensionUnitApp F P Q YZ.1.unop YZ.2.unop (s ⊗ₜ[ℤ] t))
    rw [kanExtensionUnitApp_tmul, kanExtensionUnitApp_tmul,
      generator_transfer, transfer_generator, Category.id_comp,
      Category.comp_id]

/-- View any pointwise extension cocone on its literal coefficient and correspondence labels. -/
def coconePairing (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (X : C)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ externalProduct P Q))
    (Y Z : C) (a : X ⟶ (F.obj Y).obj Z) : (P.obj (op Y)) →+ (Q.obj (op Z)) →+ d.pt :=
  AddMonoidHom.mk'
    (fun s => AddMonoidHom.mk'
      (fun t => d.ι.app (CostructuredArrow.mk (Y := (op Y, op Z)) a.op) (s ⊗ₜ[ℤ] t))
      (fun t t' => by rw [TensorProduct.tmul_add, map_add]))
    (fun s s' => by
      ext t
      change d.ι.app (CostructuredArrow.mk (Y := (op Y, op Z)) a.op) ((s + s') ⊗ₜ[ℤ] t) = _
      rw [TensorProduct.add_tmul, map_add]
      rfl)

omit [Preadditive C] in
/-- The two original transfer relations are the naturality equations of the pointwise cocone. -/
theorem coconePairing_transfer (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (X : C)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ externalProduct P Q))
    {Y Y' Z Z' : C} (f : Y ⟶ Y') (g : Z ⟶ Z') (s : (P.obj (op Y'))) (t : (Q.obj (op Z')))
    (a : X ⟶ (F.obj Y).obj Z) :
    coconePairing F P Q X d Y Z a (P.map (f).op s) (Q.map (g).op t) =
      coconePairing F P Q X d Y' Z'
        (a ≫ bifunctorMap F f g) s t := by
  let m : CostructuredArrow.mk (S := L(F)) (Y := (op Y', op Z'))
      (a ≫ bifunctorMap F f g).op ⟶
      CostructuredArrow.mk (S := L(F)) (Y := (op Y, op Z)) a.op :=
    CostructuredArrow.homMk (f.op, g.op) rfl
  exact ConcreteCategory.congr_hom (d.ι.naturality m) (s ⊗ₜ[ℤ] t)

/-- The original coend and its realization as integral coefficients have the same sections. -/
def sectionModuleIso (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (X : C) :
    sections F P Q X ≅
      integerModuleFunctor.obj ((presheaf F P Q).obj.obj (op X)) := by
  let A := sections F P Q X
  let B := integerModuleFunctor.obj ((presheaf F P Q).obj.obj (op X))
  let f : A →+ B := AddMonoidHom.id A
  let g : B →+ A := AddMonoidHom.id B
  refine ⟨integralModuleMap A B f, integralModuleMap B A g, ?_, ?_⟩
  · ext a
    change integralModuleMap B A g (integralModuleMap A B f a) = a
    rw [integralModuleMap_apply, integralModuleMap_apply]
    rfl
  · ext b
    change integralModuleMap A B f (integralModuleMap B A g b) = b
    rw [integralModuleMap_apply, integralModuleMap_apply]
    rfl

@[simp]
theorem sectionModuleIso_hom_apply (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (X : C)
    (a : sections F P Q X) : (sectionModuleIso F P Q X).hom a = a :=
  integralModuleMap_apply _ _ _ _

@[simp]
theorem sectionModuleIso_inv_apply (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) (X : C)
    (a : integerModuleFunctor.obj ((presheaf F P Q).obj.obj (op X))) :
    (sectionModuleIso F P Q X).inv a = a :=
  integralModuleMap_apply _ _ _ _

variable [HasBinaryBiproducts C] [F.Additive]

/-- The cocone pairing extended to the three original coefficient modules. -/
def coconeDescPairing (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) [P.Additive] (X : C)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ externalProduct P Q))
    (Y Z : C) :
    ((diagram F P Q X).obj (op (Y, Z))).obj (Y, Z) ⟶ d.pt := by
  let e (s : (P.obj (op Y))) (t : (Q.obj (op Z))) :
      ULift.{max u v w} (X ⟶ (F.obj Y).obj Z) →+ d.pt :=
    AddMonoidHom.mk' (fun a => coconePairing F P Q X d Y Z a.down s t)
      (fun a b => pairing_add_hom F
        (coconePairing F P Q X d) (coconePairing_transfer F P Q X d)
        Y Z a.down b.down s t)
  let A := (P.obj (op Y)) ⊗[ℤ] (Q.obj (op Z))
  let B := ULift.{max u v w} (X ⟶ (F.obj Y).obj Z)
  let e₁ (s : (P.obj (op Y))) :
      (Q.obj (op Z)) →+ (B →+ d.pt) :=
    AddMonoidHom.mk' (e s) (fun t t' => by
      apply AddMonoidHom.ext
      intro a
      exact (coconePairing F P Q X d Y Z a.down s).map_add t t')
  let e₂ : (P.obj (op Y)) →+ ((Q.obj (op Z)) →+ B →+ d.pt) :=
    AddMonoidHom.mk' e₁ (fun s s' => by
      apply AddMonoidHom.ext
      intro t
      apply AddMonoidHom.ext
      intro a
      exact DFunLike.congr_fun ((coconePairing F P Q X d Y Z a.down).map_add s s') t)
  let l : A →+ B →+ d.pt := liftAddHom e₂
  let m : A ⊗[ℤ] B →+ d.pt := liftAddHom l
  exact integralModuleMap (ModuleCat.of ℤ (A ⊗[ℤ] B)) d.pt m

/-- On the literal triple generator, the descended pairing is the original cocone map. -/
theorem coconeDescPairing_tmul (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) [P.Additive] (X : C)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ externalProduct P Q))
    (Y Z : C) (s : (P.obj (op Y))) (t : (Q.obj (op Z))) (a : X ⟶ (F.obj Y).obj Z) :
    coconeDescPairing F P Q X d Y Z ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a) =
      coconePairing F P Q X d Y Z a s t := by
  unfold coconeDescPairing
  exact (integralModuleMap_apply _ _ _ _).trans rfl

/-- The two transfers give dinaturality of the linear cocone pairing. -/
theorem coconeDescPairing_dinatural (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) [P.Additive] (X : C)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ externalProduct P Q))
    {Y Y' Z Z' : C} (f : Y ⟶ Y') (g : Z ⟶ Z') :
    let D := diagram F P Q X
    let h : (Y, Z) ⟶ (Y', Z') := (f, g)
    (D.map h.op).app (Y, Z) ≫ coconeDescPairing F P Q X d Y Z =
      (D.obj (op (Y', Z'))).map h ≫ coconeDescPairing F P Q X d Y' Z' := by
  let h : (Y, Z) ⟶ (Y', Z') := (f, g)
  let A := coefficientModule P Q
  let B := homModule F X
  let W := ModuleCat.of ℤ (((P.obj (op Y')) ⊗[ℤ] (Q.obj (op Z'))) ⊗[ℤ]
    ULift.{max u v w} (X ⟶ (F.obj Y).obj Z))
  let l : W ⟶ d.pt := (A.map h.op ⊗ₘ B.map (𝟙 (Y, Z))) ≫
    coconeDescPairing F P Q X d Y Z
  let r : W ⟶ d.pt := (A.map (𝟙 (op (Y', Z'))) ⊗ₘ B.map h) ≫
    coconeDescPairing F P Q X d Y' Z'
  change l = r
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  rintro st ⟨a⟩
  refine TensorProduct.inductionOn st (fun s t => ?_) ?_
  · have h := coconePairing_transfer F P Q X d f g s t a
    change l ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a) =
      r ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a)
    dsimp only [l, r]
    rw [B.map_id, A.map_id]
    change coconeDescPairing F P Q X d Y Z
        (((P.map (f).op s) ⊗ₜ[ℤ] (Q.map (g).op t)) ⊗ₜ[ℤ] ULift.up a) =
      coconeDescPairing F P Q X d Y' Z'
        ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up (a ≫ bifunctorMap F f g))
    rw [coconeDescPairing_tmul, coconeDescPairing_tmul]
    exact h
  · intro s t hs ht
    rw [TensorProduct.add_tmul, l.hom.map_add, r.hom.map_add, hs, ht]

/-- The coend maps into any pointwise extension cocone by its literal generators. -/
def coconeDesc (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) [P.Additive] (X : C)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ externalProduct P Q)) :
    sections F P Q X ⟶ d.pt :=
  coend.desc («F» := diagram F P Q X)
    (fun yz => coconeDescPairing F P Q X d yz.1 yz.2)
    (fun i j (fg : i ⟶ j) => coconeDescPairing_dinatural F P Q X d fg.1 fg.2)

/-- The descending map evaluates the supplied cocone on the same labelled generator. -/
theorem coconeDesc_generator (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) [P.Additive] (X : C)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ externalProduct P Q))
    (Y Z : C) (s : (P.obj (op Y))) (t : (Q.obj (op Z))) (a : X ⟶ (F.obj Y).obj Z) :
    coconeDesc F P Q X d (generator F P Q X Y Z s t a) =
      coconePairing F P Q X d Y Z a s t := by
  change (coend.ι (diagram F P Q X) (Y, Z) ≫ coconeDesc F P Q X d)
      ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a) = _
  let D := diagram F P Q X
  let f (YZ : C × C) := coconeDescPairing F P Q X d YZ.1 YZ.2
  have hd {i j : C × C} (g : i ⟶ j) :
      (D.map g.op).app i ≫ f i = (D.obj (op j)).map g ≫ f j :=
    coconeDescPairing_dinatural F P Q X d g.1 g.2
  have h := coend.ι_desc (F := D) f (fun _ _ g => hd g) (Y, Z)
  let w : ((D.obj (op (Y, Z))).obj (Y, Z)) := (s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a
  have h₀ := ConcreteCategory.congr_hom h w
  exact h₀.trans (coconeDescPairing_tmul F P Q X d Y Z s t a)

/-- The native integral convolution is the pointwise left Kan extension of the external product. -/
def isPointwiseLeftKanExtension (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) [P.Additive] :
    (Functor.LeftExtension.mk _
      (kanExtensionUnit F P Q)).IsPointwiseLeftKanExtension := by
  intro X
  let X₀ := X.unop
  change Limits.IsColimit ((Functor.LeftExtension.mk
    ((presheaf F P Q).obj ⋙ integerModuleFunctor)
    (kanExtensionUnit F P Q)).coconeAt (op X₀))
  let e := sectionModuleIso F P Q X₀
  refine
    { desc := fun d => e.inv ≫ coconeDesc F P Q X₀ d
      fac := ?_
      uniq := ?_ }
  · intro d j
    obtain ⟨⟨Y, Z⟩, a, rfl⟩ := CostructuredArrow.mk_surjective j
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s t
    change (P.obj (op Y.unop)) at s
    change (Q.obj (op Z.unop)) at t
    change coconeDesc F P Q X₀ d
      (e.inv (transfer F P Q a.unop
        (kanExtensionUnitApp F P Q Y.unop Z.unop (s ⊗ₜ[ℤ] t)))) = _
    rw [sectionModuleIso_inv_apply, kanExtensionUnitApp_tmul]
    let b : X₀ ⟶ (F.obj Y.unop).obj Z.unop := a.unop
    let j := generator F P Q X₀ Y.unop Z.unop s t
    have ha := transfer_generator F P Q b Y.unop Z.unop s t (𝟙 _)
    have hb : j (b ≫ 𝟙 _) = j b := congrArg j (Category.comp_id b)
    exact (congrArg (coconeDesc F P Q X₀ d) (ha.trans hb)).trans
      (coconeDesc_generator F P Q X₀ d Y.unop Z.unop s t b)
  · intro d f hf
    apply (cancel_epi e.hom).1
    change e.hom ≫ f = e.hom ≫ e.inv ≫ coconeDesc F P Q X₀ d
    rw [e.hom_inv_id_assoc]
    apply sections_hom_ext
    intro Y Z s t a
    have h := ConcreteCategory.congr_hom
      (hf (CostructuredArrow.mk (S := L(F)) (Y := (op Y, op Z)) a.op)) (s ⊗ₜ[ℤ] t)
    change f (transfer F P Q a
        (kanExtensionUnitApp F P Q Y Z (s ⊗ₜ[ℤ] t))) =
      coconePairing F P Q X₀ d Y Z a s t at h
    rw [kanExtensionUnitApp_tmul, transfer_generator, Category.comp_id] at h
    change f (e.hom (generator F P Q X₀ Y Z s t a)) =
      coconeDesc F P Q X₀ d (generator F P Q X₀ Y Z s t a)
    rw [sectionModuleIso_hom_apply, coconeDesc_generator]
    exact h

end CategoryTheory.Preadditive.Convolution
