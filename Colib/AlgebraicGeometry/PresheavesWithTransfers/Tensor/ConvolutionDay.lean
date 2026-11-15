/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionDayLinearity
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-!
# The integral coend as a pointwise Kan extension

For the actual signed correspondence bifunctor, the selected integral
coend has the ordinary pointwise Day convolution property. Linearity
in the correspondence label follows from the native binary biproducts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct MonoidalCategory.ExternalProduct

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "MZ(" K ")" => IntegerCoefficients K

variable (F : Cor k ⥤ Cor k ⥤ Cor k)

set_option quotPrecheck false in
local notation "L(" H ")" => (prodOpEquiv _).inverse ⋙ (Functor.uncurry.obj H).op

/-- A bilinear additive pairing has a descent to the actual integral tensor product. -/
def convolutionLiftAddHom {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module ℤ A] [Module ℤ B] (f : A →+ B →+ C) : A ⊗[ℤ] B →+ C :=
  TensorProduct.liftAddHom f (fun n a b => by
    change f ((inferInstance : Module ℤ A).smul n a) b =
      f a ((inferInstance : Module ℤ B).smul n b)
    rw [int_smul_eq_zsmul, int_smul_eq_zsmul, f.map_zsmul, (f a).map_zsmul]
    rfl)

/-- Convert an additive map to a linear map for the original integral module structures. -/
def convolutionIntegralModuleMap (A B : ModuleCat.{u} ℤ) (f : A →+ B) : A ⟶ B :=
  (forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).preimage (AddCommGrpCat.ofHom f)

/-- The conversion preserves the actual pointwise map. -/
theorem convolutionIntegralModuleMap_apply (A B : ModuleCat.{u} ℤ) (f : A →+ B) (a : A) :
    convolutionIntegralModuleMap A B f a = f a :=
  ConcreteCategory.congr_hom ((forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}).map_preimage
    (AddCommGrpCat.ofHom f)) a

/-- The external product of the original coefficient modules. -/
def convolutionExternalProduct (P Q : PST(k)) :
    (Cor k)ᵒᵖ × (Cor k)ᵒᵖ ⥤ MZ(k) :=
  (P.obj ⋙ integerModuleFunctor) ⊠ (Q.obj ⋙ integerModuleFunctor)

/-- The Day extension unit on a pair of input indices. -/
def convolutionKanExtensionUnitApp (P Q : PST(k)) (U V : Cor k) :
    ModuleCat.of ℤ (sections P U ⊗[ℤ] sections Q V) ⟶
      integerModuleFunctor.obj ((convolutionPresheaf F P Q).obj.obj
        (op ((F.obj U).obj V))) := by
  let X := (F.obj U).obj V
  let A := ModuleCat.of ℤ (sections P U ⊗[ℤ] sections Q V)
  let B := integerModuleFunctor.obj ((convolutionPresheaf F P Q).obj.obj (op X))
  let h (s : sections P U) : sections Q V →+ B :=
    AddMonoidHom.mk' (fun t => convolutionGenerator F P Q X U V s t (𝟙 X))
      (fun t t' => convolutionGenerator_add_right F P Q s t t' (𝟙 X))
  let h' : sections P U →+ (sections Q V →+ B) :=
    AddMonoidHom.mk' h (fun s s' => by
      apply AddMonoidHom.ext
      intro t
      exact convolutionGenerator_add_left F P Q s s' t (𝟙 X))
  let m : A →+ B := convolutionLiftAddHom h'
  exact convolutionIntegralModuleMap A B m

/-- The Day unit inserts the identity label into the coend. -/
theorem convolutionKanExtensionUnitApp_tmul (P Q : PST(k)) (U V : Cor k)
    (s : sections P U) (t : sections Q V) :
    convolutionKanExtensionUnitApp F P Q U V (s ⊗ₜ[ℤ] t) =
      convolutionGenerator F P Q ((F.obj U).obj V) U V s t (𝟙 _) := by
  unfold convolutionKanExtensionUnitApp
  exact (convolutionIntegralModuleMap_apply _ _ _ _).trans rfl

/-- The extension unit inserts the identity correspondence in the convolution generator. -/
def convolutionKanExtensionUnit (P Q : PST(k)) :
    convolutionExternalProduct P Q ⟶
      (L(F)) ⋙ (convolutionPresheaf F P Q).obj ⋙ integerModuleFunctor where
  app YZ := convolutionKanExtensionUnitApp F P Q YZ.1.unop YZ.2.unop
  naturality YZ YZ' f := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s t
    change convolutionKanExtensionUnitApp F P Q YZ'.1.unop YZ'.2.unop
        ((transfer P f.1.unop s) ⊗ₜ[ℤ] (transfer Q f.2.unop t)) =
      convolutionTransfer F P Q (convolutionCorrespondenceMap F f.1.unop f.2.unop)
        (convolutionKanExtensionUnitApp F P Q YZ.1.unop YZ.2.unop (s ⊗ₜ[ℤ] t))
    rw [convolutionKanExtensionUnitApp_tmul, convolutionKanExtensionUnitApp_tmul,
      convolutionGenerator_transfer, convolutionTransfer_generator, Category.id_comp,
      Category.comp_id]

/-- View any pointwise extension cocone on its literal coefficient and correspondence labels. -/
def convolutionCoconePairing (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q))
    (Y Z : Cor k) (a : X ⟶ (F.obj Y).obj Z) : sections P Y →+ sections Q Z →+ d.pt :=
  AddMonoidHom.mk'
    (fun s => AddMonoidHom.mk'
      (fun t => d.ι.app (CostructuredArrow.mk (Y := (op Y, op Z)) a.op) (s ⊗ₜ[ℤ] t))
      (fun t t' => by rw [TensorProduct.tmul_add, map_add]))
    (fun s s' => by
      ext t
      change d.ι.app (CostructuredArrow.mk (Y := (op Y, op Z)) a.op) ((s + s') ⊗ₜ[ℤ] t) = _
      rw [TensorProduct.add_tmul, map_add]
      rfl)

/-- The two original transfer relations are the naturality equations of the pointwise cocone. -/
theorem convolutionCoconePairing_transfer (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q))
    {Y Y' Z Z' : Cor k} (f : Y ⟶ Y') (g : Z ⟶ Z') (s : sections P Y') (t : sections Q Z')
    (a : X ⟶ (F.obj Y).obj Z) :
    convolutionCoconePairing F P Q X d Y Z a (transfer P f s) (transfer Q g t) =
      convolutionCoconePairing F P Q X d Y' Z'
        (a ≫ convolutionCorrespondenceMap F f g) s t := by
  let m : CostructuredArrow.mk (S := L(F)) (Y := (op Y', op Z'))
      (a ≫ convolutionCorrespondenceMap F f g).op ⟶
      CostructuredArrow.mk (S := L(F)) (Y := (op Y, op Z)) a.op :=
    CostructuredArrow.homMk (f.op, g.op) rfl
  exact ConcreteCategory.congr_hom (d.ι.naturality m) (s ⊗ₜ[ℤ] t)

/-- The original coend and its realization as integral coefficients have the same sections. -/
def convolutionSectionModuleIso (P Q : PST(k)) (X : Cor k) :
    convolutionSections F P Q X ≅
      integerModuleFunctor.obj ((convolutionPresheaf F P Q).obj.obj (op X)) := by
  let A := convolutionSections F P Q X
  let B := integerModuleFunctor.obj ((convolutionPresheaf F P Q).obj.obj (op X))
  let f : A →+ B := AddMonoidHom.id A
  let g : B →+ A := AddMonoidHom.id B
  refine ⟨convolutionIntegralModuleMap A B f, convolutionIntegralModuleMap B A g, ?_, ?_⟩
  · ext a
    change convolutionIntegralModuleMap B A g (convolutionIntegralModuleMap A B f a) = a
    rw [convolutionIntegralModuleMap_apply, convolutionIntegralModuleMap_apply]
    rfl
  · ext b
    change convolutionIntegralModuleMap A B f (convolutionIntegralModuleMap B A g b) = b
    rw [convolutionIntegralModuleMap_apply, convolutionIntegralModuleMap_apply]
    rfl

@[simp]
theorem convolutionSectionModuleIso_hom_apply (P Q : PST(k)) (X : Cor k)
    (a : convolutionSections F P Q X) : (convolutionSectionModuleIso F P Q X).hom a = a :=
  convolutionIntegralModuleMap_apply _ _ _ _

@[simp]
theorem convolutionSectionModuleIso_inv_apply (P Q : PST(k)) (X : Cor k)
    (a : integerModuleFunctor.obj ((convolutionPresheaf F P Q).obj.obj (op X))) :
    (convolutionSectionModuleIso F P Q X).inv a = a :=
  convolutionIntegralModuleMap_apply _ _ _ _

variable [F.Additive]

/-- The cocone pairing extended to the three original coefficient modules. -/
def convolutionCoconeDescPairing (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q))
    (Y Z : Cor k) :
    ((convolutionDiagram F P Q X).obj (op (Y, Z))).obj (Y, Z) ⟶ d.pt := by
  let e (s : sections P Y) (t : sections Q Z) :
      ULift.{u + 1} (X ⟶ (F.obj Y).obj Z) →+ d.pt :=
    AddMonoidHom.mk' (fun a => convolutionCoconePairing F P Q X d Y Z a.down s t)
      (fun a b => convolutionPairing_add_correspondence F
        (convolutionCoconePairing F P Q X d) (convolutionCoconePairing_transfer F P Q X d)
        Y Z a.down b.down s t)
  let A := sections P Y ⊗[ℤ] sections Q Z
  let B := ULift.{u + 1} (X ⟶ (F.obj Y).obj Z)
  let e₁ (s : sections P Y) :
      sections Q Z →+ (B →+ d.pt) :=
    AddMonoidHom.mk' (e s) (fun t t' => by
      apply AddMonoidHom.ext
      intro a
      exact (convolutionCoconePairing F P Q X d Y Z a.down s).map_add t t')
  let e₂ : sections P Y →+ (sections Q Z →+ B →+ d.pt) :=
    AddMonoidHom.mk' e₁ (fun s s' => by
      apply AddMonoidHom.ext
      intro t
      apply AddMonoidHom.ext
      intro a
      exact DFunLike.congr_fun ((convolutionCoconePairing F P Q X d Y Z a.down).map_add s s') t)
  let l : A →+ B →+ d.pt := convolutionLiftAddHom e₂
  let m : A ⊗[ℤ] B →+ d.pt := convolutionLiftAddHom l
  exact convolutionIntegralModuleMap (ModuleCat.of ℤ (A ⊗[ℤ] B)) d.pt m

/-- On the literal triple generator, the descended pairing is the original cocone map. -/
theorem convolutionCoconeDescPairing_tmul (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q))
    (Y Z : Cor k) (s : sections P Y) (t : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    convolutionCoconeDescPairing F P Q X d Y Z ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a) =
      convolutionCoconePairing F P Q X d Y Z a s t := by
  unfold convolutionCoconeDescPairing
  exact (convolutionIntegralModuleMap_apply _ _ _ _).trans rfl

/-- The two transfers give dinaturality of the linear cocone pairing. -/
theorem convolutionCoconeDescPairing_dinatural (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q))
    {Y Y' Z Z' : Cor k} (f : Y ⟶ Y') (g : Z ⟶ Z') :
    let D := convolutionDiagram F P Q X
    let h : (Y, Z) ⟶ (Y', Z') := (f, g)
    (D.map h.op).app (Y, Z) ≫ convolutionCoconeDescPairing F P Q X d Y Z =
      (D.obj (op (Y', Z'))).map h ≫ convolutionCoconeDescPairing F P Q X d Y' Z' := by
  let h : (Y, Z) ⟶ (Y', Z') := (f, g)
  let A := convolutionCoefficientModule P Q
  let B := convolutionCorrespondenceModule F X
  let W := ModuleCat.of ℤ ((sections P Y' ⊗[ℤ] sections Q Z') ⊗[ℤ]
    ULift.{u + 1} (X ⟶ (F.obj Y).obj Z))
  let l : W ⟶ d.pt := (A.map h.op ⊗ₘ B.map (𝟙 (Y, Z))) ≫
    convolutionCoconeDescPairing F P Q X d Y Z
  let r : W ⟶ d.pt := (A.map (𝟙 (op (Y', Z'))) ⊗ₘ B.map h) ≫
    convolutionCoconeDescPairing F P Q X d Y' Z'
  change l = r
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  rintro st ⟨a⟩
  refine TensorProduct.inductionOn st (fun s t => ?_) ?_
  · have h := convolutionCoconePairing_transfer F P Q X d f g s t a
    change l ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a) =
      r ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a)
    dsimp only [l, r]
    rw [B.map_id, A.map_id]
    change convolutionCoconeDescPairing F P Q X d Y Z
        (((transfer P f s) ⊗ₜ[ℤ] (transfer Q g t)) ⊗ₜ[ℤ] ULift.up a) =
      convolutionCoconeDescPairing F P Q X d Y' Z'
        ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up (a ≫ convolutionCorrespondenceMap F f g))
    rw [convolutionCoconeDescPairing_tmul, convolutionCoconeDescPairing_tmul]
    exact h
  · intro s t hs ht
    rw [TensorProduct.add_tmul, l.hom.map_add, r.hom.map_add, hs, ht]

/-- The coend maps into any pointwise extension cocone by its literal generators. -/
def convolutionCoconeDesc (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q)) :
    convolutionSections F P Q X ⟶ d.pt :=
  coend.desc («F» := convolutionDiagram F P Q X)
    (fun yz => convolutionCoconeDescPairing F P Q X d yz.1 yz.2)
    (fun i j (fg : i ⟶ j) => convolutionCoconeDescPairing_dinatural F P Q X d fg.1 fg.2)

/-- The descending map evaluates the supplied cocone on the same labelled generator. -/
theorem convolutionCoconeDesc_generator (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q))
    (Y Z : Cor k) (s : sections P Y) (t : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    convolutionCoconeDesc F P Q X d (convolutionGenerator F P Q X Y Z s t a) =
      convolutionCoconePairing F P Q X d Y Z a s t := by
  change (coend.ι (convolutionDiagram F P Q X) (Y, Z) ≫ convolutionCoconeDesc F P Q X d)
      ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a) = _
  let D := convolutionDiagram F P Q X
  let f (YZ : Cor k × Cor k) := convolutionCoconeDescPairing F P Q X d YZ.1 YZ.2
  have hd {i j : Cor k × Cor k} (g : i ⟶ j) :
      (D.map g.op).app i ≫ f i = (D.obj (op j)).map g ≫ f j :=
    convolutionCoconeDescPairing_dinatural F P Q X d g.1 g.2
  have h := coend.ι_desc (F := D) f (fun _ _ g => hd g) (Y, Z)
  let w : ((D.obj (op (Y, Z))).obj (Y, Z)) := (s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a
  have h₀ := ConcreteCategory.congr_hom h w
  exact h₀.trans (convolutionCoconeDescPairing_tmul F P Q X d Y Z s t a)

/-- The native integral convolution is the pointwise left Kan extension of the external product. -/
def convolutionIsPointwiseLeftKanExtension (P Q : PST(k)) :
    (Functor.LeftExtension.mk _
      (convolutionKanExtensionUnit F P Q)).IsPointwiseLeftKanExtension := by
  intro X
  let X₀ := X.unop
  change Limits.IsColimit ((Functor.LeftExtension.mk
    ((convolutionPresheaf F P Q).obj ⋙ integerModuleFunctor)
    (convolutionKanExtensionUnit F P Q)).coconeAt (op X₀))
  let e := convolutionSectionModuleIso F P Q X₀
  refine
    { desc := fun d => e.inv ≫ convolutionCoconeDesc F P Q X₀ d
      fac := ?_
      uniq := ?_ }
  · intro d j
    obtain ⟨⟨Y, Z⟩, a, rfl⟩ := CostructuredArrow.mk_surjective j
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro s t
    change sections P Y.unop at s
    change sections Q Z.unop at t
    change convolutionCoconeDesc F P Q X₀ d
      (e.inv (convolutionTransfer F P Q a.unop
        (convolutionKanExtensionUnitApp F P Q Y.unop Z.unop (s ⊗ₜ[ℤ] t)))) = _
    rw [convolutionSectionModuleIso_inv_apply, convolutionKanExtensionUnitApp_tmul]
    let b : X₀ ⟶ (F.obj Y.unop).obj Z.unop := a.unop
    let j := convolutionGenerator F P Q X₀ Y.unop Z.unop s t
    have ha := convolutionTransfer_generator F P Q b Y.unop Z.unop s t (𝟙 _)
    have hb : j (b ≫ 𝟙 _) = j b := congrArg j (Category.comp_id b)
    exact (congrArg (convolutionCoconeDesc F P Q X₀ d) (ha.trans hb)).trans
      (convolutionCoconeDesc_generator F P Q X₀ d Y.unop Z.unop s t b)
  · intro d f hf
    apply (cancel_epi e.hom).1
    change e.hom ≫ f = e.hom ≫ e.inv ≫ convolutionCoconeDesc F P Q X₀ d
    rw [e.hom_inv_id_assoc]
    apply convolutionSections_hom_ext
    intro Y Z s t a
    have h := ConcreteCategory.congr_hom
      (hf (CostructuredArrow.mk (S := L(F)) (Y := (op Y, op Z)) a.op)) (s ⊗ₜ[ℤ] t)
    change f (convolutionTransfer F P Q a
        (convolutionKanExtensionUnitApp F P Q Y Z (s ⊗ₜ[ℤ] t))) =
      convolutionCoconePairing F P Q X₀ d Y Z a s t at h
    rw [convolutionKanExtensionUnitApp_tmul, convolutionTransfer_generator, Category.comp_id] at h
    change f (e.hom (convolutionGenerator F P Q X₀ Y Z s t a)) =
      convolutionCoconeDesc F P Q X₀ d (convolutionGenerator F P Q X₀ Y Z s t a)
    rw [convolutionSectionModuleIso_hom_apply, convolutionCoconeDesc_generator]
    exact h

end AlgebraicGeometry.PresheafWithTransfers
