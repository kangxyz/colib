/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Preadditive.IntegralConvolutionRepresented
public import Colib.CategoryTheory.Preadditive.IntegralConvolutionDayComparison
public import Mathlib.CategoryTheory.Monoidal.DayConvolution
public import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Associator of the signed convolution

Mathlib's Day associator applies to the pointwise extension on the
original integral coefficient modules. Full faithfulness transports
it back to the existing convolution of transfer presheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open MonoidalCategory
open scoped MonoidalCategory.ExternalProduct DayConvolution TensorProduct

universe u v w

namespace CategoryTheory.Preadditive.ConvolutionRepresented

variable {C : Type u} [Category.{v} C] [Preadditive C]

open CategoryTheory.Preadditive.Convolution (integerModuleFunctor)

/-- Sections of a bundled additive presheaf at an object. -/
abbrev sections (P : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) (X : C) := P.obj.obj (op X)

/-- The convolution map induced by a pair of coefficient morphisms. -/
abbrev convolutionMap := @Convolution.map.{u, v, w} C _ _

theorem convolutionMap_generator (F : C ⥤ C ⥤ C)
    {P P' Q Q' : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}}
    (f : P ⟶ P') (g : Q ⟶ Q') (X Y Z : C)
    (s : P.obj.obj (op Y)) (t : Q.obj.obj (op Z)) (a : X ⟶ (F.obj Y).obj Z) :
    (Convolution.map F f g).hom.app (op X) (Convolution.generator F P.obj Q.obj X Y Z s t a) =
      Convolution.generator F P'.obj Q'.obj X Y Z
        (f.hom.app (op Y) s) (g.hom.app (op Z) t) a :=
  Convolution.map_generator F f g X Y Z s t a

theorem convolutionPresheaf_hom_ext (F : C ⥤ C ⥤ C)
    {P Q R : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}}
    {f g : Convolution.presheaf F P.obj Q.obj ⟶ R}
    (h : ∀ (X Y Z : C) (s : P.obj.obj (op Y)) (t : Q.obj.obj (op Z))
      (a : X ⟶ (F.obj Y).obj Z),
      f.hom.app (op X) (Convolution.generator F P.obj Q.obj X Y Z s t a) =
        g.hom.app (op X) (Convolution.generator F P.obj Q.obj X Y Z s t a)) : f = g :=
  Convolution.presheaf_hom_ext F h

/-- The external tensor product of bundled additive coefficients. -/
abbrev convolutionExternalProduct (P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) :=
  Convolution.externalProduct P.obj Q.obj

/-- The integral Day extension unit for bundled additive coefficients. -/
abbrev convolutionKanExtensionUnitApp (F : C ⥤ C ⥤ C)
    (P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) :=
  Convolution.kanExtensionUnitApp F P.obj Q.obj

theorem convolutionKanExtensionUnitApp_tmul (F : C ⥤ C ⥤ C)
    (P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) (U V : C)
    (s : P.obj.obj (op U)) (t : Q.obj.obj (op V)) :
    Convolution.kanExtensionUnitApp F P.obj Q.obj U V (s ⊗ₜ[ℤ] t) =
      Convolution.generator F P.obj Q.obj ((F.obj U).obj V) U V s t (𝟙 _) :=
  Convolution.kanExtensionUnitApp_tmul F P.obj Q.obj U V s t

/-- The contravariant action of a bundled additive presheaf. -/
abbrev transfer (P : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) {X Y : C} (f : X ⟶ Y) :=
  P.obj.map f.op

@[simp] theorem transfer_id (P : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) (X : C) :
    transfer P (𝟙 X) = 𝟙 _ := by simp [transfer]

theorem transfer_naturality {P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}}
    (f : P ⟶ Q) {X Y : C} (a : X ⟶ Y) :
    transfer P a ≫ f.hom.app (op X) = f.hom.app (op Y) ≫ transfer Q a :=
  f.hom.naturality a.op

theorem convolutionGenerator_transfer (F : C ⥤ C ⥤ C)
    (P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) {X Y Y' Z Z' : C}
    (f : Y ⟶ Y') (g : Z ⟶ Z') (s : sections P Y') (t : sections Q Z')
    (a : X ⟶ (F.obj Y).obj Z) :
    convolutionGenerator F P Q X Y Z (transfer P f s) (transfer Q g t) a =
      convolutionGenerator F P Q X Y' Z' s t (a ≫ convolutionCorrespondenceMap F f g) :=
  Convolution.generator_transfer.{u, v, w} F P.obj Q.obj f g s t a

theorem convolutionPresheaf_transfer_generator (F : C ⥤ C ⥤ C)
    (P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) {X X' : C} (β : X' ⟶ X)
    (Y Z : C) (s : sections P Y) (t : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    transfer (convolutionPresheaf F P Q) β (convolutionGenerator F P Q X Y Z s t a) =
      convolutionGenerator F P Q X' Y Z s t (β ≫ a) :=
  Convolution.transfer_generator.{u, v, w} F P.obj Q.obj β Y Z s t a

theorem convolutionMap_id (F : C ⥤ C ⥤ C)
    (P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) :
    Convolution.map F (𝟙 P) (𝟙 Q) = 𝟙 _ :=
  Convolution.map_id F P Q

theorem convolutionMap_comp (F : C ⥤ C ⥤ C)
    {P P' P'' Q Q' Q'' : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}}
    (f : P ⟶ P') (f' : P' ⟶ P'') (g : Q ⟶ Q') (g' : Q' ⟶ Q'') :
    Convolution.map F (f ≫ f') (g ≫ g') =
      Convolution.map F f g ≫ Convolution.map F f' g' :=
  Convolution.map_comp F f f' g g'

theorem convolutionSections_hom_ext (F : C ⥤ C ⥤ C)
    (P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) (X : C)
    {M : ModuleCat.{max u v w} ℤ} {f g : Convolution.sections F P.obj Q.obj X ⟶ M}
    (h : ∀ (Y Z : C) (s : P.obj.obj (op Y)) (t : Q.obj.obj (op Z))
      (a : X ⟶ (F.obj Y).obj Z),
      f (Convolution.generator F P.obj Q.obj X Y Z s t a) =
        g (Convolution.generator F P.obj Q.obj X Y Z s t a)) : f = g :=
  Convolution.sections_hom_ext F P.obj Q.obj X h

theorem convolutionTransfer_generator (F : C ⥤ C ⥤ C)
    (P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) {X X' : C} (β : X' ⟶ X)
    (Y Z : C) (s : P.obj.obj (op Y)) (t : Q.obj.obj (op Z)) (a : X ⟶ (F.obj Y).obj Z) :
    Convolution.transfer F P.obj Q.obj β (Convolution.generator F P.obj Q.obj X Y Z s t a) =
      Convolution.generator F P.obj Q.obj X' Y Z s t (β ≫ a) :=
  Convolution.transfer_generator F P.obj Q.obj β Y Z s t a

theorem convolutionGenerator_add_left (F : C ⥤ C ⥤ C)
    (P Q : Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) {X Y Z : C}
    (s s' : P.obj.obj (op Y)) (t : Q.obj.obj (op Z)) (a : X ⟶ (F.obj Y).obj Z) :
    Convolution.generator F P.obj Q.obj X Y Z (s + s') t a =
      Convolution.generator F P.obj Q.obj X Y Z s t a +
        Convolution.generator F P.obj Q.obj X Y Z s' t a :=
  Convolution.generator_add_left F P.obj Q.obj s s' t a

/-- Regard an additive map of integer modules as a module morphism. -/
abbrev convolutionIntegralModuleMap := Convolution.integralModuleMap.{w}

theorem convolutionIntegralModuleMap_apply (A B : ModuleCat.{w} ℤ) (f : A →+ B) (a : A) :
    Convolution.integralModuleMap A B f a = f a :=
  Convolution.integralModuleMap_apply A B f a

/-- Regard the original additive transfer coefficients as ordinary integer-module
    presheaves. -/
def convolutionForget : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}) ⥤ ((C)ᵒᵖ ⥤
    (ModuleCat.{max u v w} ℤ)) :=
  AdditiveFunctor.forget Cᵒᵖ AddCommGrpCat.{max u v w} ⋙
    (Functor.whiskeringRight _ _ _).obj integerModuleFunctor

/-- The coefficient realization is fully faithful. -/
def convolutionForgetFullyFaithful : (convolutionForget (C := C)).FullyFaithful := by
  let V := forget₂ ((ModuleCat.{max u v w} ℤ)) AddCommGrpCat.{max u v w}
  let e : integerModuleFunctor ⋙ V ≅ 𝟭 AddCommGrpCat.{max u v w} :=
    NatIso.ofComponents (fun _ => Iso.refl _)
  let h := (Functor.FullyFaithful.id AddCommGrpCat.{max u v w}).ofIso e.symm
  let hM := Functor.FullyFaithful.ofCompFaithful h
  exact (ObjectProperty.fullyFaithfulι (additiveFunctor (C)ᵒᵖ AddCommGrpCat.{max u v
      w})).comp
    (hM.whiskeringRight (C)ᵒᵖ)

variable [HasBinaryBiproducts C] [MonoidalCategory (C)] [MonoidalPreadditive (C)]

local notation "F" => curriedTensor C

/-- The product on opposite correspondences is the opposite of the selected signed product. -/
def convolutionOppositeTensorIso :
    (prodOpEquiv (D := C) (C)).inverse ⋙
        (Functor.uncurry.obj (F)).op ≅ tensor (C)ᵒᵖ :=
  CategoryTheory.Preadditive.Convolution.oppositeTensorIso.{u, v} (C := C)

/-- The pointwise extension unit along the product on opposite correspondences. -/
def convolutionDayUnit (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    convolutionExternalProduct P Q ⟶
      tensor (C)ᵒᵖ ⋙ (convolutionForget (C := C)).obj (convolutionPresheaf (F) P Q) :=
  CategoryTheory.Preadditive.Convolution.dayUnit.{u, v, w} P.obj Q.obj

/-- The original integral coend has the pointwise extension property for the opposite
    product. -/
theorem convolutionDayUnit_isPointwiseLeftKanExtension (P Q : (Cᵒᵖ ⥤+
    AddCommGrpCat.{max u v w})) (X : (C)ᵒᵖ) :
    Nonempty ((Functor.LeftExtension.mk _
      (convolutionDayUnit P Q)).IsPointwiseLeftKanExtensionAt X) :=
  CategoryTheory.Preadditive.Convolution.dayUnit_isPointwiseLeftKanExtension.{u, v, w}
    P.obj Q.obj X

/-- The original convolution is a pointwise Day extension of the coefficient tensor. -/
@[instance_reducible]
def convolutionDayComparison (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    DayConvolution ((convolutionForget (C := C)).obj P) (convolutionForget.obj Q) where
  convolution := (convolutionForget (C := C)).obj (convolutionPresheaf (F) P Q)
  unit := convolutionDayUnit P Q
  isPointwiseLeftKanExtensionUnit X :=
    Classical.choice (convolutionDayUnit_isPointwiseLeftKanExtension P Q X)

/-- The Day extension unit acts on the same literal identity generator as the coend unit. -/
theorem convolutionDayUnit_tmul (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) (X Y : C)
    (x : sections P X) (y : sections Q Y) :
    let W := convolutionForget (C := C)
    letI := convolutionDayComparison P Q
    (DayConvolution.unit (W.obj P) (W.obj Q)).app (op X, op Y) (x ⊗ₜ[ℤ] y) =
      convolutionGenerator (F) P Q (X ⊗ Y) X Y x y (𝟙 _) := by
  intro W
  let := convolutionDayComparison P Q
  let G := W.obj (convolutionPresheaf (F) P Q)
  change G.map (𝟙 (op (X ⊗ Y))) (convolutionKanExtensionUnitApp (F) P Q X Y
      (x ⊗ₜ[ℤ] y)) = _
  rw [G.map_id, ModuleCat.id_apply]
  exact convolutionKanExtensionUnitApp_tmul (F) P Q X Y x y

/-- The Day map is the realization of the actual convolution coefficient map. -/
theorem convolutionForget_map_eq_dayMap {P P' Q Q' : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v
    w})} (f : P ⟶ P') (g : Q ⟶ Q') :
    let W := convolutionForget (C := C)
    letI := convolutionDayComparison P Q
    letI := convolutionDayComparison P' Q'
    W.map (convolutionMap (F) f g) = DayConvolution.map (W.map f) (W.map g) := by
  intro W
  let := convolutionDayComparison P Q
  let := convolutionDayComparison P' Q'
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit (W.obj P) (W.obj Q))
  apply NatTrans.ext
  funext YZ
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro p q
  obtain ⟨Y, Z⟩ := YZ
  change sections P Y.unop at p
  change sections Q Z.unop at q
  let X := Y.unop ⊗ Z.unop
  let U := DayConvolution.unit (W.obj P) (W.obj Q)
  let V := DayConvolution.unit (W.obj P') (W.obj Q')
  let m := W.map (convolutionMap (F) f g)
  let n := DayConvolution.map (W.map f) (W.map g)
  let p' := f.hom.app Y p
  let q' := g.hom.app Z q
  have h₁ := convolutionDayUnit_tmul P Q Y.unop Z.unop p q
  have h₂ := convolutionDayUnit_tmul P' Q' Y.unop Z.unop p' q'
  have hm := convolutionMap_generator (F) f g X Y.unop Z.unop p q (𝟙 _)
  have h := ConcreteCategory.congr_hom
    (DayConvolution.unit_app_map_app (W.map f) (W.map g) Y Z) (p ⊗ₜ[ℤ] q)
  change n.app (op X) (U.app (Y, Z) (p ⊗ₜ[ℤ] q)) =
    V.app (Y, Z) (p' ⊗ₜ[ℤ] q') at h
  change m.app (op X) (U.app (Y, Z) (p ⊗ₜ[ℤ] q)) =
    n.app (op X) (U.app (Y, Z) (p ⊗ₜ[ℤ] q))
  exact ((congrArg (m.app (op X)) h₁).trans (hm.trans h₂.symm)).trans h.symm

/-- The associator on the original integral coend of transfer presheaves. -/
def convolutionAssociator (P Q R : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    convolutionPresheaf (F) (convolutionPresheaf (F) P Q) R ≅
      convolutionPresheaf (F) P (convolutionPresheaf (F) Q R) := by
  let W := convolutionForget (C := C)
  let : ∀ P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}), DayConvolution (W.obj P)
      (W.obj Q) := convolutionDayComparison
  let : DayConvolution (W.obj P) (W.obj Q ⊛ W.obj R) :=
    convolutionDayComparison P (convolutionPresheaf (F) Q R)
  let : DayConvolution (W.obj P ⊛ W.obj Q) (W.obj R) :=
    convolutionDayComparison (convolutionPresheaf (F) P Q) R
  exact convolutionForgetFullyFaithful.preimageIso
    (DayConvolution.associator (W.obj P) (W.obj Q) (W.obj R))

/-- The component of the Day associator on a triple with identity inner label. -/
private theorem convolutionAssociator_identity_generator (P Q R : (Cᵒᵖ ⥤+
    AddCommGrpCat.{max u v w}))
    (X Y Z : C) (x : sections P X) (y : sections Q Y) (z : sections R Z) :
    (convolutionAssociator P Q R).hom.hom.app (op ((X ⊗ Y) ⊗ Z))
      (convolutionGenerator (F) (convolutionPresheaf (F) P Q) R
        ((X ⊗ Y) ⊗ Z) (X ⊗ Y) Z
        (convolutionGenerator (F) P Q (X ⊗ Y) X Y x y (𝟙 _)) z (𝟙 _)) =
      convolutionGenerator (F) P (convolutionPresheaf (F) Q R)
        ((X ⊗ Y) ⊗ Z) X (Y ⊗ Z) x
        (convolutionGenerator (F) Q R (Y ⊗ Z) Y Z y z (𝟙 _)) (α_ X Y Z).hom := by
  let W := convolutionForget (C := C)
  let : ∀ P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}), DayConvolution (W.obj P)
      (W.obj Q) := convolutionDayComparison
  let : DayConvolution (W.obj P) (W.obj Q ⊛ W.obj R) :=
    convolutionDayComparison P (convolutionPresheaf (F) Q R)
  let : DayConvolution (W.obj P ⊛ W.obj Q) (W.obj R) :=
    convolutionDayComparison (convolutionPresheaf (F) P Q) R
  have h := ConcreteCategory.congr_hom
    (DayConvolution.associator_hom_unit_unit (W.obj P) (W.obj Q) (W.obj R)
      (op X) (op Y) (op Z)) ((x ⊗ₜ[ℤ] y) ⊗ₜ[ℤ] z)
  have hα := convolutionForgetFullyFaithful.map_preimage
    (DayConvolution.associator (W.obj P) (W.obj Q) (W.obj R)).hom
  change W.map (convolutionAssociator P Q R).hom = _ at hα
  rw [← hα] at h
  let PQ := convolutionPresheaf (F) P Q
  let QR := convolutionPresheaf (F) Q R
  let A := DayConvolution.unit (W.obj P) (W.obj Q)
  let B := DayConvolution.unit (W.obj Q) (W.obj R)
  let L := DayConvolution.unit (W.obj PQ) (W.obj R)
  let J := DayConvolution.unit (W.obj P) (W.obj QR)
  let X₀ := op ((X ⊗ Y) ⊗ Z)
  let m := (W.map (convolutionAssociator P Q R).hom).app X₀
  let g := (W.obj (convolutionPresheaf (F) P QR)).map (α_ X Y Z).hom.op
  change m (L.app (op (X ⊗ Y), op Z) ((A.app (op X, op Y) (x ⊗ₜ[ℤ] y))
      ⊗ₜ[ℤ] z)) =
    g (J.app (op X, op (Y ⊗ Z)) (x ⊗ₜ[ℤ] (B.app (op Y, op Z) (y ⊗ₜ[ℤ] z)))) at h
  rw [show A.app (op X, op Y) (x ⊗ₜ[ℤ] y) =
      convolutionGenerator (F) P Q (X ⊗ Y) X Y x y (𝟙 _) from
      convolutionDayUnit_tmul P Q X Y x y,
    show B.app (op Y, op Z) (y ⊗ₜ[ℤ] z) =
      convolutionGenerator (F) Q R (Y ⊗ Z) Y Z y z (𝟙 _) from
      convolutionDayUnit_tmul Q R Y Z y z] at h
  let s := convolutionGenerator (F) P Q (X ⊗ Y) X Y x y (𝟙 _)
  let t := convolutionGenerator (F) Q R (Y ⊗ Z) Y Z y z (𝟙 _)
  have hL : L.app (op (X ⊗ Y), op Z) (s ⊗ₜ[ℤ] z) =
      convolutionGenerator (F) PQ R ((X ⊗ Y) ⊗ Z) (X ⊗ Y) Z s z (𝟙 _) :=
    convolutionDayUnit_tmul PQ R (X ⊗ Y) Z s z
  have hR : J.app (op X, op (Y ⊗ Z)) (x ⊗ₜ[ℤ] t) =
      convolutionGenerator (F) P QR (X ⊗ (Y ⊗ Z)) X (Y ⊗ Z) x t (𝟙 _) :=
    convolutionDayUnit_tmul P QR X (Y ⊗ Z) x t
  have hG := convolutionPresheaf_transfer_generator (F) P QR (α_ X Y Z).hom
    X (Y ⊗ Z) x t (𝟙 _)
  rw [Category.comp_id] at hG
  exact (congrArg m hL).symm.trans (h.trans ((congrArg g hR).trans hG))

/-- The original associator acts on the two correspondence labels by composition and
reassociation. -/
theorem convolutionAssociator_hom_generator (P Q R : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}))
    (U V X Y Z : C) (x : sections P X) (y : sections Q Y) (z : sections R Z)
    (a : V ⟶ X ⊗ Y) (b : U ⟶ V ⊗ Z) :
    (convolutionAssociator P Q R).hom.hom.app (op U)
      (convolutionGenerator (F) (convolutionPresheaf (F) P Q) R U V Z
        (convolutionGenerator (F) P Q V X Y x y a) z b) =
      convolutionGenerator (F) P (convolutionPresheaf (F) Q R) U X (Y ⊗ Z) x
        (convolutionGenerator (F) Q R (Y ⊗ Z) Y Z y z (𝟙 _))
        (b ≫ (a ▷ Z) ≫ (α_ X Y Z).hom) := by
  let P' := convolutionPresheaf (F) P Q
  let C := convolutionPresheaf (F) P' R
  let D := convolutionPresheaf (F) P (convolutionPresheaf (F) Q R)
  let t := convolutionGenerator (F) P Q (X ⊗ Y) X Y x y (𝟙 _)
  let d := b ≫ a ▷ Z
  have ht : transfer P' a t = convolutionGenerator (F) P Q V X Y x y a := by
    exact (Convolution.transfer_generator.{u, v, w} F P.obj Q.obj a X Y x y (𝟙 _)).trans
      (congrArg (convolutionGenerator F P Q V X Y x y) (Category.comp_id a))
  have hz : transfer R (𝟙 Z) z = z := by simp
  have hlabel : convolutionCorrespondenceMap (F) a (𝟙 Z) = a ▷ Z := by
    change (a ▷ Z) ≫ (X ⊗ Y) ◁ 𝟙 Z = a ▷ Z
    rw [whiskerLeft_id, Category.comp_id]
  have hmove := convolutionGenerator_transfer (F) P' R a (𝟙 Z) t z b
  rw [ht, hz, hlabel] at hmove
  let t' := convolutionGenerator (F) P' R ((X ⊗ Y) ⊗ Z) (X ⊗ Y) Z t z (𝟙 _)
  have hn := ConcreteCategory.congr_hom
    (transfer_naturality (convolutionAssociator P Q R).hom d) t'
  change (convolutionAssociator P Q R).hom.hom.app (op U) (transfer C d t') =
    transfer D d ((convolutionAssociator P Q R).hom.hom.app (op ((X ⊗ Y) ⊗ Z)) t') at hn
  rw [show t' = convolutionGenerator (F) P' R ((X ⊗ Y) ⊗ Z) (X ⊗ Y) Z t z (𝟙 _)
      from rfl,
    convolutionPresheaf_transfer_generator, Category.comp_id,
    convolutionAssociator_identity_generator, convolutionPresheaf_transfer_generator] at hn
  exact (congrArg ((convolutionAssociator P Q R).hom.hom.app (op U)) hmove).trans
    (by simpa only [d, Category.assoc] using hn)

/-- The actual convolution associator is natural in all three coefficients. -/
theorem convolutionAssociator_naturality {P P' Q Q' R R' : (Cᵒᵖ ⥤+
    AddCommGrpCat.{max u v w})}
    (f : P ⟶ P') (g : Q ⟶ Q') (h : R ⟶ R') :
    convolutionMap (F) (convolutionMap (F) f g) h ≫
        (convolutionAssociator P' Q' R').hom =
      (convolutionAssociator P Q R).hom ≫ convolutionMap (F) f (convolutionMap (F) g h) := by
  let W := convolutionForget (C := C)
  let : ∀ P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}), DayConvolution (W.obj P)
      (W.obj Q) := convolutionDayComparison
  let : DayConvolution (W.obj P) (W.obj Q ⊛ W.obj R) :=
    convolutionDayComparison P (convolutionPresheaf (F) Q R)
  let : DayConvolution (W.obj P ⊛ W.obj Q) (W.obj R) :=
    convolutionDayComparison (convolutionPresheaf (F) P Q) R
  let : DayConvolution (W.obj P') (W.obj Q' ⊛ W.obj R') :=
    convolutionDayComparison P' (convolutionPresheaf (F) Q' R')
  let : DayConvolution (W.obj P' ⊛ W.obj Q') (W.obj R') :=
    convolutionDayComparison (convolutionPresheaf (F) P' Q') R'
  apply convolutionForgetFullyFaithful.map_injective
  simp only [Functor.map_comp, convolutionForget_map_eq_dayMap]
  simp only [convolutionAssociator, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  exact DayConvolution.associator_naturality (W.map f) (W.map g) (W.map h)

/-- The Day pentagon for the actual convolution and its coefficient maps. -/
theorem convolutionAssociator_pentagon (P Q R S : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    convolutionMap (F) (convolutionAssociator P Q R).hom (𝟙 S) ≫
        (convolutionAssociator P (convolutionPresheaf (F) Q R) S).hom ≫
          convolutionMap (F) (𝟙 P) (convolutionAssociator Q R S).hom =
      (convolutionAssociator (convolutionPresheaf (F) P Q) R S).hom ≫
        (convolutionAssociator P Q (convolutionPresheaf (F) R S)).hom := by
  let W := convolutionForget (C := C)
  let wP := W.obj P
  let wQ := W.obj Q
  let wR := W.obj R
  let wS := W.obj S
  let : ∀ P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}), DayConvolution (W.obj P)
      (W.obj Q) := convolutionDayComparison
  let : DayConvolution (wP ⊛ wQ) wR :=
    convolutionDayComparison (convolutionPresheaf (F) P Q) R
  let : DayConvolution wP (wQ ⊛ wR) :=
    convolutionDayComparison P (convolutionPresheaf (F) Q R)
  let : DayConvolution (wQ ⊛ wR) wS :=
    convolutionDayComparison (convolutionPresheaf (F) Q R) S
  let : DayConvolution wQ (wR ⊛ wS) :=
    convolutionDayComparison Q (convolutionPresheaf (F) R S)
  let : DayConvolution ((wP ⊛ wQ) ⊛ wR) wS :=
    convolutionDayComparison (convolutionPresheaf (F)
      (convolutionPresheaf (F) P Q) R) S
  let : DayConvolution (wP ⊛ wQ) (wR ⊛ wS) :=
    convolutionDayComparison (convolutionPresheaf (F) P Q) (convolutionPresheaf (F) R S)
  let : DayConvolution (wP ⊛ wQ ⊛ wR) wS :=
    convolutionDayComparison (convolutionPresheaf (F) P
      (convolutionPresheaf (F) Q R)) S
  let : DayConvolution wP (wQ ⊛ wR ⊛ wS) :=
    convolutionDayComparison P (convolutionPresheaf (F) Q (convolutionPresheaf (F) R S))
  let : DayConvolution wP ((wQ ⊛ wR) ⊛ wS) :=
    convolutionDayComparison P (convolutionPresheaf (F) (convolutionPresheaf (F) Q R) S)
  let hW := convolutionForgetFullyFaithful (C := C)
  apply hW.map_injective
  simp only [Functor.map_comp, convolutionForget_map_eq_dayMap]
  simp only [convolutionAssociator, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage]
  exact DayConvolution.pentagon wP wQ wR wS

end CategoryTheory.Preadditive.ConvolutionRepresented
