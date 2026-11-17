/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionDayLinearity
public import Colib.CategoryTheory.Preadditive.IntegralConvolutionDay
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

public import Colib.AlgebraicGeometry.Correspondences.Coproducts.Binary

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
  CategoryTheory.Preadditive.Convolution.liftAddHom f

/-- Convert an additive map to a linear map for the original integral module structures. -/
def convolutionIntegralModuleMap (A B : ModuleCat.{u} ℤ) (f : A →+ B) : A ⟶ B :=
  CategoryTheory.Preadditive.Convolution.integralModuleMap.{u} A B f

/-- The conversion preserves the actual pointwise map. -/
theorem convolutionIntegralModuleMap_apply (A B : ModuleCat.{u} ℤ) (f : A →+ B) (a : A) :
    convolutionIntegralModuleMap A B f a = f a :=
  CategoryTheory.Preadditive.Convolution.integralModuleMap_apply.{u} A B f a

/-- The external product of the original coefficient modules. -/
def convolutionExternalProduct (P Q : PST(k)) :
    (Cor k)ᵒᵖ × (Cor k)ᵒᵖ ⥤ MZ(k) :=
  CategoryTheory.Preadditive.Convolution.externalProduct.{u + 1, u, 0} P.obj Q.obj

/-- The Day extension unit on a pair of input indices. -/
def convolutionKanExtensionUnitApp (P Q : PST(k)) (U V : Cor k) :
    ModuleCat.of ℤ (sections P U ⊗[ℤ] sections Q V) ⟶
      integerModuleFunctor.obj ((convolutionPresheaf F P Q).obj.obj
        (op ((F.obj U).obj V))) :=
  CategoryTheory.Preadditive.Convolution.kanExtensionUnitApp.{u + 1, u, 0} F P.obj Q.obj U V

/-- The Day unit inserts the identity label into the coend. -/
theorem convolutionKanExtensionUnitApp_tmul (P Q : PST(k)) (U V : Cor k)
    (s : sections P U) (t : sections Q V) :
    convolutionKanExtensionUnitApp F P Q U V (s ⊗ₜ[ℤ] t) =
      convolutionGenerator F P Q ((F.obj U).obj V) U V s t (𝟙 _) :=
  CategoryTheory.Preadditive.Convolution.kanExtensionUnitApp_tmul.{u + 1, u, 0}
    F P.obj Q.obj U V s t

/-- The extension unit inserts the identity correspondence in the convolution generator. -/
def convolutionKanExtensionUnit (P Q : PST(k)) :
    convolutionExternalProduct P Q ⟶
      (L(F)) ⋙ (convolutionPresheaf F P Q).obj ⋙ integerModuleFunctor :=
  CategoryTheory.Preadditive.Convolution.kanExtensionUnit.{u + 1, u, 0} F P.obj Q.obj

/-- View any pointwise extension cocone on its literal coefficient and correspondence labels. -/
def convolutionCoconePairing (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q))
    (Y Z : Cor k) (a : X ⟶ (F.obj Y).obj Z) : sections P Y →+ sections Q Z →+ d.pt :=
  CategoryTheory.Preadditive.Convolution.coconePairing.{u + 1, u, 0} F P.obj Q.obj X d Y Z a

/-- The two original transfer relations are the naturality equations of the pointwise cocone. -/
theorem convolutionCoconePairing_transfer (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q))
    {Y Y' Z Z' : Cor k} (f : Y ⟶ Y') (g : Z ⟶ Z') (s : sections P Y') (t : sections Q Z')
    (a : X ⟶ (F.obj Y).obj Z) :
    convolutionCoconePairing F P Q X d Y Z a (transfer P f s) (transfer Q g t) =
      convolutionCoconePairing F P Q X d Y' Z'
        (a ≫ convolutionCorrespondenceMap F f g) s t :=
  CategoryTheory.Preadditive.Convolution.coconePairing_transfer.{u + 1, u, 0}
    F P.obj Q.obj X d f g s t a

/-- The original coend and its realization as integral coefficients have the same sections. -/
def convolutionSectionModuleIso (P Q : PST(k)) (X : Cor k) :
    convolutionSections F P Q X ≅
      integerModuleFunctor.obj ((convolutionPresheaf F P Q).obj.obj (op X)) :=
  CategoryTheory.Preadditive.Convolution.sectionModuleIso.{u + 1, u, 0} F P.obj Q.obj X

@[simp]
theorem convolutionSectionModuleIso_hom_apply (P Q : PST(k)) (X : Cor k)
    (a : convolutionSections F P Q X) : (convolutionSectionModuleIso F P Q X).hom a = a :=
  CategoryTheory.Preadditive.Convolution.sectionModuleIso_hom_apply.{u + 1, u, 0} F P.obj Q.obj X a

@[simp]
theorem convolutionSectionModuleIso_inv_apply (P Q : PST(k)) (X : Cor k)
    (a : integerModuleFunctor.obj ((convolutionPresheaf F P Q).obj.obj (op X))) :
    (convolutionSectionModuleIso F P Q X).inv a = a :=
  CategoryTheory.Preadditive.Convolution.sectionModuleIso_inv_apply.{u + 1, u, 0} F P.obj Q.obj X a

variable [F.Additive]

/-- The cocone pairing extended to the three original coefficient modules. -/
def convolutionCoconeDescPairing (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q))
    (Y Z : Cor k) :
    ((convolutionDiagram F P Q X).obj (op (Y, Z))).obj (Y, Z) ⟶ d.pt :=
  CategoryTheory.Preadditive.Convolution.coconeDescPairing.{u + 1, u, 0} F P.obj Q.obj X d Y Z

/-- On the literal triple generator, the descended pairing is the original cocone map. -/
theorem convolutionCoconeDescPairing_tmul (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q))
    (Y Z : Cor k) (s : sections P Y) (t : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    convolutionCoconeDescPairing F P Q X d Y Z ((s ⊗ₜ[ℤ] t) ⊗ₜ[ℤ] ULift.up a) =
      convolutionCoconePairing F P Q X d Y Z a s t :=
  CategoryTheory.Preadditive.Convolution.coconeDescPairing_tmul.{u + 1, u, 0}
    F P.obj Q.obj X d Y Z s t a

/-- The two transfers give dinaturality of the linear cocone pairing. -/
theorem convolutionCoconeDescPairing_dinatural (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q))
    {Y Y' Z Z' : Cor k} (f : Y ⟶ Y') (g : Z ⟶ Z') :
    let D := convolutionDiagram F P Q X
    let h : (Y, Z) ⟶ (Y', Z') := (f, g)
    (D.map h.op).app (Y, Z) ≫ convolutionCoconeDescPairing F P Q X d Y Z =
      (D.obj (op (Y', Z'))).map h ≫ convolutionCoconeDescPairing F P Q X d Y' Z' :=
  CategoryTheory.Preadditive.Convolution.coconeDescPairing_dinatural.{u + 1, u, 0}
    F P.obj Q.obj X d f g

/-- The coend maps into any pointwise extension cocone by its literal generators. -/
def convolutionCoconeDesc (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q)) :
    convolutionSections F P Q X ⟶ d.pt :=
  CategoryTheory.Preadditive.Convolution.coconeDesc.{u + 1, u, 0} F P.obj Q.obj X d

/-- The descending map evaluates the supplied cocone on the same labelled generator. -/
theorem convolutionCoconeDesc_generator (P Q : PST(k)) (X : Cor k)
    (d : Cocone (CostructuredArrow.proj (L(F)) (op X) ⋙ convolutionExternalProduct P Q))
    (Y Z : Cor k) (s : sections P Y) (t : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    convolutionCoconeDesc F P Q X d (convolutionGenerator F P Q X Y Z s t a) =
      convolutionCoconePairing F P Q X d Y Z a s t :=
  CategoryTheory.Preadditive.Convolution.coconeDesc_generator.{u + 1, u, 0}
    F P.obj Q.obj X d Y Z s t a

/-- The native integral convolution is the pointwise left Kan extension of the external product. -/
def convolutionIsPointwiseLeftKanExtension (P Q : PST(k)) :
    (Functor.LeftExtension.mk _
      (convolutionKanExtensionUnit F P Q)).IsPointwiseLeftKanExtension :=
  CategoryTheory.Preadditive.Convolution.isPointwiseLeftKanExtension.{u + 1, u, 0} F P.obj Q.obj

end AlgebraicGeometry.PresheafWithTransfers
