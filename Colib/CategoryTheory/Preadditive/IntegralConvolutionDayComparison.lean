/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Preadditive.IntegralConvolutionDay
public import Mathlib.CategoryTheory.Monoidal.DayConvolution
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# The integral coend as Mathlib Day convolution

For a monoidal preadditive category with binary biproducts, the integral coend
provides Mathlib's existing `DayConvolution` structure. No second tensor model
or independent coherence axioms are introduced. The first coefficient is
additive; the second coefficient may be an ordinary presheaf.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped DayConvolution

universe u v w

namespace CategoryTheory.Preadditive.Convolution

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [MonoidalCategory C] [MonoidalPreadditive C]

/-- The product on the opposite category is the opposite of the selected tensor product. -/
def oppositeTensorIso :
    (prodOpEquiv (D := C) (C)).inverse ⋙
        (Functor.uncurry.obj (curriedTensor C)).op ≅ tensor (C)ᵒᵖ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {X Y} f => by
    change (bifunctorMap (curriedTensor C) f.1.unop f.2.unop).op ≫ 𝟙 _ =
      𝟙 _ ≫ (tensor (C)ᵒᵖ).map f
    rw [Category.comp_id, Category.id_comp]
    apply Quiver.Hom.unop_inj
    change (f.1.unop ▷ Y.2.unop) ≫ (X.1.unop ◁ f.2.unop) = (f.1.unop ⊗ₘ f.2.unop)
    exact (MonoidalCategory.tensorHom_def _ _).symm)

/-- The pointwise extension unit along the product on the opposite category. -/
def dayUnit (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) :
    externalProduct P Q ⟶
      tensor (C)ᵒᵖ ⋙ ((presheaf (curriedTensor C) P Q).obj ⋙ integerModuleFunctor) :=
  kanExtensionUnit (curriedTensor C) P Q ≫
    Functor.whiskerRight oppositeTensorIso.hom
      (((presheaf (curriedTensor C) P Q).obj ⋙ integerModuleFunctor))

private theorem isPointwiseLeftKanExtension_transport
    {C D A : Type*} [Category* C] [Category* D] [Category* A]
    {L L' : C ⥤ D} {F : C ⥤ A} {G : D ⥤ A}
    (T : L ≅ L') (η : F ⟶ L ⋙ G) (X : D)
    (h : (Functor.LeftExtension.mk G η).IsPointwiseLeftKanExtensionAt X) :
    Nonempty ((Functor.LeftExtension.mk G
      (η ≫ Functor.whiskerRight T.hom G)).IsPointwiseLeftKanExtensionAt X) := by
  let H := CostructuredArrow.mapNatIso (T := X) T
  let d := (Functor.LeftExtension.mk G (η ≫ Functor.whiskerRight T.hom G)).coconeAt X
  have h' : IsColimit (d.whisker H.functor) := by
    apply h.ofIsoColimit
    refine Cocone.ext (Iso.refl _) (fun i => ?_)
    change (η.app i.left ≫ G.map i.hom) ≫ 𝟙 _ =
      (η.app i.left ≫ G.map (T.hom.app i.left)) ≫ G.map (T.inv.app i.left ≫ i.hom)
    rw [Category.comp_id, Category.assoc]
    have hmap := G.map_comp (T.hom.app i.left) (T.inv.app i.left ≫ i.hom)
    have ht : T.hom.app i.left ≫ T.inv.app i.left ≫ i.hom = i.hom :=
      Iso.hom_inv_id_app_assoc T i.left i.hom
    exact congrArg (η.app i.left ≫ ·) ((G.congr_map ht).symm.trans hmap)
  exact ⟨(IsColimit.whiskerEquivalenceEquiv H).symm h'⟩

variable [HasBinaryBiproducts C]

/-- The original integral coend has the pointwise extension property for the opposite product. -/
theorem dayUnit_isPointwiseLeftKanExtension
    (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) [P.Additive] (X : Cᵒᵖ) :
    Nonempty ((Functor.LeftExtension.mk _
      (dayUnit P Q)).IsPointwiseLeftKanExtensionAt X) :=
  isPointwiseLeftKanExtension_transport (oppositeTensorIso (C := C))
    (kanExtensionUnit (curriedTensor C) P Q) X
    (isPointwiseLeftKanExtension (curriedTensor C) P Q X)

/-- The original convolution is a pointwise Day extension of the coefficient tensor. -/
@[instance_reducible]
def dayComparison (P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max u v w}) [P.Additive] :
    DayConvolution (P ⋙ integerModuleFunctor) (Q ⋙ integerModuleFunctor) where
  convolution := ((presheaf (curriedTensor C) P Q).obj ⋙ integerModuleFunctor)
  unit := dayUnit P Q
  isPointwiseLeftKanExtensionUnit X :=
    Classical.choice (dayUnit_isPointwiseLeftKanExtension P Q X)

end CategoryTheory.Preadditive.Convolution
