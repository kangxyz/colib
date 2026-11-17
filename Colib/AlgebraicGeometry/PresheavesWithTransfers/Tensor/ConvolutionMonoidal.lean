/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Preadditive.IntegralConvolutionMonoidal
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionAssociator
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionSwap
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionDayBraiding
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.RepresentedUnit
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.DayConvolution.Braided
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence

/-!
# The symmetric integral convolution of transfer presheaves

The additive representable of the correspondence unit supplies the unit.
The Day associator and symmetry act on the original integral coend, and
the triangle follows by composing the original correspondence labels.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped DayConvolution TensorProduct

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)]
  [MonoidalPreadditive (Cor k)]

local notation "PST" => TransferCoefficients k
local notation "F" => curriedTensor (Cor k)
local notation "S" => BraidedCategory.curriedBraidingNatIso (Cor k)
set_option quotPrecheck false in
local notation "𝟙ₚ" => (representableLarge k).obj (𝟙_ (Cor k))
local infixl:70 " ⋆ " => convolutionPresheaf F

/-- The hom of the right unitor of correspondences is natural in the varied input. -/
def correspondenceRightUnitorIso : (F).flip.obj (𝟙_ (Cor k)) ≅ 𝟭 (Cor k) :=
  NatIso.ofComponents (fun X => ρ_ X) (fun f => rightUnitor_naturality f)

local notation "rP" => convolutionRightUnitIso F (𝟙_ (Cor k)) correspondenceRightUnitorIso

omit [MonoidalPreadditive (Cor k)] in
/-- The correspondence braiding used by convolution is involutive. -/
theorem curriedCorrespondenceBraiding_involutive (Y Z : Cor k) :
    ((S).hom.app Y).app Z ≫ ((S).hom.app Z).app Y = 𝟙 _ :=
  SymmetricCategory.symmetry Y Z

/-- The left unit given by the represented correspondence unit. -/
def convolutionLeftUnitor : (convolutionBifunctor F).obj 𝟙ₚ ≅ 𝟭 PST :=
  (convolutionSwap F S curriedCorrespondenceBraiding_involutive).app 𝟙ₚ ≪≫ rP

private theorem convolutionLeftUnitor_hom_generator
    (P : PST) (U Y Z : Cor k) (b : Y ⟶ 𝟙_ (Cor k)) (p : sections P Z) (a : U ⟶ Y ⊗ Z) :
    ((convolutionLeftUnitor).hom.app P).hom.app (op U)
        (convolutionGenerator F 𝟙ₚ P U Y Z (ULift.up b) p a) =
      transfer P (a ≫ (b ▷ Z) ≫ (λ_ Z).hom) p := by
  change ((rP).hom.app P).hom.app (op U)
    ((convolutionSwapHom F S 𝟙ₚ P).hom.app (op U)
      (convolutionGenerator F 𝟙ₚ P U Y Z (ULift.up b) p a)) = _
  rw [convolutionSwapHom_generator, convolutionRightUnitIso_hom_generator, Category.assoc]
  change transfer P (a ≫ (β_ Y Z).hom ≫ (Z ◁ b) ≫ (ρ_ Z).hom) p = _
  rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor]

/-- The represented unit and original Day associator satisfy the convolution triangle. -/
theorem convolution_triangle (P Q : PST) :
    (convolutionAssociator P 𝟙ₚ Q).hom ≫
        convolutionMap F (𝟙 P) ((convolutionLeftUnitor).hom.app Q) =
      convolutionMap F ((rP).hom.app P) (𝟙 Q) := by
  apply convolutionPresheaf_hom_ext
  intro U V Z x z b
  let l := (convolutionAssociator P 𝟙ₚ Q).hom ≫
    convolutionMap F (𝟙 P) ((convolutionLeftUnitor).hom.app Q)
  let r := convolutionMap F ((rP).hom.app P) (𝟙 Q)
  let a₀ := convolutionSections F P 𝟙ₚ V
  let a₁ := convolutionSections F (P ⋆ 𝟙ₚ) Q U
  let a₂ := convolutionSections F P Q U
  let f : a₀ →+ a₁ := AddMonoidHom.mk'
    (fun s => convolutionGenerator F (P ⋆ 𝟙ₚ) Q U V Z s z b)
    (fun s t => convolutionGenerator_add_left F (P ⋆ 𝟙ₚ) Q s t z b)
  let j := convolutionIntegralModuleMap a₀ a₁ f
  have hj (s : a₀) : j s = convolutionGenerator F (P ⋆ 𝟙ₚ) Q U V Z s z b :=
    convolutionIntegralModuleMap_apply _ _ _ _
  let l₀ := convolutionIntegralModuleMap a₁ a₂ (l.hom.app (op U)).hom
  let r₀ := convolutionIntegralModuleMap a₁ a₂ (r.hom.app (op U)).hom
  have h : j ≫ l₀ = j ≫ r₀ := by
    apply convolutionSections_hom_ext
    intro X Y p y a
    change ULift.{u + 1} (Y ⟶ 𝟙_ (Cor k)) at y
    obtain ⟨y⟩ := y
    simp only [ConcreteCategory.comp_apply, l₀, r₀, convolutionIntegralModuleMap_apply]
    change l.hom.app (op U) (j (convolutionGenerator F P 𝟙ₚ V X Y p (ULift.up y) a)) =
      r.hom.app (op U) (j (convolutionGenerator F P 𝟙ₚ V X Y p (ULift.up y) a))
    have hInput :=
      hj (convolutionGenerator F P 𝟙ₚ V X Y p (ULift.up y) a)
    rw [hInput]
    simp only [l, r, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, ConcreteCategory.comp_apply]
    change (convolutionMap F (𝟙 P) ((convolutionLeftUnitor).hom.app Q)).hom.app (op U)
        ((convolutionAssociator P 𝟙ₚ Q).hom.hom.app (op U)
          (convolutionGenerator F (P ⋆ 𝟙ₚ) Q U V Z
            (convolutionGenerator F P 𝟙ₚ V X Y p (ULift.up y) a) z b)) =
      (convolutionMap F ((rP).hom.app P) (𝟙 Q)).hom.app (op U)
        (convolutionGenerator F (P ⋆ 𝟙ₚ) Q U V Z
          (convolutionGenerator F P 𝟙ₚ V X Y p (ULift.up y) a) z b)
    rw [convolutionAssociator_hom_generator]
    let xy := convolutionGenerator F P 𝟙ₚ V X Y p (ULift.up y) a
    let yz := convolutionGenerator F 𝟙ₚ Q (Y ⊗ Z) Y Z (ULift.up y) z (𝟙 _)
    let w := b ≫ (a ▷ Z) ≫ (α_ X Y Z).hom
    have hl := convolutionMap_generator F (𝟙 P) (convolutionLeftUnitor.hom.app Q)
      U X (Y ⊗ Z) p yz w
    have hr := convolutionMap_generator F ((rP).hom.app P) (𝟙 Q) U V Z xy z b
    change (convolutionMap F (𝟙 P) (convolutionLeftUnitor.hom.app Q)).hom.app (op U)
        (convolutionGenerator F P (𝟙ₚ ⋆ Q) U X (Y ⊗ Z) p yz w) =
      (convolutionMap F ((rP).hom.app P) (𝟙 Q)).hom.app (op U)
        (convolutionGenerator F (P ⋆ 𝟙ₚ) Q U V Z xy z b)
    refine Eq.trans hl (Eq.trans ?_ hr.symm)
    dsimp only [xy, yz]
    rw [convolutionLeftUnitor_hom_generator, convolutionRightUnitIso_hom_generator]
    rw [Category.id_comp]
    change convolutionGenerator F P Q U X (Y ⊗ Z) p
        (transfer Q ((y ▷ Z) ≫ (λ_ Z).hom) z) (b ≫ (a ▷ Z) ≫ (α_ X Y Z).hom) =
      convolutionGenerator F P Q U V Z (transfer P (a ≫ (X ◁ y) ≫ (ρ_ X).hom) p) z b
    have h₁ := convolutionGenerator_transfer F P Q (𝟙 X) ((y ▷ Z) ≫ (λ_ Z).hom) p z
      (b ≫ (a ▷ Z) ≫ (α_ X Y Z).hom)
    have h₂ := convolutionGenerator_transfer F P Q (a ≫ (X ◁ y) ≫ (ρ_ X).hom)
      (𝟙 Z) p z b
    simp only [transfer_id, AddCommGrpCat.id_apply] at h₁ h₂
    rw [h₁, h₂]
    apply congrArg (convolutionGenerator F P Q U X Z p z)
    simp only [convolutionCorrespondenceMap, curriedTensor_map_app, curriedTensor_obj_map,
      id_whiskerRight, whiskerLeft_id, Category.assoc,
      whiskerLeft_comp, comp_whiskerRight]
    have h := associator_naturality_middle_assoc X y Z (X ◁ (λ_ Z).hom)
    have ht := MonoidalCategory.triangle X Z
    have he : (α_ X Y Z).hom ≫ X ◁ (y ▷ Z) ≫ X ◁ (λ_ Z).hom =
        (X ◁ y) ▷ Z ≫ (ρ_ X).hom ▷ Z := by
      exact h.symm.trans (congrArg (((X ◁ y) ▷ Z) ≫ ·) ht)
    let l := X ◁ (y ▷ Z) ≫ X ◁ (λ_ Z).hom
    let r := (ρ_ X).hom ▷ Z
    have hleft : (α_ X Y Z).hom ≫ 𝟙 _ ≫ l = (α_ X Y Z).hom ≫ l :=
      congrArg ((α_ X Y Z).hom ≫ ·) (Category.id_comp l)
    have hright : ((X ◁ y) ▷ Z) ≫ r ≫ 𝟙 _ = ((X ◁ y) ▷ Z) ≫ r :=
      congrArg (((X ◁ y) ▷ Z) ≫ ·) (Category.comp_id r)
    exact congrArg (b ≫ (a ▷ Z) ≫ ·) (hleft.trans (he.trans hright.symm))
  have hx := ConcreteCategory.congr_hom h x
  simp only [ConcreteCategory.comp_apply, l₀, r₀, convolutionIntegralModuleMap_apply] at hx
  change l.hom.app (op U) (j x) = r.hom.app (op U) (j x) at hx
  rw [hj] at hx
  exact hx

/-- The actual convolution, its represented unit and its constraint maps. -/
@[instance_reducible]
def convolutionMonoidalStruct : MonoidalCategoryStruct PST :=
  CategoryTheory.Preadditive.ConvolutionRepresented.convolutionMonoidalStruct.{u + 1, u, 0}


/-- The integral coend with its represented unit and Day associator. -/
@[colib_tag "COL-1302", instance_reducible]
def convolutionMonoidalCategory : MonoidalCategory PST :=
  CategoryTheory.Preadditive.ConvolutionRepresented.convolutionMonoidalCategory.{u + 1, u, 0}


/-- For the convolution monoidal structure the curried tensor is the original coend bifunctor. -/
def convolutionCurriedTensorIso :
    letI := convolutionMonoidalCategory (k := k)
    curriedTensor PST ≅ convolutionBifunctor F := by
  letI := convolutionMonoidalCategory (k := k)
  refine NatIso.ofComponents (fun P => NatIso.ofComponents (fun Q => Iso.refl (P ⋆ Q))
    (fun f => by
      change convolutionMap F (𝟙 P) f ≫ 𝟙 _ = 𝟙 _ ≫ convolutionMap F (𝟙 P) f
      rw [Category.comp_id, Category.id_comp])) (fun f => ?_)
  apply NatTrans.ext
  funext Q
  change convolutionMap F f (𝟙 Q) ≫ 𝟙 _ = 𝟙 _ ≫ convolutionMap F f (𝟙 Q)
  rw [Category.comp_id, Category.id_comp]

/-- The original convolution is additive in both variables. -/
theorem convolutionMonoidalPreadditive :
    letI := convolutionMonoidalCategory (k := k)
    MonoidalPreadditive PST :=
  CategoryTheory.Preadditive.ConvolutionRepresented.convolutionMonoidalPreadditive.{u + 1, u, 0}


/-- The actual coend associator and swap satisfy the forward hexagon. -/
theorem convolution_hexagon_forward (P Q U₀ : PST) :
    (convolutionAssociator P Q U₀).hom ≫ (convolutionSwapHom F S P (Q ⋆ U₀)) ≫
        (convolutionAssociator Q U₀ P).hom =
      convolutionMap F (convolutionSwapHom F S P Q) (𝟙 U₀) ≫
        (convolutionAssociator Q P U₀).hom ≫
          convolutionMap F (𝟙 Q) (convolutionSwapHom F S P U₀) := by
  let W := convolutionForget (k := k)
  let p := W.obj P
  let q := W.obj Q
  let r := W.obj U₀
  let : ∀ X Y : PST, DayConvolution (W.obj X) (W.obj Y) := convolutionDayComparison
  let : DayConvolution p (q ⊛ r) := convolutionDayComparison P (Q ⋆ U₀)
  let : DayConvolution (p ⊛ q) r := convolutionDayComparison (P ⋆ Q) U₀
  let : DayConvolution q (r ⊛ p) := convolutionDayComparison Q (U₀ ⋆ P)
  let : DayConvolution (q ⊛ r) p := convolutionDayComparison (Q ⋆ U₀) P
  let : DayConvolution (q ⊛ p) r := convolutionDayComparison (Q ⋆ P) U₀
  let : DayConvolution q (p ⊛ r) := convolutionDayComparison Q (P ⋆ U₀)
  apply convolutionForgetFullyFaithful.map_injective
  simp only [Functor.map_comp, convolutionForget_map_eq_dayMap]
  simp only [convolutionAssociator, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, convolutionForget_map_swap]
  exact DayConvolution.hexagon_forward p q r

omit [MonoidalPreadditive (Cor k)] in
/-- Reversing the two coefficient inputs gives the inverse swap. -/
theorem convolutionSwap_symm (P Q : PST) :
    ((convolutionSwap F S curriedCorrespondenceBraiding_involutive).app P |>.app Q).symm =
      ((convolutionSwap F S curriedCorrespondenceBraiding_involutive).app Q).app P :=
  Iso.ext rfl

/-- The symmetry of the coend swaps the coefficients and composes its correspondence label
with the switch of factors. -/
@[colib_tag "COL-1302", instance_reducible]
def convolutionSymmetricCategory :
    letI := convolutionMonoidalCategory (k := k)
    SymmetricCategory PST :=
  CategoryTheory.Preadditive.ConvolutionRepresented.convolutionSymmetricCategory.{u + 1, u, 0}

end AlgebraicGeometry.PresheafWithTransfers
