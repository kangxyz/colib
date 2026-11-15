/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalTransport
public import Colib.CategoryTheory.Functor.FactorizationComparison
public import Mathlib.CategoryTheory.Functor.Category
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorSingleNaturality

/-! # The native tensor comparison with a projective coefficient -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

private theorem singleRightComparison_comp_identities
    {C : Type*} [Category* C] {X Y Z : C} (a : X ⟶ Y) (b : Y ⟶ Z)
    {iX : X ⟶ X} {iY : Y ⟶ Y} {iZ : Z ⟶ Z}
    (hX : iX = 𝟙 X) (hY : iY = 𝟙 Y) (hZ : iZ = 𝟙 Z) :
    a ≫ b = (iX ≫ 𝟙 X) ≫
      (a ≫ 𝟙 Y ≫ iY ≫ b ≫ 𝟙 Z) ≫ 𝟙 Z ≫ iZ := by
  simp only [hX, hY, hZ, Category.id_comp, Category.comp_id]

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)]
  [MonoidalPreadditive (Cor k)] [HasDerivedCategory.{w} (TransferCoefficients k)]

local notation "PST" => TransferCoefficients k
local notation "F" => curriedTensor (Cor k)
local notation "B" => convolutionBifunctor F
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => boundedAboveProjectiveEquivalence k
local notation "P" => boundedAboveProjectiveCondition k
local notation "J" => BoundedAboveProjectiveHomotopy k

attribute [local instance] convolutionHomotopyMonoidalCategory convolutionHomotopySymmetricCategory
  boundedAboveProjectiveCondition_convolution_isMonoidal

attribute [local instance] derivedConvolutionMonoidalCategory

omit [SymmetricCategory (Cor k)] [MonoidalPreadditive (Cor k)] [HasDerivedCategory PST] in
/-- The integral convolution is additive with a fixed right coefficient. -/
theorem convolutionBifunctor_flip_additive (A : PST) : ((B).flip.obj A).Additive where
  map_add := by
    intro X Y f g
    exact NatTrans.congr_app ((B).map_add (f := f) (g := g)) A

attribute [local instance] convolutionBifunctor_flip_additive

/-- The coherent tensor with a degree-zero projective coefficient is computed termwise. -/
def derivedConvolutionSingleRightIso (A : PST) [Projective A] :
    tensorRight ((singleDerivedMinus k 0).obj A) ≅
      projectiveDerivedMinusFunctor k ((B).flip.obj A) :=
  ((CategoryTheory.flipFunctor D D D).mapIso derivedConvolutionTensorIso).app
    ((singleDerivedMinus k 0).obj A) ≪≫ projectiveDerivedMinusBifunctorSingleRightIso B A

set_option maxHeartbeats 425000 in
-- The dependent sources are the original projective single and derived quotient.
/-- The comparison on the chosen projective representative. -/
theorem derivedConvolutionSingleRightIso_hom_app (A : PST) [Projective A] (K : D) :
    let I := (E).inverse
    let V := (E).functor
    let j := singleProjectiveComparison A 0
    let η := (curriedTensor J).flip.map j.hom
    (derivedConvolutionSingleRightIso A).hom.app K =
      V.map (η.app (I.obj K)) ≫ (projectiveHomotopySingleRightIso B A).hom.app (I.obj K) := by
  intro I V j η
  change (𝟙 _ : (tensorRight ((singleDerivedMinus k 0).obj A)).obj K ⟶ _) ≫
    (V.map (η.app (I.obj K)) ≫ (projectiveHomotopySingleRightIso B A).hom.app (I.obj K)) = _
  exact Category.id_comp _

attribute [local irreducible] convolutionBifunctor

set_option maxHeartbeats 1250000 in
-- Identify the actual quotient and coefficient maps before comparing their shifts.
/-- The native tensor comparison after inclusion into the unbounded derived category. -/
theorem derivedConvolutionSingleRightIso_hom_throughQuotient
    (A : PST) [Projective A] :
    let I := (E).inverse
    let P₀ := I.obj ((singleDerivedMinus k 0).obj A)
    let P₁ := singleProjective A 0
    let j := singleProjectiveComparison A 0
    let V := DerivedCategory.Minus.ι (C := PST)
    let Q := DerivedCategory.Qh (C := PST)
    let J₀ := (P).ι
    let T := curriedTensor J
    let V₀ := (E).functor
    let C₀ := (B).flip.obj A
    let F₀ := C₀.mapHomotopyCategory (ComplexShape.up ℤ)
    let L := projectiveHomotopyMapToDerivedMinus k C₀
    let U₀ := tensorRight P₀
    let U₁ := tensorRight P₁
    let U₂ := tensorRight (J₀.obj P₁)
    let X := (I ⋙ U₀) ⋙ V₀
    let Y := projectiveDerivedMinusFunctor k C₀
    let f : X ⟶ Y := (derivedConvolutionSingleRightIso A).hom
    let d : V₀ ⋙ V ≅ J₀ ⋙ Q := Iso.refl _
    let d' : L ⋙ V ≅ J₀ ⋙ F₀ ⋙ Q := Iso.refl _
    let e₀ := Functor.associator I U₀ V₀
    let e₁ : U₁ ⋙ J₀ ≅ J₀ ⋙ U₂ := Iso.refl _
    let e₂ : Y ≅ I ⋙ L := Iso.refl _
    let t := signedTotalHomotopySingleRightIso B A
    let η : U₀ ⟶ U₁ := T.flip.map j.hom
    let a := Functor.isoWhiskerRight e₀ V ≪≫ Functor.associator I (U₀ ⋙ V₀) V
    let b := Functor.isoWhiskerRight e₂ V ≪≫ Functor.associator I L V
    let n := Functor.factorizationComparison d e₁ d' η t.hom
    let m := Functor.whiskerLeft I n
    Functor.whiskerRight f V = a.hom ≫ m ≫ b.inv := by
  intro I P₀ P₁ j V Q J₀ T V₀ C₀ F₀ L U₀ U₁ U₂ X Y f d d' e₀ e₁ e₂ t η a b n m
  apply NatTrans.ext
  funext K
  let K₀ := I.obj K
  let X₀ := X.obj K
  let X₁ := J₀.obj (U₁.obj K₀)
  let Y₀ := Y.obj K
  let g : X₀ ⟶ V₀.obj (U₁.obj K₀) := V₀.map (η.app K₀)
  let h : V₀.obj (U₁.obj K₀) ⟶ Y₀ := (projectiveHomotopySingleRightIso B A).hom.app K₀
  let a₀ : V.obj X₀ ⟶ Q.obj X₁ := V.map g
  let b₀ : Q.obj X₁ ⟶ V.obj Y₀ := Q.map (t.hom.app (J₀.obj K₀))
  have hf : f.app K = g ≫ h := derivedConvolutionSingleRightIso_hom_app A K
  have hh : V.map h = b₀ := projectiveHomotopySingleRightIso_map_hom B A K₀
  have hleft : (Functor.whiskerRight f V).app K = a₀ ≫ b₀ :=
    (V.congr_map hf).trans ((V.map_comp g h).trans (congrArg (a₀ ≫ ·) hh))
  let i₀ := V.map (𝟙 X₀)
  let i₁ := Q.map (𝟙 X₁)
  let i₂ := V.map (𝟙 Y₀)
  let eX := 𝟙 (V.obj X₀)
  let eC := 𝟙 (Q.obj X₁)
  let eY := 𝟙 (V.obj Y₀)
  have ha : a.hom.app K = i₀ ≫ eX := rfl
  have hb : b.inv.app K = eY ≫ i₂ := rfl
  have hn : n.app K₀ = a₀ ≫ eC ≫ i₁ ≫ b₀ ≫ eY :=
    Functor.factorizationComparison_app d e₁ d' η t.hom K₀
  have hright : (a.hom ≫ m ≫ b.inv).app K =
      (i₀ ≫ eX) ≫ (a₀ ≫ eC ≫ i₁ ≫ b₀ ≫ eY) ≫ eY ≫ i₂ := by
    change a.hom.app K ≫ n.app K₀ ≫ b.inv.app K = _
    rw [ha, hn, hb]
  exact hleft.trans ((singleRightComparison_comp_identities a₀ b₀
    (V.map_id X₀) (Q.map_id X₁) (V.map_id Y₀)).trans hright.symm)

end AlgebraicGeometry.PresheafWithTransfers
