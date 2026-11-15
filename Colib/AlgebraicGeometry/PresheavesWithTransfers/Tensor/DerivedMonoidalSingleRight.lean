/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalShift
public import Mathlib.CategoryTheory.Functor.Category
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorSingleShift
import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-! # The original shift of tensor with a projective coefficient -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

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

attribute [local instance] derivedConvolutionMonoidalCategory convolutionHomotopyCommShift₂Int
  convolutionProjectiveCommShift₂Int

local instance : (P).IsStableUnderShift ℤ :=
  (inferInstance : (P).IsTriangulated).toIsStableUnderShift

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
private theorem derivedConvolutionSingleRightIso_hom_app (A : PST) [Projective A] (K : D) :
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

set_option maxHeartbeats 1250000 in
-- Expose the original quotient comparisons separately before composing them.
/-- The first-variable shift on tensoring with a degree-zero projective coefficient
is the original termwise shift. -/
theorem derivedConvolutionSingleRightIso_commShift (A : PST) [Projective A] :
    letI := derivedConvolutionCommShift₂Int (k := k)
    NatTrans.CommShift (derivedConvolutionSingleRightIso A).hom ℤ := by
  let := derivedConvolutionCommShift₂Int (k := k)
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
  let X := tensorRight ((singleDerivedMinus k 0).obj A)
  let Y := projectiveDerivedMinusFunctor k C₀
  let f : X ⟶ Y := (derivedConvolutionSingleRightIso A).hom
  let U₀ := tensorRight P₀
  let U₁ := tensorRight P₁
  let U₂ := tensorRight (J₀.obj P₁)
  let d : V₀ ⋙ V ≅ J₀ ⋙ Q := Iso.refl _
  let d' : L ⋙ V ≅ J₀ ⋙ F₀ ⋙ Q := Iso.refl _
  let : NatTrans.CommShift d.hom ℤ := boundedAboveProjectiveEquivalence_comp_ι_commShift k
  let : NatTrans.CommShift d'.hom ℤ :=
    projectiveHomotopyMapToDerivedMinus_comp_ι_commShift k C₀
  let : NatTrans.CommShift d'.inv ℤ := NatTrans.CommShift.of_iso_inv d' ℤ
  let e₀ : X ≅ I ⋙ (U₀ ⋙ V₀) := Functor.associator I U₀ V₀
  let : NatTrans.CommShift e₀.hom ℤ := NatTrans.CommShift.associator U₀ V₀ ℤ
  let e₁ : U₁ ⋙ J₀ ≅ J₀ ⋙ U₂ := Iso.refl _
  let : NatTrans.CommShift e₁.hom ℤ := Functor.CommShift.ofComp_compatibility e₁ ℤ
  let e₂ : Y ≅ I ⋙ L := Iso.refl _
  let : NatTrans.CommShift e₂.hom ℤ :=
    projectiveDerivedMinusFunctor_comp_projective_commShift k C₀
  let t := signedTotalHomotopySingleRightIso B A
  let : NatTrans.CommShift t.hom ℤ := signedTotalHomotopySingleRightIso_commShift B A
  let η : U₀ ⟶ U₁ := T.flip.map j.hom
  let : NatTrans.CommShift η ℤ := inferInstanceAs (NatTrans.CommShift (T.flip.map j.hom) ℤ)
  let a := Functor.isoWhiskerRight e₀ V ≪≫ Functor.associator I (U₀ ⋙ V₀) V
  let b := Functor.isoWhiskerRight e₂ V ≪≫ Functor.associator I L V
  let u₀ : (U₀ ⋙ V₀) ⋙ V ⟶ U₁ ⋙ (V₀ ⋙ V) :=
    Functor.whiskerRight (Functor.whiskerRight η V₀) V ≫ (Functor.associator U₁ V₀ V).hom
  let u₁ : U₁ ⋙ (V₀ ⋙ V) ⟶ (U₁ ⋙ J₀) ⋙ Q :=
    Functor.whiskerLeft U₁ d.hom ≫ (Functor.associator U₁ J₀ Q).inv
  let u₂ : (U₁ ⋙ J₀) ⋙ Q ⟶ J₀ ⋙ U₂ ⋙ Q :=
    Functor.whiskerRight e₁.hom Q ≫ (Functor.associator J₀ U₂ Q).hom
  let u₃ : J₀ ⋙ U₂ ⋙ Q ⟶ L ⋙ V :=
    Functor.whiskerLeft J₀ (Functor.whiskerRight t.hom Q) ≫ d'.inv
  let u : X ⋙ V ⟶ Y ⋙ V :=
    a.hom ≫ Functor.whiskerLeft I (u₀ ≫ u₁ ≫ u₂ ≫ u₃) ≫ b.inv
  have hu : Functor.whiskerRight f V = u := by
    apply NatTrans.ext
    funext K
    let hV := Functor.FullyFaithful.ofFullyFaithful V
    let e := Functor.isoWhiskerLeft J₀ (Functor.isoWhiskerRight t Q)
    have h := NatTrans.congr_app ((hV.whiskeringRight J).map_preimage
      (X := (projectiveHomotopyBifunctorToDerivedMinus B).flip.obj P₁)
      (Y := L) e.hom) (I.obj K)
    change V.map ((projectiveHomotopySingleRightIso B A).hom.app (I.obj K)) =
      Q.map (t.hom.app (J₀.obj (I.obj K))) at h
    have hf : f.app K = V₀.map (η.app (I.obj K)) ≫
        (projectiveHomotopySingleRightIso B A).hom.app (I.obj K) :=
      derivedConvolutionSingleRightIso_hom_app A K
    rw [Functor.whiskerRight_app, hf, V.map_comp, h]
    simp only [u, a, b, u₀, u₁, u₂, u₃, e₀, d, d', e₁, e₂, NatTrans.comp_app,
      Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Iso.refl_inv, Iso.refl_hom, NatTrans.id_app]
    let X₀ := ((I ⋙ U₀) ⋙ V₀).obj K
    let X₁ := (U₁ ⋙ J₀).obj (I.obj K)
    let Y₀ := Y.obj K
    let a₀ : V.obj X₀ ⟶ Q.obj X₁ := V.map (V₀.map (η.app (I.obj K)))
    let b₀ : Q.obj X₁ ⟶ V.obj Y₀ := Q.map (t.hom.app (J₀.obj (I.obj K)))
    let i₀ := V.map (𝟙 X₀)
    let i₁ := Q.map (𝟙 X₁)
    let i₂ := V.map (𝟙 Y₀)
    let eX := 𝟙 (V.obj X₀)
    let eC := 𝟙 (Q.obj X₁)
    let eY := 𝟙 (V.obj Y₀)
    change a₀ ≫ b₀ = (i₀ ≫ eX) ≫
      ((a₀ ≫ eC) ≫ (eC ≫ eC) ≫ (i₁ ≫ eC) ≫ b₀ ≫ eY) ≫ eY ≫ i₂
    have hX : i₀ ≫ eX = eX := (Category.comp_id _).trans (V.map_id X₀)
    have hA : a₀ ≫ eC = a₀ := Category.comp_id _
    have hC : eC ≫ eC = eC := Category.comp_id _
    have hQ : i₁ ≫ eC = eC := (Category.comp_id _).trans (Q.map_id X₁)
    have hB : b₀ ≫ eY = b₀ := Category.comp_id _
    have hY : eY ≫ i₂ = eY := (Category.id_comp _).trans (V.map_id Y₀)
    have hTail : (i₁ ≫ eC) ≫ b₀ ≫ eY = b₀ :=
      (congrArg₂ (· ≫ ·) hQ hB).trans (Category.id_comp _)
    have hMid : (eC ≫ eC) ≫ (i₁ ≫ eC) ≫ b₀ ≫ eY = b₀ :=
      (congrArg₂ (· ≫ ·) hC hTail).trans (Category.id_comp _)
    have hBody : (a₀ ≫ eC) ≫ (eC ≫ eC) ≫ (i₁ ≫ eC) ≫ b₀ ≫ eY = a₀ ≫ b₀ :=
      congrArg₂ (· ≫ ·) hA hMid
    exact ((congrArg₂ (· ≫ ·) hX (congrArg₂ (· ≫ ·) hBody hY)).trans
      ((Category.id_comp _).trans (Category.comp_id _))).symm
  change NatTrans.CommShift f ℤ
  apply NatTrans.commShift_of_whiskerRight f V
  rw [hu]
  let x := Functor.whiskerRight e₀.hom V
  let x' := Functor.whiskerRight e₂.hom V
  let y := (Functor.associator I (U₀ ⋙ V₀) V).hom
  let y' := (Functor.associator I L V).hom
  let : NatTrans.CommShift x ℤ := NatTrans.CommShift.whiskerRight e₀.hom V ℤ
  let : NatTrans.CommShift x' ℤ := NatTrans.CommShift.whiskerRight e₂.hom V ℤ
  let : NatTrans.CommShift y ℤ := NatTrans.CommShift.associator (U₀ ⋙ V₀) V ℤ
  let : NatTrans.CommShift y' ℤ := NatTrans.CommShift.associator L V ℤ
  let : NatTrans.CommShift a.hom ℤ := NatTrans.CommShift.comp x y ℤ
  let : NatTrans.CommShift b.hom ℤ := NatTrans.CommShift.comp x' y' ℤ
  let : NatTrans.CommShift b.inv ℤ := NatTrans.CommShift.of_iso_inv b ℤ
  let : NatTrans.CommShift u₀ ℤ := by dsimp only [u₀]; infer_instance
  let : NatTrans.CommShift u₁ ℤ := by dsimp only [u₁]; infer_instance
  let : NatTrans.CommShift u₂ ℤ := by dsimp only [u₂]; infer_instance
  let : NatTrans.CommShift u₃ ℤ := by dsimp only [u₃]; infer_instance
  let : NatTrans.CommShift (u₂ ≫ u₃) ℤ := NatTrans.CommShift.comp u₂ u₃ ℤ
  let : NatTrans.CommShift (u₁ ≫ u₂ ≫ u₃) ℤ :=
    NatTrans.CommShift.comp u₁ (u₂ ≫ u₃) ℤ
  let : NatTrans.CommShift (u₀ ≫ u₁ ≫ u₂ ≫ u₃) ℤ :=
    NatTrans.CommShift.comp u₀ (u₁ ≫ u₂ ≫ u₃) ℤ
  let m := Functor.whiskerLeft I (u₀ ≫ u₁ ≫ u₂ ≫ u₃)
  let : NatTrans.CommShift m ℤ := by dsimp only [m]; infer_instance
  let : NatTrans.CommShift (m ≫ b.inv) ℤ := NatTrans.CommShift.comp m b.inv ℤ
  exact NatTrans.CommShift.comp a.hom (m ≫ b.inv) ℤ

end AlgebraicGeometry.PresheafWithTransfers
