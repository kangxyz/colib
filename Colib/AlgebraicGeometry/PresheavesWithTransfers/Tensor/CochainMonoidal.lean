/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionMonoidal
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Total
public import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian
public import Mathlib.Algebra.Homology.BifunctorShift
public import StacksFrontier.Algebra.Homology.KoszulSymmetric
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionCoproducts
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # The signed convolution tensor of cochain complexes -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)]
  [MonoidalPreadditive (Cor k)]

local notation "PST" => TransferCoefficients k
local notation "F" => curriedTensor (Cor k)
local notation "B" => convolutionBifunctor F
local notation "c" => ComplexShape.up ℤ
local notation "Ch" => CochainComplex PST ℤ

attribute [local instance] convolutionMonoidalCategory convolutionMonoidalPreadditive
  convolutionSymmetricCategory

/-- The abelian structure of additive presheaves used for the signed cochain tensor. -/
local instance transferCoefficientAbelian : Abelian PST := AdditiveFunctor.abelian

private theorem tensorLeft_preservesSmallCoproducts (P : PST) (I : Type) :
    PreservesColimitsOfShape (Discrete I) (tensorLeft P) := by
  let e := (convolutionCurriedTensorIso (k := k)).app P
  let : PreservesColimitsOfShape (Discrete (ULift.{u + 1} I)) ((B).obj P) :=
    convolution_preservesCoproducts_right F P _
  let : PreservesColimitsOfShape (Discrete I) ((B).obj P) :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) ((B).obj P)
  exact preservesColimitsOfShape_of_natIso e.symm

private theorem tensorRight_preservesSmallCoproducts (P : PST) (I : Type) :
    PreservesColimitsOfShape (Discrete I) (tensorRight P) := by
  let := tensorLeft_preservesSmallCoproducts P I
  exact preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight P)

private instance transferHasSmallCoproducts (I : Type) : HasColimitsOfShape (Discrete I) PST := by
  let : HasColimitsOfShape (Discrete I) AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasColimitsOfShape
  let : HasColimitsOfShape (Discrete I) ((Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    functorCategoryHasColimitsOfShape
  exact hasColimitsOfShape_of_closedUnderColimits (Discrete I)
    (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1})

/-- Each convolution degree is the coproduct over the corresponding integer antidiagonal. -/
theorem cochainTensorHasCoproducts (X Y : GradedObject ℤ PST) :
    GradedObject.HasTensor X Y :=
  fun _ => (transferHasSmallCoproducts _).has_colimit _

/-- Tensoring on the right preserves the coproduct in the first pair of degrees. -/
theorem cochainTensorPreservesCoproducts₁₂ (X Y Z : GradedObject ℤ PST) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z :=
  fun _ j => (tensorRight_preservesSmallCoproducts (Z j) _).preservesColimit

/-- Tensoring on the left preserves the coproduct in the last pair of degrees. -/
theorem cochainTensorPreservesCoproducts₂₃ (X Y Z : GradedObject ℤ PST) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z :=
  fun i _ => (tensorLeft_preservesSmallCoproducts (X i) _).preservesColimit

/-- Left convolution preserves the coproduct of each degree in the three remaining factors. -/
theorem cochainTensorPreservesCoproducts₄ (X Y Z V : GradedObject ℤ PST) :
    GradedObject.HasTensor₄ObjExt X Y Z V :=
  fun i _ => (tensorLeft_preservesSmallCoproducts (X i) _).preservesColimit

/-- Left convolution preserves the initial coefficient. -/
theorem convolutionTensorLeft_preservesInitial (P : PST) :
    PreservesColimit (Functor.empty.{0} PST) (tensorLeft P) :=
  Functor.preservesInitialObject_of_preservesZeroMorphisms (tensorLeft P)

/-- Right convolution preserves the initial coefficient. -/
theorem convolutionTensorRight_preservesInitial (P : PST) :
    PreservesColimit (Functor.empty.{0} PST) (tensorRight P) :=
  Functor.preservesInitialObject_of_preservesZeroMorphisms (tensorRight P)

/-- The curried convolution tensor preserves addition of maps in its first argument. -/
theorem convolutionCurriedTensor_additive : (curriedTensor PST).Additive where
  map_add {_ _ f g} := (B).map_add (f := f) (g := g)

/-- Convolution with a fixed left coefficient preserves addition of maps. -/
theorem convolutionTensorLeft_additive (P : PST) : (tensorLeft P).Additive where
  map_add {_ _ f g} := ((B).obj P).map_add (f := f) (g := g)

attribute [local instance] cochainTensorHasCoproducts convolutionCurriedTensor_additive
  convolutionTensorLeft_additive convolutionTensorLeft_preservesInitial
  convolutionTensorRight_preservesInitial cochainTensorPreservesCoproducts₁₂
  cochainTensorPreservesCoproducts₂₃ cochainTensorPreservesCoproducts₄

/-- The monoidal structure on cochains whose tensor is the signed total of convolution. -/
@[instance_reducible]
def convolutionCochainMonoidalCategory : MonoidalCategory Ch :=
  @HomologicalComplex.monoidalCategory PST _ (convolutionMonoidalCategory (k := k)) _ _
    convolutionCurriedTensor_additive convolutionTensorLeft_additive ℤ _ c _
    cochainTensorHasCoproducts convolutionTensorLeft_preservesInitial
    convolutionTensorRight_preservesInitial
    cochainTensorPreservesCoproducts₄ cochainTensorPreservesCoproducts₁₂
    cochainTensorPreservesCoproducts₂₃ _

/-- The cochain braiding on the homogeneous summand of bidegree `(p,q)` has sign
`(-1)^(p*q)`. -/
@[instance_reducible]
def convolutionCochainSymmetricCategory :
    letI := convolutionCochainMonoidalCategory (k := k)
    SymmetricCategory Ch :=
  @CochainComplex.symmetricCategory PST _ (convolutionMonoidalCategory (k := k)) _
    convolutionMonoidalPreadditive convolutionSymmetricCategory _
    cochainTensorHasCoproducts convolutionTensorLeft_preservesInitial
    convolutionTensorRight_preservesInitial cochainTensorPreservesCoproducts₄
    cochainTensorPreservesCoproducts₁₂ cochainTensorPreservesCoproducts₂₃

attribute [local instance] convolutionCochainMonoidalCategory convolutionCochainSymmetricCategory

/-- The native coefficient-convolution bifunctor gives the same signed tensor on cochains. -/
def convolutionCochainTensorIso :
    curriedTensor Ch ≅ (B).map₂CochainComplex := by
  refine NatIso.ofComponents (fun K => NatIso.ofComponents (fun L => Iso.refl (K ⊗ L))
    (fun g => by
      change tensorHom (𝟙 K) g ≫ 𝟙 _ = 𝟙 _ ≫ tensorHom (𝟙 K) g
      rw [Category.comp_id, Category.id_comp])) (fun f => ?_)
  apply NatTrans.ext
  funext L
  change tensorHom f (𝟙 L) ≫ 𝟙 _ = 𝟙 _ ≫ tensorHom f (𝟙 L)
  rw [Category.comp_id, Category.id_comp]

set_option maxHeartbeats 900000 in
-- This is the native bifunctor shift specialized to the cochain monoidal structure.
/-- The actual cochain tensor commutes with the shifts by the native total comparisons. -/
@[instance_reducible]
def convolutionCochainCommShift₂Int : (curriedTensor Ch).CommShift₂Int := by
  change ((curriedTensor PST).map₂CochainComplex).CommShift₂Int
  infer_instance

/-- The coherent tensor uses the same two-variable shift comparison on its literal
representatives. -/
theorem convolutionCochain_commShiftIso_hom (K L : Ch) (n : ℤ) :
    letI := convolutionCochainCommShift₂Int (k := k)
    ((tensorLeft K).commShiftIso n).hom.app L =
      (CochainComplex.mapBifunctorShift₂Iso K L (curriedTensor PST) n).hom := by
  let := convolutionCochainCommShift₂Int (k := k)
  exact Functor.commShiftIso_map₂CochainComplex_hom_app (curriedTensor PST) K L n

/-- The native cochain comparison in the first variable uses its original signed total. -/
theorem convolutionCochain_commShiftIso_flip_hom (K L : Ch) (n : ℤ) :
    letI := convolutionCochainCommShift₂Int (k := k)
    ((tensorRight L).commShiftIso n).hom.app K =
      (CochainComplex.mapBifunctorShift₁Iso K L (curriedTensor PST) n).hom := by
  let := convolutionCochainCommShift₂Int (k := k)
  exact Functor.commShiftIso_map₂CochainComplex_flip_hom_app (curriedTensor PST) K L n


end AlgebraicGeometry.PresheafWithTransfers
