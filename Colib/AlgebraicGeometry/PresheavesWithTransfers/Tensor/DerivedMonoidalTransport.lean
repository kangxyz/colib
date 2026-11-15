/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveMonoidal
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedConvolution
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport
public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Signed convolution on the bounded-above derived category

The original projective equivalence transports the coherent signed tensor.
Its tensor bifunctor is the signed total on the selected projective resolutions.
The unit is the correspondence unit represented in degree zero.
-/

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
set_option quotPrecheck false in
local notation "R" => (representableLarge k).obj (𝟙_ (Cor k))
set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => boundedAboveProjectiveEquivalence k

attribute [local instance] convolutionHomotopyMonoidalCategory convolutionHomotopySymmetricCategory
  boundedAboveProjectiveCondition_convolution_isMonoidal

/-- The symmetric monoidal structure given by the signed integral derived tensor. -/
@[instance_reducible]
def derivedConvolutionMonoidalCategory : MonoidalCategory D :=
  Monoidal.transport E

set_option maxHeartbeats 1100000 in
-- The transported symmetry uses the actual projective monoidal equivalence.
/-- The derived tensor symmetry comes from the original Koszul symmetry on cochains. -/
@[instance_reducible]
def derivedConvolutionSymmetricCategory :
    letI := derivedConvolutionMonoidalCategory (k := k)
    SymmetricCategory D :=
  Monoidal.Transported.instSymmetricCategory (E)

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionSymmetricCategory

set_option maxHeartbeats 1000000 in
-- Identify both whiskerings after applying the actual derived quotient.
/-- The transported tensor is the bifunctor defined by the original projective resolutions. -/
def derivedConvolutionTensorIso : curriedTensor D ≅ derivedConvolution F := by
  refine NatIso.ofComponents (fun K => NatIso.ofComponents
    (fun L => Iso.refl ((E).functor.obj ((E).inverse.obj K ⊗ (E).inverse.obj L))) (fun g => ?_))
    (fun f => ?_)
  · apply ObjectProperty.hom_ext
    change DerivedCategory.Qh.map (((E).inverse.obj K).obj ◁ ((E).inverse.map g).hom) ≫ 𝟙 _ =
      𝟙 _ ≫ DerivedCategory.Qh.map (((E).inverse.obj K).obj ◁ ((E).inverse.map g).hom)
    rw [Category.comp_id, Category.id_comp]
  · apply NatTrans.ext
    funext L
    apply ObjectProperty.hom_ext
    change DerivedCategory.Qh.map (((E).inverse.map f).hom ▷ ((E).inverse.obj L).obj) ≫ 𝟙 _ =
      𝟙 _ ≫ DerivedCategory.Qh.map (((E).inverse.map f).hom ▷ ((E).inverse.obj L).obj)
    rw [Category.comp_id, Category.id_comp]

/-- The unit is the representable of the correspondence unit in degree zero. -/
def derivedConvolutionUnitIso : 𝟙_ D ≅ (singleDerivedMinus k 0).obj R :=
  ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso PST).app
    ((CochainComplex.singleFunctor PST 0).obj R))

/-- The actual inverse projective equivalence is monoidal for the transported tensor. -/
@[instance_reducible]
def derivedConvolutionInverseMonoidal : ((E).inverse).Monoidal :=
  inferInstanceAs ((Monoidal.equivalenceTransported E).inverse.Monoidal)

attribute [local instance] derivedConvolutionInverseMonoidal

/-- The inverse equivalence tensorator is its unit on the original projective tensor. -/
theorem derivedConvolutionInverseMonoidal_μ (X Y : D) :
    Functor.LaxMonoidal.μ (E).inverse X Y =
      (E).unitIso.hom.app ((E).inverse.obj X ⊗ (E).inverse.obj Y) :=
  rfl

end AlgebraicGeometry.PresheafWithTransfers
