/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.CochainMonoidal
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionProjective
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorShift
public import StacksFrontier.CategoryTheory.Localization.Monoidal
public import StacksFrontier.CategoryTheory.Monoidal.Reseat
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization
import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian

/-!
# Signed tensor of bounded-above projective transfer complexes

The integral convolution total descends along the original homotopy quotient.
The full subcategory of bounded-above projectives is closed under the unit and tensor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)]
  [MonoidalPreadditive (Cor k)]

local notation "PST" => TransferCoefficients k
local notation "F" => curriedTensor (Cor k)
local notation "S" => BraidedCategory.curriedBraidingNatIso (Cor k)
local notation "B" => convolutionBifunctor F
local notation "c" => ComplexShape.up ℤ
local notation "Ch" => CochainComplex PST ℤ
local notation "Ho" => HomotopyCategory PST c
set_option quotPrecheck false in
local notation "R" => (representableLarge k).obj (𝟙_ (Cor k))
local notation "Q" => HomotopyCategory.quotient PST c
local notation "W" => HomologicalComplex.homotopyEquivalences PST c
attribute [local instance] convolutionMonoidalCategory convolutionMonoidalPreadditive
  convolutionSymmetricCategory

attribute [local instance] transferCoefficientAbelian

attribute [local instance] convolutionCochainMonoidalCategory convolutionCochainSymmetricCategory
  cochainTensorHasCoproducts convolutionCurriedTensor_additive convolutionTensorLeft_additive
  convolutionTensorLeft_preservesInitial convolutionTensorRight_preservesInitial
  cochainTensorPreservesCoproducts₁₂ cochainTensorPreservesCoproducts₂₃
  cochainTensorPreservesCoproducts₄

set_option quotPrecheck false in
local notation "U" => (Q).obj (𝟙_ Ch)

/-- Homotopy equivalences are closed under the signed convolution of complexes. -/
theorem convolutionHomotopyEquivalencesMonoidal :
    letI := convolutionCochainMonoidalCategory (k := k)
    (W).IsMonoidal :=
  @CochainComplex.KFlatMonoidal.homotopyEquivalences_isMonoidal PST _
    AdditiveFunctor.abelian (convolutionMonoidalCategory (k := k))
    convolutionCurriedTensor_additive convolutionTensorLeft_additive cochainTensorHasCoproducts
    convolutionTensorLeft_preservesInitial convolutionTensorRight_preservesInitial
    cochainTensorPreservesCoproducts₄ cochainTensorPreservesCoproducts₁₂
    cochainTensorPreservesCoproducts₂₃

attribute [local instance] convolutionHomotopyEquivalencesMonoidal

/-- The signed tensor descends to the native homotopy category of transfer complexes. -/
@[instance_reducible]
def localizedHomotopyMonoidal : MonoidalCategory Ho :=
  Localization.monoidalCategory Q W (Iso.refl U)

/-- The Koszul symmetry descends to the native homotopy category. -/
@[instance_reducible]
def localizedHomotopySymmetric :
    letI := localizedHomotopyMonoidal (k := k)
    SymmetricCategory Ho :=
  Localization.symmetricCategory Q W (Iso.refl U)

section

attribute [local instance] localizedHomotopyMonoidal localizedHomotopySymmetric

/-- The homotopy tensor uses the signed convolution of cochains on representatives. -/
@[instance_reducible]
def convolutionHomotopyTensorLifting :
    Localization.Lifting₂ Q Q W W
      (curriedTensor Ch ⋙ (Functor.whiskeringRight _ _ _).obj Q) (curriedTensor Ho) := by
  constructor
  exact Localization.Monoidal.tensorBifunctorIso Q W (Iso.refl U)

/-- The coherence on the homotopy category acts on the original signed total bifunctor. -/
def localizedHomotopyTensorIso :
    curriedTensor Ho ≅ signedTotalHomotopyBifunctor B := by
  let post := (Functor.whiskeringRight Ch Ch Ho).obj Q
  let A := curriedTensor Ch ⋙ post
  let A' := (B).map₂CochainComplex ⋙ post
  let M := curriedTensor Ho
  let N := signedTotalHomotopyBifunctor B
  let : Localization.Lifting₂ Q Q W W A M := convolutionHomotopyTensorLifting
  let : Localization.Lifting₂ Q Q W W A' N := signedTotalHomotopyBifunctorLifting B
  let e : A ≅ A' := Functor.isoWhiskerRight convolutionCochainTensorIso post
  exact Localization.lift₂NatIso Q Q W W A A' M N e

end

/-- The homotopy tensor uses the native signed total on the original complexes. -/
@[instance_reducible]
def convolutionHomotopyMonoidalCategory : MonoidalCategory Ho :=
  let := localizedHomotopyMonoidal (k := k)
  reseat localizedHomotopyTensorIso (Iso.refl U)

/-- The homotopy symmetry of the original signed total. -/
@[instance_reducible]
def convolutionHomotopySymmetricCategory :
    letI := convolutionHomotopyMonoidalCategory (k := k)
    SymmetricCategory Ho :=
  letI := localizedHomotopyMonoidal (k := k)
  letI := localizedHomotopySymmetric (k := k)
  reseatSymmetric localizedHomotopyTensorIso (Iso.refl U)

attribute [local instance] convolutionHomotopyMonoidalCategory convolutionHomotopySymmetricCategory

/-- The native signed shift data on the actual homotopy tensor. -/
@[instance_reducible]
def convolutionHomotopyCommShift₂Int : (curriedTensor Ho).CommShift₂Int := by
  change (signedTotalHomotopyBifunctor B).CommShift₂Int
  exact signedTotalHomotopyBifunctorCommShift₂Int B

/-- The signed tensor, with the represented unit in degree zero, preserves
the bounded-above projective homotopy category. -/
theorem boundedAboveProjectiveCondition_convolution_isMonoidal :
    (boundedAboveProjectiveCondition k).IsMonoidal where
  prop_unit := by
    let C : Ch := (CochainComplex.singleFunctor PST 0).obj R
    change ∃ n : ℤ, C.IsStrictlyLE n ∧ ∀ i, Projective (C.X i)
    refine ⟨0, inferInstance, fun i => ?_⟩
    by_cases h : i = 0
    · subst i
      exact Projective.of_iso (HomologicalComplex.singleObjXSelf c 0 R).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X c 0 R i h).projective
  prop_tensor K L hK hL := by
    obtain ⟨a, ha, hKp⟩ := hK
    obtain ⟨b, hb, hLp⟩ := hL
    let : CochainComplex.IsStrictlyLE K.as a := ha
    let : CochainComplex.IsStrictlyLE L.as b := hb
    let : ∀ i, Projective (K.as.X i) := hKp
    let : ∀ i, Projective (L.as.X i) := hLp
    let T : Ch := HomologicalComplex.mapBifunctor K.as L.as B c
    change ∃ n : ℤ, T.IsStrictlyLE n ∧ ∀ i, Projective (T.X i)
    exact ⟨a + b, mapBifunctor_isStrictlyLE B K.as L.as a b, fun n =>
      convolutionTotal_projective F S curriedCorrespondenceBraiding_involutive K.as L.as n⟩

end AlgebraicGeometry.PresheafWithTransfers
