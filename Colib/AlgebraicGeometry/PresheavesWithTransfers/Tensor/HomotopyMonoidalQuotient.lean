/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctorBraided
import Colib.CategoryTheory.Monoidal.ReseatComparisons
import StacksFrontier.CategoryTheory.Localization.BifunctorCommShiftTwoLiftingIso

/-! # The monoidal homotopy quotient for signed convolution -/

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
local notation "B" => convolutionBifunctor F
local notation "c" => ComplexShape.up ℤ
local notation "Ch" => CochainComplex PST ℤ
local notation "Ho" => HomotopyCategory PST c
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

attribute [local instance] convolutionHomotopyEquivalencesMonoidal
  convolutionHomotopyMonoidalCategory convolutionHomotopySymmetricCategory

section

attribute [local instance] localizedHomotopyMonoidal localizedHomotopySymmetric

private abbrev localizedHomotopyTensorator (K L : Ch) :
    ((Q).obj K ⊗ (Q).obj L) ≅ (Q).obj (K ⊗ L) :=
  Localization.Monoidal.μ Q W (Iso.refl U) K L

end

/-- The quotient has Mathlib's strong monoidal structure before it is placed on the
literal total. -/
@[instance_reducible]
def localizedHomotopyQuotientMonoidal :
    letI := localizedHomotopyMonoidal (k := k)
    (Q).Monoidal :=
  letI := localizedHomotopyMonoidal (k := k)
  Functor.CoreMonoidal.toMonoidal (Localization.coreMonoidal Q W (Iso.refl U))

/-- Strong monoidality of the quotient into the native signed total on homotopy categories. -/
@[instance_reducible]
def convolutionHomotopyQuotientMonoidal : (Q).Monoidal := by
  let A := localizedHomotopyMonoidal (k := k)
  let A' := convolutionHomotopyMonoidalCategory (k := k)
  let C := convolutionCochainMonoidalCategory (k := k)
  let e := localizedHomotopyTensorIso (k := k)
  let ε := Iso.refl U
  let j : @Functor.Monoidal Ho _ A Ho _ A' (𝟭 Ho) := @reseatInverseMonoidal Ho _ A _ _ e ε
  let m : @Functor.Monoidal Ch _ C Ho _ A Q := localizedHomotopyQuotientMonoidal
  let m' := @Functor.Monoidal.instComp Ch _ C Ho _ A Ho _ A' Q (𝟭 Ho) m j
  exact @Functor.Monoidal.transport Ch _ C Ho _ A' (Q ⋙ 𝟭 Ho) Q m' (Functor.rightUnitor Q)

set_option maxHeartbeats 900000 in
-- Work with the specified component of each lifting through the homotopy quotient.
private theorem localizedHomotopyTensorIso_hom_app (K L : Ch) :
    letI := localizedHomotopyMonoidal (k := k)
    let e := localizedHomotopyTensorIso (k := k)
    ((e.app ((Q).obj K)).app ((Q).obj L)).hom =
      (localizedHomotopyTensorator K L).hom := by
  let := localizedHomotopyMonoidal (k := k)
  let T := signedTotalHomotopyBifunctor B
  let post := (Functor.whiskeringRight Ch Ch Ho).obj Q
  let A := curriedTensor Ch ⋙ post
  let A' := (B).map₂CochainComplex ⋙ post
  let : Localization.Lifting₂ Q Q W W A (curriedTensor Ho) := convolutionHomotopyTensorLifting
  let : Localization.Lifting₂ Q Q W W A' T := signedTotalHomotopyBifunctorLifting B
  let e := localizedHomotopyTensorIso (k := k)
  let τ := (Functor.isoWhiskerRight convolutionCochainTensorIso post).hom
  let t := localizedHomotopyTensorator K L
  let X := K ⊗ L
  let a : ((Q).obj K ⊗ (Q).obj L) ⟶ (Q).obj X :=
    ((Localization.Lifting₂.iso Q Q W W A (curriedTensor Ho)).hom.app K).app L
  let b : (Q).obj X ⟶ (Q).obj X := (τ.app K).app L
  let c' : (Q).obj X ⟶ (Q).obj X :=
    ((Localization.Lifting₂.iso Q Q W W A' T).inv.app K).app L
  have h : ((e.app ((Q).obj K)).app ((Q).obj L)).hom = a ≫ b ≫ c' :=
    Localization.lift₂NatTrans_app_app Q Q W W A A' (curriedTensor Ho) T τ K L
  have ha : a = t.hom := rfl
  have hb : b = 𝟙 ((Q).obj X) :=
    (show b = (Q).map (𝟙 X) from rfl).trans ((Q).map_id X)
  have hc : c' = 𝟙 ((Q).obj X) := rfl
  have hbc : b ≫ c' = 𝟙 ((Q).obj X) :=
    ((congrArg (b ≫ ·) hc).trans (Category.comp_id b)).trans hb
  exact h.trans (((congrArg (a ≫ ·) hbc).trans (Category.comp_id a)).trans ha)

-- The remaining proofs use the components of the comparison through the preceding equation.
attribute [local irreducible] localizedHomotopyTensorIso

set_option maxHeartbeats 850000 in
-- Compute the tensorator through the original localization comparison.
/-- The actual monoidal quotient tensorator on cochains is the identity of their signed total. -/
theorem convolutionHomotopyQuotientMonoidal_μ (K L : Ch) :
    letI := convolutionHomotopyQuotientMonoidal (k := k)
    Functor.LaxMonoidal.μ Q K L = 𝟙 _ := by
  let cCh : Category Ch := inferInstance
  let cHo : Category Ho := inferInstance
  let A : @MonoidalCategory Ho cHo := localizedHomotopyMonoidal (k := k)
  let A' : @MonoidalCategory Ho cHo := convolutionHomotopyMonoidalCategory (k := k)
  let C : @MonoidalCategory Ch cCh := convolutionCochainMonoidalCategory (k := k)
  let m : @Functor.Monoidal Ch cCh C Ho cHo A Q := localizedHomotopyQuotientMonoidal
  let m' : @Functor.Monoidal Ch cCh C Ho cHo A' Q := convolutionHomotopyQuotientMonoidal
  let e := localizedHomotopyTensorIso (k := k)
  let ε := Iso.refl U
  let b := (e.app ((Q).obj K)).app ((Q).obj L)
  let t := localizedHomotopyTensorator K L
  let μ := @Functor.LaxMonoidal.μ Ch cCh C Ho cHo A Q m.toLaxMonoidal K L
  have hp : @Functor.LaxMonoidal.μ Ch cCh C Ho cHo A' Q m'.toLaxMonoidal K L =
      b.inv ≫ μ := @Functor.Monoidal.transport_reseat_μ Ch Ho cCh cHo C A Q m _ _ e ε K L
  have hμ : μ = t.hom := rfl
  have ht : b.hom = t.hom := localizedHomotopyTensorIso_hom_app K L
  calc
    _ = b.inv ≫ μ := hp
    _ = b.inv ≫ t.hom := congrArg (b.inv ≫ ·) hμ
    _ = b.inv ≫ b.hom := congrArg (b.inv ≫ ·) ht.symm
    _ = _ := b.inv_hom_id

section QuotientShift

-- The shift comparison uses the tensorator component equation for this exact instance.
attribute [local irreducible] convolutionHomotopyQuotientMonoidal

set_option maxHeartbeats 1000000 in
-- Use the exact two-variable localized shift data on both readings of the tensorator.
/-- The shift comparison on signed cochains descends through the actual monoidal quotient. -/
theorem convolutionHomotopyQuotientMonoidalCommShift :
    letI := convolutionCochainCommShift₂Int (k := k)
    letI := convolutionHomotopyCommShift₂Int (k := k)
    letI := convolutionHomotopyQuotientMonoidal (k := k)
    Functor.LaxMonoidal.CommShift Q ℤ := by
  let := convolutionCochainCommShift₂Int (k := k)
  let := convolutionHomotopyCommShift₂Int (k := k)
  let := convolutionHomotopyQuotientMonoidal (k := k)
  let B₀ := (B).map₂CochainComplex ⋙ (Functor.whiskeringRight Ch Ch Ho).obj Q
  let H := signedTotalHomotopyBifunctor B
  let : B₀.CommShift₂Int := Functor.CommShift₂.postcompInt (B).map₂CochainComplex Q
  let : Localization.Lifting₂ Q Q W W B₀ H := signedTotalHomotopyBifunctorLifting B
  let φ := (Localization.Lifting₂.iso Q Q W W B₀ H).hom
  let hφ := Localization.lifting₂_iso_hom_commShift₂Int Q Q W W B₀ H
  refine ⟨fun L => ?_, fun K => ?_⟩
  · let := hφ.commShift_flipApp L
    have h : Functor.LaxMonoidal.μNatTransFst Q L = φ.flipApp L := by
      apply NatTrans.ext
      funext K
      change Functor.LaxMonoidal.μ Q K L = 𝟙 _
      exact convolutionHomotopyQuotientMonoidal_μ K L
    exact NatTrans.commShift_of_eq h
  · let := hφ.commShift_app K
    have h : Functor.LaxMonoidal.μNatTransSnd Q K = φ.app K := by
      apply NatTrans.ext
      funext L
      change Functor.LaxMonoidal.μ Q K L = 𝟙 _
      exact convolutionHomotopyQuotientMonoidal_μ K L
    exact NatTrans.commShift_of_eq h

end QuotientShift

set_option maxHeartbeats 850000 in
-- The localization and the transported symmetry use the same cochain components.
/-- The braiding on the signed total homotopy tensor is the image of the
Koszul braiding of the actual cochain representatives. -/
theorem convolutionHomotopy_braiding_on_cochains (K L : Ch) :
    (β_ ((Q).obj K) ((Q).obj L)).hom = (Q).map (β_ K L).hom := by
  let cHo : Category Ho := inferInstance
  let A : @MonoidalCategory Ho cHo := localizedHomotopyMonoidal (k := k)
  let s : @SymmetricCategory Ho cHo A := localizedHomotopySymmetric (k := k)
  let : MonoidalCategory Ho := A
  let : SymmetricCategory Ho := s
  let e := localizedHomotopyTensorIso (k := k)
  let ε := Iso.refl U
  let X := (Q).obj K
  let Y := (Q).obj L
  let t := localizedHomotopyTensorator K L
  let t' := localizedHomotopyTensorator L K
  let b := (Q).map (β_ K L).hom
  have hβ : (β_ X Y).hom = t.hom ≫ b ≫ t'.inv :=
    Localization.Monoidal.β_hom_app Q W ε K L
  exact @MonoidalCategory.reseatSymmetric_braiding_hom_of_components Ho cHo A s _ _ e ε X Y t t' b
    (localizedHomotopyTensorIso_hom_app K L) (localizedHomotopyTensorIso_hom_app L K) hβ

end AlgebraicGeometry.PresheafWithTransfers
