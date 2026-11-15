/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift
public import StacksFrontier.CategoryTheory.Monoidal.ReseatFunctorBraided
import StacksFrontier.CategoryTheory.Localization.BifunctorCommShiftTwoLiftingIso
import StacksFrontier.CategoryTheory.Monoidal.ReseatConstraints

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
  change (((Localization.lift₂NatTrans Q Q W W A A' (curriedTensor Ho) T
    (Functor.isoWhiskerRight convolutionCochainTensorIso post).hom).app
    ((Q).obj K)).app ((Q).obj L)) = _
  rw [Localization.lift₂NatTrans_app_app]
  change (localizedHomotopyTensorator K L).hom ≫ (Q).map (𝟙 (K ⊗ L)) ≫ 𝟙 _ =
    (localizedHomotopyTensorator K L).hom
  rw [(Q).map_id, Category.comp_id, Category.comp_id]

set_option maxHeartbeats 850000 in
-- Compute the tensorator through the original localization comparison.
/-- The actual monoidal quotient tensorator on cochains is the identity of their signed total. -/
theorem convolutionHomotopyQuotientMonoidal_μ (K L : Ch) :
    letI := convolutionHomotopyQuotientMonoidal (k := k)
    Functor.LaxMonoidal.μ Q K L = 𝟙 _ := by
  let := convolutionHomotopyQuotientMonoidal (k := k)
  let A := localizedHomotopyMonoidal (k := k)
  let A' := convolutionHomotopyMonoidalCategory (k := k)
  let C := convolutionCochainMonoidalCategory (k := k)
  let e := localizedHomotopyTensorIso (k := k)
  let ε := Iso.refl U
  let X := (Q).obj K
  let Y := (Q).obj L
  let j : @Functor.Monoidal Ho _ A Ho _ A' (𝟭 Ho) := @reseatInverseMonoidal Ho _ A _ _ e ε
  let m : @Functor.Monoidal Ch _ C Ho _ A Q := localizedHomotopyQuotientMonoidal
  let m' := @Functor.Monoidal.instComp Ch _ C Ho _ A Ho _ A' Q (𝟭 Ho) m j
  let ρ := Functor.rightUnitor Q
  let μ := @Functor.LaxMonoidal.μ Ho _ A Ho _ A' (𝟭 Ho) j.toLaxMonoidal X Y
  have hμ : μ = ((e.app X).app Y).inv := rfl
  have hρ := @Functor.Monoidal.transport_μ Ch _ _ Ho _ _ (Q ⋙ 𝟭 Ho) Q m' ρ K L
  change Functor.LaxMonoidal.μ Q K L = _ at hρ
  have hK : ρ.inv.app K = 𝟙 X := rfl
  have hL : ρ.inv.app L = 𝟙 Y := rfl
  have hKL : ρ.hom.app (K ⊗ L) = 𝟙 ((Q).obj (K ⊗ L)) := rfl
  rw [hK, hL, hKL, id_tensorHom_id, Category.id_comp] at hρ
  let p := @Functor.LaxMonoidal.μ Ch _ C Ho _ A' (Q ⋙ 𝟭 Ho) m'.toLaxMonoidal K L
  have hp : p = μ ≫ (localizedHomotopyTensorator K L).hom := rfl
  have hρ' : Functor.LaxMonoidal.μ Q K L = p := hρ.trans (Category.comp_id p)
  let : MonoidalCategory Ho := A
  let b : (e.app X).app Y = localizedHomotopyTensorator K L :=
    Iso.ext (localizedHomotopyTensorIso_hom_app K L)
  calc
    _ = p := hρ'
    _ = μ ≫ (localizedHomotopyTensorator K L).hom := hp
    _ = ((e.app X).app Y).inv ≫ (localizedHomotopyTensorator K L).hom :=
      congrArg (· ≫ (localizedHomotopyTensorator K L).hom) hμ
    _ = (localizedHomotopyTensorator K L).inv ≫ (localizedHomotopyTensorator K L).hom :=
      congrArg (fun z => z.inv ≫ (localizedHomotopyTensorator K L).hom) b
    _ = _ := (localizedHomotopyTensorator K L).inv_hom_id

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
  have hl (L : Ch) :
      Functor.LaxMonoidal.μNatTransFst Q L =
        ((Localization.Lifting₂.iso Q Q W W B₀.flip H.flip).hom.app L) := by
    apply NatTrans.ext
    funext K
    change Functor.LaxMonoidal.μ Q K L = 𝟙 _
    exact convolutionHomotopyQuotientMonoidal_μ K L
  have hr (K : Ch) :
      Functor.LaxMonoidal.μNatTransSnd Q K =
        ((Localization.Lifting₂.iso Q Q W W B₀ H).hom.app K) := by
    apply NatTrans.ext
    funext L
    change Functor.LaxMonoidal.μ Q K L = 𝟙 _
    exact convolutionHomotopyQuotientMonoidal_μ K L
  refine ⟨fun L => ?_, fun K => ?_⟩
  · let := Localization.lifting₂_iso_hom_app_commShift (M := ℤ) Q Q W W B₀.flip H.flip L
    exact NatTrans.commShift_of_eq (hl L)
  · let := Localization.lifting₂_iso_hom_app_commShift (M := ℤ) Q Q W W B₀ H K
    exact NatTrans.commShift_of_eq (hr K)

set_option maxHeartbeats 850000 in
-- The localization and the transported symmetry use the same cochain components.
/-- The braiding on the signed total homotopy tensor is the image of the
Koszul braiding of the actual cochain representatives. -/
theorem convolutionHomotopy_braiding_on_cochains (K L : Ch) :
    (β_ ((Q).obj K) ((Q).obj L)).hom = (Q).map (β_ K L).hom := by
  let : MonoidalCategory Ho := localizedHomotopyMonoidal (k := k)
  let : SymmetricCategory Ho := localizedHomotopySymmetric (k := k)
  let e := localizedHomotopyTensorIso (k := k)
  let ε := Iso.refl U
  let X := (Q).obj K
  let Y := (Q).obj L
  let t := localizedHomotopyTensorator K L
  let t' := localizedHomotopyTensorator L K
  have he : (e.app X).app Y = t := Iso.ext (localizedHomotopyTensorIso_hom_app K L)
  have he' : (e.app Y).app X = t' := Iso.ext (localizedHomotopyTensorIso_hom_app L K)
  have hβ := Localization.Monoidal.β_hom_app Q W ε K L
  change (β_ X Y).hom = (localizedHomotopyTensorator K L).hom ≫ (Q).map (β_ K L).hom ≫
    (localizedHomotopyTensorator L K).inv at hβ
  have h := MonoidalCategory.reseatSymmetric_braiding e ε X Y
  let b := (β_ X Y).hom
  let b' := (Q).map (β_ K L).hom
  change _ = ((e.app X).app Y).inv ≫ b ≫ ((e.app Y).app X).hom at h
  calc
    _ = _ := h
    _ = t.inv ≫ b ≫ t'.hom :=
      congrArg₂ (fun g g' => g.inv ≫ b ≫ g'.hom) he he'
    _ = t.inv ≫ (t.hom ≫ b' ≫ t'.inv) ≫ t'.hom :=
      congrArg (fun g => t.inv ≫ g ≫ t'.hom) hβ
    _ = b' := by simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.PresheafWithTransfers
