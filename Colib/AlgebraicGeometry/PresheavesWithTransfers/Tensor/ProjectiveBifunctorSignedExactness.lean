/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorShift
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorTriangulated
import StacksFrontier.CategoryTheory.Localization.BifunctorCommShiftTwoLiftingIso
import StacksFrontier.CategoryTheory.Shift.DetectingCommShift
import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery.LeftFactorTriangulated

/-! # Exactness for the signed shift on the original homotopy tensor -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor.Reduction

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ
local notation "H" => HomotopyCategory PST(k) c
local notation "Q" => HomotopyCategory.quotient PST(k) c
local notation "W" => HomologicalComplex.homotopyEquivalences PST(k) c

variable (B : PST(k) ⥤ PST(k) ⥤ PST(k)) [B.Additive] [∀ X, (B.obj X).Additive]

set_option maxHeartbeats 850000 in
-- Compare the signed localization shift and the original cone shift on cochains.
/-- Stacks' cone comparison preserves the actual second-variable Koszul shift. -/
theorem signedTotalHomotopyBifunctor_obj_isTriangulated (K : H) :
    ((signedTotalHomotopyBifunctor B).obj K).IsTriangulated := by
  let C := B.map₂CochainComplex.obj K.as
  let G := B.map₂CochainComplex ⋙ (Functor.whiskeringRight _ _ _).obj Q
  let T := signedTotalHomotopyBifunctor B
  let X := T.obj K
  let Y := bifunctorPhi B K.as
  let : Localization.Lifting₂ Q Q W W G T := signedTotalHomotopyBifunctorLifting B
  let : Y.CommShift ℤ := bifunctorXi B K.as
  let d : Q ⋙ X ≅ G.obj K.as := (Localization.Lifting₂.iso Q Q W W G T).app K.as
  let f : Q ⋙ Y ≅ C ⋙ Q := bifunctorPhiFactors B K.as
  let e := signedTotalHomotopyBifunctorLeftIso B K
  have h₁ : NatTrans.CommShift (F₁ := Q ⋙ X) (F₂ := G.obj K.as) d.hom ℤ :=
    Localization.lifting₂_iso_hom_app_commShift Q Q W W G T K.as
  have h₂ : NatTrans.CommShift (F₁ := Q ⋙ Y) (F₂ := C ⋙ Q) f.hom ℤ :=
    Quotient.liftCommShift_compatibility _ _ _ _
  let : NatTrans.CommShift f.inv ℤ := NatTrans.CommShift.of_iso_inv f ℤ
  have h₃ : NatTrans.CommShift e.hom ℤ := by
    let : (Q).EssSurj := ⟨fun L => ⟨L.as, ⟨Iso.refl _⟩⟩⟩
    apply NatTrans.commShift_of_whiskerLeft Q e.hom
    have he : Functor.whiskerLeft Q e.hom = d.hom ≫ f.inv := by
      apply NatTrans.ext
      funext L
      change 𝟙 _ = 𝟙 _ ≫ 𝟙 _
      exact (Category.id_comp _).symm
    rw [he]
    exact NatTrans.CommShift.comp d.hom f.inv ℤ
  let : Y.IsTriangulated := bifunctorPhi_isTriangulated B K.as
  let : NatTrans.CommShift e.inv ℤ := NatTrans.CommShift.of_iso_inv e ℤ
  change X.IsTriangulated
  exact Functor.isTriangulated_of_iso e.symm

end AlgebraicGeometry.PresheafWithTransfers
