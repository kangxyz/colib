/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedMonoidalShift
public import StacksFrontier.CategoryTheory.Monoidal.LaxMonoidalCommShift
import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-! # The signed tensorators of the projective inclusion and equivalence -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)]
  [MonoidalPreadditive (Cor k)]

local notation "PST" => TransferCoefficients k
local notation "P" => boundedAboveProjectiveCondition k
local notation "J" => BoundedAboveProjectiveHomotopy k
local notation "H" => HomotopyCategory PST (ComplexShape.up ℤ)

attribute [local instance] convolutionHomotopyMonoidalCategory convolutionHomotopySymmetricCategory
  boundedAboveProjectiveCondition_convolution_isMonoidal

private instance : (P).IsStableUnderShift ℤ :=
  (inferInstance : (P).IsTriangulated).toIsStableUnderShift

attribute [local instance] convolutionHomotopyCommShift₂Int convolutionProjectiveCommShift₂Int

set_option maxHeartbeats 1050000 in
-- Use the actual two-variable shift on the fully faithful inclusion.
/-- The projective inclusion intertwines the original one-variable shifts in both variables. -/
theorem convolutionProjectiveInclusionMonoidalCommShift :
    Functor.LaxMonoidal.CommShift (P).ι ℤ := by
  let I := (P).ι
  refine ⟨fun Y => ?_, fun X => ?_⟩
  · let G := (curriedTensor J).flip.obj Y
    let H₀ := (curriedTensor H).flip.obj (I.obj Y)
    let e : G ⋙ I ≅ I ⋙ H₀ := Iso.refl _
    have he : e.inv = Functor.LaxMonoidal.μNatTransFst I Y := by
      ext X
      rfl
    let : G.CommShift ℤ := Functor.CommShift.ofComp e ℤ
    let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
    let : NatTrans.CommShift e.inv ℤ := NatTrans.CommShift.of_iso_inv e ℤ
    exact NatTrans.commShift_of_eq he.symm
  · let G := (curriedTensor J).obj X
    let H₀ := (curriedTensor H).obj (I.obj X)
    let e : G ⋙ I ≅ I ⋙ H₀ := Iso.refl _
    have he : e.inv = Functor.LaxMonoidal.μNatTransSnd I X := by
      ext Y
      rfl
    let : G.CommShift ℤ := Functor.CommShift.ofComp e ℤ
    let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
    let : NatTrans.CommShift e.inv ℤ := NatTrans.CommShift.of_iso_inv e ℤ
    exact NatTrans.commShift_of_eq he.symm

variable [HasDerivedCategory.{w} (TransferCoefficients k)]

set_option quotPrecheck false in
local notation "D" => DerivedCategory.Minus PST
local notation "E" => boundedAboveProjectiveEquivalence k

attribute [local instance] derivedConvolutionMonoidalCategory derivedConvolutionSymmetricCategory
  derivedConvolutionInverseMonoidal derivedConvolutionCommShift₂Int

set_option maxHeartbeats 1050000 in
-- The inverse projective equivalence tensorators are the original unit.
/-- Both tensorators of the inverse projective equivalence preserve the chosen shifts. -/
theorem derivedConvolutionInverseMonoidalCommShift :
    Functor.LaxMonoidal.CommShift (E).inverse ℤ := by
  let I := (E).inverse
  let V := (E).functor
  let : (E).CommShift ℤ := boundedAboveProjectiveEquivalenceCommShift k
  refine ⟨fun Y => ?_, fun X => ?_⟩
  · let W := I ⋙ tensorRight (I.obj Y)
    let a : I ⋙ tensorRight (I.obj Y) ≅ W ⋙ 𝟭 J := (Functor.rightUnitor W).symm
    let b : W ⋙ (V ⋙ I) ≅ tensorRight Y ⋙ I := (Functor.associator W V I).symm
    let t : I ⋙ tensorRight (I.obj Y) ⟶ tensorRight Y ⋙ I :=
      a.hom ≫ Functor.whiskerLeft W (E).unitIso.hom ≫ b.hom
    have ht : Functor.LaxMonoidal.μNatTransFst I Y = t := by
      apply NatTrans.ext
      funext X
      change Functor.LaxMonoidal.μ (E).inverse X Y = 𝟙 _ ≫ (E).unitIso.hom.app _ ≫ 𝟙 _
      simpa only [Category.id_comp, Category.comp_id] using derivedConvolutionInverseMonoidal_μ X Y
    rw [ht]
    dsimp only [t, a, b, W, I, V]
    infer_instance
  · let W := I ⋙ tensorLeft (I.obj X)
    let a : I ⋙ tensorLeft (I.obj X) ≅ W ⋙ 𝟭 J := (Functor.rightUnitor W).symm
    let b : W ⋙ (V ⋙ I) ≅ tensorLeft X ⋙ I := (Functor.associator W V I).symm
    let t : I ⋙ tensorLeft (I.obj X) ⟶ tensorLeft X ⋙ I :=
      a.hom ≫ Functor.whiskerLeft W (E).unitIso.hom ≫ b.hom
    have ht : Functor.LaxMonoidal.μNatTransSnd I X = t := by
      apply NatTrans.ext
      funext Y
      change Functor.LaxMonoidal.μ (E).inverse X Y = 𝟙 _ ≫ (E).unitIso.hom.app _ ≫ 𝟙 _
      simpa only [Category.id_comp, Category.comp_id] using derivedConvolutionInverseMonoidal_μ X Y
    rw [ht]
    dsimp only [t, a, b, W, I, V]
    infer_instance

end AlgebraicGeometry.PresheafWithTransfers
