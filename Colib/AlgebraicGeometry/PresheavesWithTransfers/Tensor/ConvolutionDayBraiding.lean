/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionAssociator
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionSwap
import Mathlib.CategoryTheory.Monoidal.DayConvolution.Braided

/-! # Comparison of the coend swap with Day braiding -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite MonoidalCategory
open scoped DayConvolution TensorProduct

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k] [MonoidalCategory (Cor k)] [SymmetricCategory (Cor k)]
  [MonoidalPreadditive (Cor k)]

local notation "PST" => TransferCoefficients k
local notation "F" => curriedTensor (Cor k)
local notation "S" => BraidedCategory.curriedBraidingNatIso (Cor k)
local infixl:70 " ⋆ " => convolutionPresheaf F

private theorem eq_dayBraiding_of_tmul
    {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    {A B : C ⥤ ModuleCat.{v} ℤ} [DayConvolution A B] [DayConvolution B A]
    (f : A ⊛ B ⟶ B ⊛ A)
    (hf : ∀ (X Y : C) (p : A.obj X) (q : B.obj Y),
      f.app (X ⊗ Y) ((DayConvolution.unit A B).app (X, Y) (p ⊗ₜ[ℤ] q)) =
        (B ⊛ A).map (β_ Y X).hom ((DayConvolution.unit B A).app (Y, X) (q ⊗ₜ[ℤ] p))) :
    f = (DayConvolution.braiding A B).hom := by
  apply Functor.hom_ext_of_isLeftKanExtension _ (DayConvolution.unit A B)
  apply NatTrans.ext
  funext XY
  obtain ⟨X, Y⟩ := XY
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro p q
  have h := ConcreteCategory.congr_hom
    (DayConvolution.unit_app_braiding_hom_app A B X Y) (p ⊗ₜ[ℤ] q)
  simp only [ModuleCat.comp_apply] at h
  -- The module braiding sends the pure tensor to the reversed pure tensor by definition.
  exact (hf X Y p q).trans h.symm

/-- Realizing integral coend coefficients carries the original swap to Day braiding. -/
theorem convolutionForget_map_swap (P Q : PST) :
    let W := convolutionForget (k := k)
    letI := convolutionDayComparison P Q
    letI := convolutionDayComparison Q P
    W.map (convolutionSwapHom F S P Q) = (DayConvolution.braiding (W.obj P) (W.obj Q)).hom := by
  intro W
  let := convolutionDayComparison P Q
  let := convolutionDayComparison Q P
  refine eq_dayBraiding_of_tmul (A := W.obj P) (B := W.obj Q)
    (W.map (convolutionSwapHom F S P Q)) ?_
  rintro ⟨Y⟩ ⟨Z⟩ p q
  change sections P Y at p
  change sections Q Z at q
  let m := (W.map (convolutionSwapHom F S P Q)).app (op (Y ⊗ Z))
  let n := (W.obj (Q ⋆ P)).map (β_ Y Z).hom.op
  let x := convolutionGenerator F P Q (Y ⊗ Z) Y Z p q (𝟙 _)
  let y := convolutionGenerator F Q P (Z ⊗ Y) Z Y q p (𝟙 _)
  let z := convolutionGenerator F Q P (Y ⊗ Z) Z Y q p (β_ Y Z).hom
  let a := (convolutionDayUnit P Q).app (op Y, op Z) (p ⊗ₜ[ℤ] q)
  let b := (convolutionDayUnit Q P).app (op Z, op Y) (q ⊗ₜ[ℤ] p)
  change m a = n b
  have ha : a = x := convolutionDayUnit_tmul P Q Y Z p q
  have hb : b = y := convolutionDayUnit_tmul Q P Z Y q p
  have hm : m x = z := by
    have h := convolutionSwapHom_generator F S P Q (Y ⊗ Z) Y Z p q (𝟙 _)
    rw [Category.id_comp] at h
    exact h
  have hn : n y = z := by
    have h := convolutionPresheaf_transfer_generator F Q P (β_ Y Z).hom Z Y q p (𝟙 _)
    rw [Category.comp_id] at h
    exact h
  calc
    m a = m x := congrArg m ha
    _ = z := hm
    _ = n y := hn.symm
    _ = n b := congrArg n hb.symm

end AlgebraicGeometry.PresheafWithTransfers
