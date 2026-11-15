/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.DerivedConvolution
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorSymmetry
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionSwap

/-! # Koszul symmetry of the signed derived convolution -/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K

variable (F : Cor k ⥤ Cor k ⥤ Cor k) (s : F ≅ F.flip)
  (hs : ∀ Y Z, (s.hom.app Y).app Z ≫ (s.hom.app Z).app Y = 𝟙 _)

variable [HasDerivedCategory.{w} PST(k)]
variable [F.Additive] [∀ Y, (F.obj Y).Additive]

/-- The correspondence swap induces the signed swap of derived convolution. -/
def derivedConvolutionSwap : derivedConvolution F ≅ (derivedConvolution F).flip :=
  projectiveDerivedMinusBifunctorSwap (convolutionBifunctor F) (convolutionSwap F s hs)

omit [F.Additive] [∀ Y, (F.obj Y).Additive] in
/-- The signed derived convolution swap is involutive. -/
theorem derivedConvolutionSwap_involutive (K L : DerivedCategory.Minus PST(k)) :
    ((derivedConvolutionSwap F s hs).hom.app K).app L ≫
      ((derivedConvolutionSwap F s hs).hom.app L).app K = 𝟙 _ :=
  projectiveDerivedMinusBifunctorSwap_involutive (convolutionBifunctor F)
    (convolutionSwap F s hs) (fun P Q => by
      have h := (convolutionSwap F s hs).hom_inv_id
      exact NatTrans.congr_app (NatTrans.congr_app h P) Q) K L

end AlgebraicGeometry.PresheafWithTransfers
