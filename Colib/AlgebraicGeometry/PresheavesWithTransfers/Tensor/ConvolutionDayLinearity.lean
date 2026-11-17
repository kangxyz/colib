/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Convolution
public import Colib.CategoryTheory.Preadditive.ConvolutionLinearity
import Colib.AlgebraicGeometry.Correspondences.Coproducts.Binary

/-!
# Linearity of convolution cocones in the correspondence label

A family of bilinear coefficient pairings satisfying the transfer relations
is additive in the correspondence label. The proof uses the two projections
and the fold of the original binary biproduct in the correspondence category.
This is the extra relation needed to identify the integral coend with
ordinary pointwise Day convolution on the additive coefficient functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K

variable (F : Cor k ⥤ Cor k ⥤ Cor k) [F.Additive]
variable {P Q : PST(k)} {X : Cor k} {M : Type v} [AddCommGroup M]

/-- The two transfer relations already force addition in the correspondence label. -/
theorem convolutionPairing_add_correspondence
    (e : ∀ Y Z : Cor k, (X ⟶ (F.obj Y).obj Z) → (sections P Y →+ sections Q Z →+ M))
    (he : ∀ {Y Y' Z Z' : Cor k} (f : Y ⟶ Y') (g : Z ⟶ Z')
      (s : sections P Y') (t : sections Q Z') (a : X ⟶ (F.obj Y).obj Z),
      e Y Z a (transfer P f s) (transfer Q g t) =
        e Y' Z' (a ≫ convolutionCorrespondenceMap F f g) s t)
    (Y Z : Cor k) (a b : X ⟶ (F.obj Y).obj Z) (s : sections P Y) (t : sections Q Z) :
    e Y Z (a + b) s t = e Y Z a s t + e Y Z b s t := by
  exact CategoryTheory.Preadditive.Convolution.pairing_add_hom F (P := P.obj) (Q := Q.obj)
    e he Y Z a b s t

end AlgebraicGeometry.PresheafWithTransfers
