/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SmallModelTransformations

/-!
# Invertibility of native model transformation operations

The native endpoint wrappers are the ordinary whiskering and equality transport.
Their invertibility is inherited from those operations without changing any endpoint.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory
variable {U V W X Y : WideSubcategory preservesZero.{u}}

instance (E : U ⟶ V) {P Q : V ⟶ W}
    (μ : P.hom.toFunctor ⟶ Q.hom.toFunctor) [IsIso μ] :
    IsIso (modelWhiskerLeft E μ) := by
  rw [modelWhiskerLeft_eq]
  infer_instance

instance (A : U ⟶ V) (E : V ⟶ W) (B : U ⟶ X) (P : X ⟶ W) (Q : W ⟶ Y)
    (α : (A ≫ E).hom.toFunctor ⟶ (B ≫ P).hom.toFunctor) [IsIso α] :
    IsIso (modelWhiskerRightAssoc A E B P Q α) := by
  rw [modelWhiskerRightAssoc_eq]
  infer_instance

instance {F G : U ⟶ V} (h : F = G) : IsIso (modelEqToHom h) := by
  rw [modelEqToHom_eq]
  infer_instance

instance (E : U ⟶ V) {P : V ⟶ V}
    (δ : P.hom.toFunctor ⟶ (𝟙 V : V ⟶ V).hom.toFunctor) [IsIso δ] :
    IsIso (modelWhiskerLeftId E δ) := by
  rw [modelWhiskerLeftId_eq]
  infer_instance

end CategoryTheory.Waldhausen.IteratedS
