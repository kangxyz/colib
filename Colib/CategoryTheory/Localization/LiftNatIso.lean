/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Localization.Predicate

/-! # The comparison between two lifts of one functor -/

@[expose] public noncomputable section

namespace CategoryTheory.Localization

/-- The comparison induced by the identity on a common functor evaluates to the two
specified lifting maps on the image of the localization. -/
theorem liftNatIso_refl_hom_app
    {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
    (L : C₁ ⥤ C₂) (W : MorphismProperty C₁) [L.IsLocalization W]
    (H : C₁ ⥤ C₃) {F G : C₂ ⥤ C₃} (a : L ⋙ F ≅ H) (b : H ≅ L ⋙ G) (X : C₁) :
    letI : Lifting L W H F := ⟨a⟩
    letI : Lifting L W H G := ⟨b.symm⟩
    (liftNatIso L W H H F G (Iso.refl H)).hom.app (L.obj X) =
      a.hom.app X ≫ b.hom.app X := by
  let : Lifting L W H F := ⟨a⟩
  let : Lifting L W H G := ⟨b.symm⟩
  rw [liftNatIso_hom, liftNatTrans_app]
  change a.hom.app X ≫ 𝟙 (H.obj X) ≫ b.hom.app X = _
  rw [Category.id_comp]

end CategoryTheory.Localization
