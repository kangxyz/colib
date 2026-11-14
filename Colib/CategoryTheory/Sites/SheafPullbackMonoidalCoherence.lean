/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.CategoryTheory.Sites.SheafPullbackMonoidal
public import StacksFrontier.CategoryTheory.Sites.SheafPushforwardMonoidal

/-!
# Comparison of the two sheaf inverse-image monoidal constructions

The localized left-Kan-extension construction and the adjoint construction use the same
comparison between sheafification and left Kan extension. This identifies that comparison
before any assertion that their tensorators agree.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace Colib.SheafPullbackCoherence

/-- Monoidal natural transformations between strong monoidal functors also commute with
oplax tensorators. -/
theorem app_tensor_comp_δ {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] {F G : C ⥤ D}
    [F.Monoidal] [G.Monoidal] (τ : F ⟶ G) [τ.IsMonoidal] (X Y : C) :
    τ.app (X ⊗ Y) ≫ δ G X Y = δ F X Y ≫ (τ.app X ⊗ₘ τ.app Y) := by
  apply (cancel_epi (μ F X Y)).mp
  simp only [← Category.assoc, NatTrans.IsMonoidal.tensor]
  simp

/-- Transporting an adjunction along the identity changes nothing. -/
theorem ofNatIsoRight_refl {B E : Type*} [Category* B] [Category* E]
    {L : B ⥤ E} {R : E ⥤ B} (adj : L ⊣ R) :
    adj.ofNatIsoRight (Iso.refl R) = adj := by
  apply Adjunction.ext
  ext X
  simp [Adjunction.ofNatIsoRight]

variable {C D : Type*} [Category* C] [Category* D]
  (G : C ⥤ D) (A : Type*) [Category* A] [MonoidalCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal]
  [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op X) A]
  [∀ P : Cᵒᵖ ⥤ A, Functor.HasPointwiseLeftKanExtension G.op P]

omit [MonoidalCategory A] [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal] in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison used to localize the native pullback is the inverse of the comparison
used by the adjoint monoidal construction. -/
theorem presheafToSheafCompSheafPullbackIso_eq :
    Functor.presheafToSheafCompSheafPullbackIso G A J K =
      (Stacks.SheafPushforwardMonoidal.lanSheafifyIso J K A G
        (G.sheafAdjunctionContinuous A J K)).symm := by
  unfold Functor.presheafToSheafCompSheafPullbackIso
  rw [ofNatIsoRight_refl]
  rfl

end Colib.SheafPullbackCoherence
