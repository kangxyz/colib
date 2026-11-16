/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.SheafPullbackMonoidalCoherence

/-! # Native pullback tensor comparison on sheafifications -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal

namespace Colib.SheafPullbackCoherence

variable {C D : Type*} [Category* C] [Category* D]
  (G : C ⥤ D) (A : Type*) [Category* A] [MonoidalCategory A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [G.IsContinuous J K] [(G.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal]
  [∀ P : Cᵒᵖ ⥤ A, Functor.HasPointwiseLeftKanExtension G.op P]

variable [∀ X : Dᵒᵖ, IsFiltered (CostructuredArrow G.op X)]
  [∀ (X : Dᵒᵖ) (M : A),
    PreservesColimitsOfShape (CostructuredArrow G.op X) ((curriedTensor A).obj M)]
  [∀ (X : Dᵒᵖ) (M : A),
    PreservesColimitsOfShape (CostructuredArrow G.op X) ((curriedTensor A).flip.obj M)]

attribute [local instance] Sheaf.monoidalCategory Functor.lanMonoidal

/-- The localization comparison is monoidal for the native Kan-extension construction. -/
theorem nativeComparison_isMonoidal :
    letI := Functor.sheafPullbackMonoidal G A J K
    (Functor.presheafToSheafCompSheafPullbackIso G A J K).hom.IsMonoidal := by
  let : Localization.Lifting (presheafToSheaf J A) J.W
      (G.op.lan ⋙ presheafToSheaf K A) (G.sheafPullback A J K) :=
    ⟨Functor.presheafToSheafCompSheafPullbackIso G A J K⟩
  exact Localization.Monoidal.lifting_isMonoidal (presheafToSheaf J A) J.W
    (G.sheafPullback A J K) (G.op.lan ⋙ presheafToSheaf K A)

/-- The native oplax tensorator satisfies the same comparison equation as the adjoint
construction, without identifying the two monoidal instances by assumption. -/
theorem nativeComparison_inv_app_tensor_comp_δ (P Q : Cᵒᵖ ⥤ A) :
    letI := Functor.sheafPullbackMonoidal G A J K
    (Functor.presheafToSheafCompSheafPullbackIso G A J K).inv.app (P ⊗ Q) ≫
        δ (presheafToSheaf J A ⋙ G.sheafPullback A J K) P Q =
      δ (G.op.lan ⋙ presheafToSheaf K A) P Q ≫
        ((Functor.presheafToSheafCompSheafPullbackIso G A J K).inv.app P ⊗ₘ
          (Functor.presheafToSheafCompSheafPullbackIso G A J K).inv.app Q) := by
  let := Functor.sheafPullbackMonoidal G A J K
  have := nativeComparison_isMonoidal G A J K
  exact app_tensor_comp_δ (Functor.presheafToSheafCompSheafPullbackIso G A J K).inv P Q

end Colib.SheafPullbackCoherence
