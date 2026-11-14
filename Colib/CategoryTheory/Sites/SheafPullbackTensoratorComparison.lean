/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.SheafPullbackNativeTensorator

/-! # Native and adjoint pullback tensorators agree -/

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

variable [∀ X : Dᵒᵖ, HasColimitsOfShape (CostructuredArrow G.op X) A]

/-- The native and adjoint oplax tensorators agree on sheafifications. -/
theorem native_delta_eq_adjoint_delta_sheafify (P Q : Cᵒᵖ ⥤ A) :
    letI := Functor.sheafPullbackMonoidal G A J K
    δ (G.sheafPullback A J K) ((presheafToSheaf J A).obj P)
        ((presheafToSheaf J A).obj Q) =
      (letI := Stacks.SheafPushforwardMonoidal.pullbackOplaxMonoidal J K A G
        (G.sheafAdjunctionContinuous A J K)
       δ (G.sheafPullback A J K) ((presheafToSheaf J A).obj P)
        ((presheafToSheaf J A).obj Q)) := by
  let := Functor.sheafPullbackMonoidal G A J K
  apply (cancel_epi ((G.sheafPullback A J K).map
    (δ (presheafToSheaf J A) P Q))).mp
  apply (cancel_epi
    ((Functor.presheafToSheafCompSheafPullbackIso G A J K).inv.app (P ⊗ Q))).mp
  have hn := nativeComparison_inv_app_tensor_comp_δ G A J K P Q
  have hm := Stacks.SheafPushforwardMonoidal.lanSheafifyIso_hom_app_tensor_comp_δ
    J K A G (G.sheafAdjunctionContinuous A J K) P Q
  rw [presheafToSheafCompSheafPullbackIso_eq] at hn ⊢
  exact hn.trans hm.symm

/-- The native and adjoint oplax tensorators agree on arbitrary sheaves. -/
theorem native_delta_eq_adjoint_delta (M N : Sheaf J A) :
    letI := Functor.sheafPullbackMonoidal G A J K
    δ (G.sheafPullback A J K) M N =
      (letI := Stacks.SheafPushforwardMonoidal.pullbackOplaxMonoidal J K A G
        (G.sheafAdjunctionContinuous A J K)
       δ (G.sheafPullback A J K) M N) := by
  let := Functor.sheafPullbackMonoidal G A J K
  let eM := (sheafificationAdjunction J A).counit.app M
  let eN := (sheafificationAdjunction J A).counit.app N
  apply (cancel_epi ((G.sheafPullback A J K).map (eM ⊗ₘ eN))).mp
  have hn := (Functor.OplaxMonoidal.δ_natural (G.sheafPullback A J K) eM eN).symm
  have hm := (
    letI := Stacks.SheafPushforwardMonoidal.pullbackOplaxMonoidal J K A G
      (G.sheafAdjunctionContinuous A J K)
    (Functor.OplaxMonoidal.δ_natural (G.sheafPullback A J K) eM eN).symm)
  dsimp only [Functor.id_obj] at hn hm
  rw [hn, hm]
  dsimp only [Functor.comp_obj]
  rw [native_delta_eq_adjoint_delta_sheafify G A J K
    ((sheafToPresheaf J A).obj M) ((sheafToPresheaf J A).obj N)]

end Colib.SheafPullbackCoherence
