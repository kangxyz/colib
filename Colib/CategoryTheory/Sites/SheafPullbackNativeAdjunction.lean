/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.SheafPullbackTensoratorComparison

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

/-- The native and adjoint oplax unit comparisons agree. -/
theorem native_eta_eq_adjoint_eta :
    letI := Functor.sheafPullbackMonoidal G A J K
    η (G.sheafPullback A J K) =
      (letI := Stacks.SheafPushforwardMonoidal.pullbackOplaxMonoidal J K A G
        (G.sheafAdjunctionContinuous A J K)
       η (G.sheafPullback A J K)) := by
  let := Functor.sheafPullbackMonoidal G A J K
  have := nativeComparison_isMonoidal G A J K
  have hn :
      (Functor.presheafToSheafCompSheafPullbackIso G A J K).inv.app (𝟙_ _) ≫
        η (presheafToSheaf J A ⋙ G.sheafPullback A J K) =
      η (G.op.lan ⋙ presheafToSheaf K A) := by
    apply (cancel_epi (ε (G.op.lan ⋙ presheafToSheaf K A))).mp
    simp only [← Category.assoc, NatTrans.IsMonoidal.unit]
    simp
  have hm := Stacks.SheafPushforwardMonoidal.lanSheafifyIso_hom_app_unit_comp_η
    J K A G (G.sheafAdjunctionContinuous A J K)
  apply (cancel_epi ((G.sheafPullback A J K).map (η (presheafToSheaf J A)))).mp
  apply (cancel_epi
    ((Functor.presheafToSheafCompSheafPullbackIso G A J K).inv.app (𝟙_ _))).mp
  rw [presheafToSheafCompSheafPullbackIso_eq] at hn ⊢
  exact hn.trans hm.symm

/-- The original Kan-extension/localization monoidal inverse image is compatible with its
original sheaf adjunction, not merely with a newly chosen monoidal structure. -/
theorem nativeSheafAdjunction_isMonoidal :
    letI := Functor.sheafPullbackMonoidal G A J K
    letI := Stacks.SheafPushforwardMonoidal.pushforwardLaxMonoidal J K A G
    (G.sheafAdjunctionContinuous A J K).IsMonoidal := by
  let := Functor.sheafPullbackMonoidal G A J K
  let := Stacks.SheafPushforwardMonoidal.pushforwardLaxMonoidal J K A G
  constructor
  · rw [native_eta_eq_adjoint_eta G A J K]
    exact Adjunction.IsMonoidal.leftAdjoint_ε (adj := G.sheafAdjunctionContinuous A J K)
  · intro M N
    rw [native_delta_eq_adjoint_delta G A J K]
    exact Adjunction.IsMonoidal.leftAdjoint_μ (adj := G.sheafAdjunctionContinuous A J K) M N

end Colib.SheafPullbackCoherence
