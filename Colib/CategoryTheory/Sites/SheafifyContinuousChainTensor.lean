/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.Sites.SheafifyContinuousMonoidal
public import Colib.Algebra.Homology.MapChainLaxTensorNatTrans
public import StacksFrontier.CategoryTheory.Sites.MonoidalPreadditive
/-! # The canonical sheafification-reindex tensor square on actual chain complexes -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace CategoryTheory.Functor
open Stacks.SheafPushforwardMonoidal
attribute [local instance] Sheaf.monoidalCategory Sheaf.monoidalPreadditive
  sheafToPresheafLaxMonoidal pushforwardLaxMonoidal
variable {C D : Type*} [Category C] [Category D]
  (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [F.IsContinuous J K] (A : Type*) [Category A] [Preadditive A]
  [MonoidalCategory A] [MonoidalPreadditive A]
  [HasWeakSheafify J A] [HasWeakSheafify K A]
  [(J.W (A := A)).IsMonoidal] [(K.W (A := A)).IsMonoidal]
  [(presheafToSheaf J A).Additive] [(presheafToSheaf K A).Additive]
  [HasCoproducts.{0} (Dᵒᵖ ⥤ A)] [HasCoproducts.{0} (Sheaf J A)]

/-- The original canonical comparison commutes with the two native composite
lax chain tensorators. It is a one-way square, not an asserted isomorphism. -/
theorem sheafifyReindexComparison_chainTensor (P Q : ChainComplex (Dᵒᵖ ⥤ A) ℕ) :
    mapChainLaxTensor
        ((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op ⋙ presheafToSheaf J A) P Q ≫
      (NatTrans.mapHomologicalComplex (F.sheafifyReindexComparison J K A) (.down ℕ)).app
        (tensorObj P Q) =
    tensorHom
        ((NatTrans.mapHomologicalComplex (F.sheafifyReindexComparison J K A) (.down ℕ)).app P)
        ((NatTrans.mapHomologicalComplex (F.sheafifyReindexComparison J K A) (.down ℕ)).app Q) ≫
      mapChainLaxTensor (presheafToSheaf K A ⋙ F.sheafPushforwardContinuous A J K) P Q :=
  mapChainLaxTensor_natTrans (F.sheafifyReindexComparison J K A) P Q

end CategoryTheory.Functor
