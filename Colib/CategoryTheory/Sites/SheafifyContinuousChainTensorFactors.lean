/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.Sites.SheafifyContinuousMonoidal
public import Colib.Algebra.Homology.MapChainLaxTensorComp
public import Colib.CategoryTheory.Sites.SheafifyContinuousChainTensor
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
  [HasCoproducts.{0} (Dᵒᵖ ⥤ A)] [HasCoproducts.{0} (Cᵒᵖ ⥤ A)]
  [HasCoproducts.{0} (Sheaf J A)] [HasCoproducts.{0} (Sheaf K A)]

/-- The canonical chain comparison square with both composite tensorators
factored into their original sheafification and reindexing comparisons. -/
theorem sheafifyReindexComparison_chainTensor_factors (P Q : ChainComplex (Dᵒᵖ ⥤ A) ℕ) :
    let R := (whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj F.op
    let SJ := presheafToSheaf J A
    let SK := presheafToSheaf K A
    let RS := F.sheafPushforwardContinuous A J K
    let γ := NatTrans.mapHomologicalComplex (F.sheafifyReindexComparison J K A) (.down ℕ)
    SJ.mapChainLaxTensor ((R.mapHomologicalComplex (.down ℕ)).obj P)
        ((R.mapHomologicalComplex (.down ℕ)).obj Q) ≫
      (SJ.mapHomologicalComplex (.down ℕ)).map (R.mapChainLaxTensor P Q) ≫
      γ.app (tensorObj P Q) =
    tensorHom (γ.app P) (γ.app Q) ≫
      RS.mapChainLaxTensor ((SK.mapHomologicalComplex (.down ℕ)).obj P)
        ((SK.mapHomologicalComplex (.down ℕ)).obj Q) ≫
      (RS.mapHomologicalComplex (.down ℕ)).map (SK.mapChainLaxTensor P Q) := by
  simpa only [mapChainLaxTensor_comp, Category.assoc] using
    F.sheafifyReindexComparison_chainTensor J K A P Q

end CategoryTheory.Functor
