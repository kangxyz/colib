/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceSimplex

/-! Exact equality transport for dependent common-reference nodes. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor
universe u v w z

namespace CategoryTheory.Waldhausen.IteratedS.ModelSimplex
/-- Transport a reference node along the given comparison isomorphism. -/
def transportedReferenceNode {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {I : Type*} (F₀ : V ⟶ W) (S T : I → (V ⟶ W))
    (ρ : ∀ i, (S i).hom.toFunctor ≅ (T i).hom.toFunctor) (i : I)
    (e : F₀.hom.toFunctor = (S i).hom.toFunctor) :
    Σ F : V ⟶ W, F₀.hom.toFunctor ≅ F.hom.toFunctor := ⟨T i, eqToIso e ≪≫ ρ i⟩

theorem transportedReferenceNode_congr
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {I : Type*} (F₀ : V ⟶ W) (S T : I → (V ⟶ W))
    (ρ : ∀ i, (S i).hom.toFunctor ≅ (T i).hom.toFunctor) {i j : I} (h : i = j)
    (ei : F₀.hom.toFunctor = (S i).hom.toFunctor)
    (ej : F₀.hom.toFunctor = (S j).hom.toFunctor) :
    transportedReferenceNode F₀ S T ρ i ei = transportedReferenceNode F₀ S T ρ j ej := by
  subst j
  rfl

end CategoryTheory.Waldhausen.IteratedS.ModelSimplex

namespace CategoryTheory

/-- Whiskering retains a literal equality transport before the chosen isomorphism. -/
theorem whiskering_eqToIso_trans {A : Type u} {B : Type v} {C : Type w} {D : Type z}
    [Category A] [Category B] [Category C] [Category D]
    (L : A ⥤ B) (R : C ⥤ D) {F G H : B ⥤ C} (e : F = G) (ρ : G ≅ H) :
    isoWhiskerLeft L (isoWhiskerRight (eqToIso e ≪≫ ρ) R) =
      eqToIso (congrArg (fun K ↦ L ⋙ K ⋙ R) e) ≪≫ isoWhiskerLeft L (isoWhiskerRight ρ R) := by
  subst G
  simp

end CategoryTheory
