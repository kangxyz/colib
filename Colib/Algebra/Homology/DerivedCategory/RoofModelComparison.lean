/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # A chain-map roof equation is independent of the derived-category model -/

@[expose] public noncomputable section

open CategoryTheory

namespace DerivedCategory

universe u v w₁ w₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (h₁ : HasDerivedCategory.{w₁} C) (h₂ : HasDerivedCategory.{w₂} C)

local notation "Q₁" => (@DerivedCategory.Q C _ _ h₁)
local notation "Q₂" => (@DerivedCategory.Q C _ _ h₂)
local notation "W" => (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))

/-- The same actual chain maps satisfy the roof equation in any chosen derived-category model,
with the specified derived morphism transported through the canonical localization comparison. -/
theorem comp_eq_iff_of_model {R K E : CochainComplex C ℤ}
    (q : R ⟶ K) (a : R ⟶ E) (α : (Q₁).obj K ⟶ (Q₁).obj E) :
    (Q₁).map q ≫ α = (Q₁).map a ↔
      (Q₂).map q ≫ (Localization.compUniqFunctor Q₁ Q₂ W).inv.app K ≫
        (Localization.uniq Q₁ Q₂ W).functor.map α ≫
          (Localization.compUniqFunctor Q₁ Q₂ W).hom.app E = (Q₂).map a := by
  let F := (Localization.uniq Q₁ Q₂ W).functor
  let e := Localization.compUniqFunctor Q₁ Q₂ W
  let α' := e.inv.app K ≫ F.map α ≫ e.hom.app E
  have hq : F.map ((Q₁).map q) = e.hom.app R ≫ (Q₂).map q ≫ e.inv.app K := by
    apply (cancel_mono (e.hom.app K)).1
    simpa only [F, Functor.comp_map, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using
      e.hom.naturality q
  have ha : F.map ((Q₁).map a) = e.hom.app R ≫ (Q₂).map a ≫ e.inv.app E := by
    apply (cancel_mono (e.hom.app E)).1
    simpa only [F, Functor.comp_map, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using
      e.hom.naturality a
  have hα : e.hom.app R ≫ ((Q₂).map q ≫ α') ≫ e.inv.app E = F.map ((Q₁).map q ≫ α) := by
    rw [F.map_comp, hq]
    simp only [α', F, Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app,
      Category.comp_id]
  change (Q₁).map q ≫ α = (Q₁).map a ↔ (Q₂).map q ≫ α' = (Q₂).map a
  constructor
  · intro h
    apply (cancel_epi (e.hom.app R)).1
    apply (cancel_mono (e.inv.app E)).1
    simpa only [Category.assoc] using hα.trans ((congrArg F.map h).trans ha)
  · intro h
    apply F.map_injective
    rw [← hα, h, ha]

end DerivedCategory
