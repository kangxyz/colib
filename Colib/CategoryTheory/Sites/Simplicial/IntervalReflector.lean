/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.IntervalLocalHom
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Reflection into interval-local objects

If each object of the chosen interval localization has an interval-local
stalkwise model, the original localization functor has a fully faithful
right adjoint. Its adjunction is given by the original localization map
on morphisms into these models.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (I : Cᵒᵖ ⥤ SSet.{w})

local notation "L" => stalkwiseToIntervalHomotopyCategory C J I

variable (h : ∀ Y : IntervalHomotopyCategory C J I,
  ∃ X : StalkwiseHomotopyCategory.{w} C J,
    IsIntervalLocal C J I X ∧ Nonempty ((stalkwiseToIntervalHomotopyCategory C J I).obj X ≅ Y))

private def intervalLocalModel (Y : IntervalHomotopyCategory C J I) :=
  (h Y).choose

private theorem intervalLocalModel_isIntervalLocal (Y : IntervalHomotopyCategory C J I) :
    IsIntervalLocal C J I (intervalLocalModel J I h Y) :=
  (h Y).choose_spec.1

private def intervalLocalModelIso (Y : IntervalHomotopyCategory C J I) :
    (L).obj (intervalLocalModel J I h Y) ≅ Y :=
  (h Y).choose_spec.2.some

private def intervalReflectorHomEquiv (X : StalkwiseHomotopyCategory.{w} C J)
    (Y : IntervalHomotopyCategory C J I) : ((L).obj X ⟶ Y) ≃ (X ⟶ intervalLocalModel J I h Y) :=
  (intervalLocalModelIso J I h Y).symm.homToEquiv.trans
    (stalkwiseIntervalLocalHomEquiv C J I _ (intervalLocalModel_isIntervalLocal J I h Y) X)

private theorem intervalReflectorHomEquiv_naturality
    (X' X : StalkwiseHomotopyCategory.{w} C J) (Y : IntervalHomotopyCategory C J I)
    (f : X' ⟶ X) (g : (L).obj X ⟶ Y) :
    intervalReflectorHomEquiv J I h X' Y ((L).map f ≫ g) =
      f ≫ intervalReflectorHomEquiv J I h X Y g := by
  let e := intervalLocalModelIso J I h Y
  let hY := intervalLocalModel_isIntervalLocal J I h Y
  change stalkwiseIntervalLocalHomEquiv C J I _ hY X' (((L).map f ≫ g) ≫ e.inv) =
    f ≫ stalkwiseIntervalLocalHomEquiv C J I _ hY X (g ≫ e.inv)
  rw [Category.assoc]
  exact stalkwiseIntervalLocalHomEquiv_naturality C J I _ hY f (g ≫ e.inv)

/-- The inclusion of the chosen interval localization into the stalkwise category. -/
@[no_expose]
def intervalLocalInclusion :
    IntervalHomotopyCategory C J I ⥤ StalkwiseHomotopyCategory.{w} C J :=
  Adjunction.rightAdjointOfEquiv (intervalReflectorHomEquiv J I h)
    (intervalReflectorHomEquiv_naturality J I h)

/-- The original intermediate localization is left adjoint to its local inclusion. -/
@[no_expose]
def intervalReflectorAdjunction : (L) ⊣ intervalLocalInclusion J I h :=
  Adjunction.adjunctionOfEquivRight (intervalReflectorHomEquiv J I h)
    (intervalReflectorHomEquiv_naturality J I h)

theorem isIntervalLocal_intervalLocalInclusion_obj (Y : IntervalHomotopyCategory C J I) :
    IsIntervalLocal C J I ((intervalLocalInclusion J I h).obj Y) :=
  intervalLocalModel_isIntervalLocal J I h Y

/-- The counit component is the chosen isomorphism from the original
localization of the local model to its represented interval object. -/
instance (Y : IntervalHomotopyCategory C J I) :
    IsIso ((intervalReflectorAdjunction J I h).counit.app Y) := by
  have hc : (intervalReflectorAdjunction J I h).counit.app Y =
      (intervalLocalModelIso J I h Y).hom := by
    change (intervalReflectorHomEquiv J I h _ Y).symm (𝟙 _) =
      (intervalLocalModelIso J I h Y).hom
    simp [intervalReflectorHomEquiv]
  rw [hc]
  exact (intervalLocalModelIso J I h Y).isIso_hom

instance : IsIso (intervalReflectorAdjunction J I h).counit :=
  NatIso.isIso_of_isIso_app _

/-- The right adjoint identifies the interval homotopy category with its
full subcategory of local objects in the stalkwise homotopy category. -/
@[no_expose]
def intervalLocalInclusionFullyFaithful : (intervalLocalInclusion J I h).FullyFaithful :=
  (intervalReflectorAdjunction J I h).fullyFaithfulROfIsIsoCounit

/-- Reflecting an already local stalkwise object gives an isomorphism on that object. -/
theorem isIso_intervalReflectorAdjunction_unit_app
    (X : StalkwiseHomotopyCategory.{w} C J) (hX : IsIntervalLocal C J I X) :
    IsIso ((intervalReflectorAdjunction J I h).unit.app X) := by
  let adj := intervalReflectorAdjunction J I h
  apply isIso_of_yoneda_map_bijective
  intro T
  have he : (fun f : T ⟶ X ↦ f ≫ adj.unit.app X) =
      fun f : T ⟶ X ↦ adj.homEquiv T ((L).obj X) ((L).map f) := by
    funext f
    exact ((adj.homEquiv_unit (f := (L).map f)).trans
      (adj.unit_naturality f)).symm
  change Function.Bijective (fun f : T ⟶ X ↦ f ≫ adj.unit.app X)
  rw [he]
  exact (adj.homEquiv T ((L).obj X)).bijective.comp
    (stalkwiseToIntervalHomotopyCategory_map_bijective C J I X hX T)

end CategoryTheory.PointedSimplicialPresheaf
