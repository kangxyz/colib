/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Type-valued functors with bounded values

Each value embeds in one fixed carrier. Its image, with the original
maps transported through that embedding, is an object of the small
category of subsets of the carrier.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u

namespace CategoryTheory.FunctorToTypes

/-- The small full category with one object for each subset of a fixed type. -/
abbrev SubsetCategory (T : Type w) := InducedCategory (Type w) (fun s : Set T => ↥s)

/-- The actual inclusion of these types into the category of types. -/
abbrev subsetInclusion (T : Type w) : SubsetCategory T ⥤ Type w :=
  inducedFunctor (fun s : Set T => ↥s)

variable {A : Type u} [Category.{v} A] (F : A ⥤ Type w) (κ : Cardinal.{w})
  (h : ∀ a, HasCardinalLT (F.obj a) κ)

/-- The selected embedding of an original value into the bounding carrier. -/
def boundedValueEmbedding (a : A) : F.obj a ↪ κ.ord.ToType := by
  have ha := (hasCardinalLT_iff_cardinal_mk_lt _ κ).1 (h a)
  exact ((Cardinal.le_def _ _).1 (by simpa only [Cardinal.mk_ord_toType] using ha.le)).some

/-- The original value is isomorphic to the image of its chosen embedding. -/
def boundedValueIso (a : A) : F.obj a ≅ ↥(Set.range (boundedValueEmbedding F κ h a)) :=
  (Equiv.ofInjective _ (boundedValueEmbedding F κ h a).injective).toIso

/-- The actual bounded functor represented by subsets of a fixed carrier. -/
def boundedModel : A ⥤ SubsetCategory κ.ord.ToType where
  obj a := Set.range (boundedValueEmbedding F κ h a)
  map {a b} f := InducedCategory.homMk <|
    (boundedValueIso F κ h a).inv ≫ F.map f ≫ (boundedValueIso F κ h b).hom
  map_id a := by
    apply InducedCategory.hom_ext
    let e := boundedValueIso F κ h a
    change e.inv ≫ F.map (𝟙 a) ≫ e.hom = 𝟙 _
    rw [F.map_id, Category.id_comp, e.inv_hom_id]
  map_comp {a b c} f g := by
    apply InducedCategory.hom_ext
    let e₁ := boundedValueIso F κ h a
    let e₂ := boundedValueIso F κ h b
    let e₃ := boundedValueIso F κ h c
    change e₁.inv ≫ F.map (f ≫ g) ≫ e₃.hom =
      (e₁.inv ≫ F.map f ≫ e₂.hom) ≫ e₂.inv ≫ F.map g ≫ e₃.hom
    simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- Each original section is sent to its image in the fixed carrier, and
the original restriction maps are identified by conjugation. -/
def boundedModelIso : F ≅ boundedModel F κ h ⋙ subsetInclusion κ.ord.ToType :=
  NatIso.ofComponents
    (boundedValueIso F κ h)
    (fun {a b} f => by
      let e₁ := boundedValueIso F κ h a
      let e₂ := boundedValueIso F κ h b
      change F.map f ≫ e₂.hom = e₁.hom ≫ e₁.inv ≫ F.map f ≫ e₂.hom
      rw [e₁.hom_inv_id_assoc])

end CategoryTheory.FunctorToTypes
