/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Nisnevich.Basic

/-!
# Field-valued criterion for the native Nisnevich site

An etale family is Nisnevich exactly when it jointly lifts all field-valued points.
This extends the actual precoverage, without introducing another field-lifting
precoverage or another residue-field predicate. The fields are in the scheme universe,
so they include every residue field of every object of the site.

Implementation adapted from `Motivic/Aglib/AlgebraicGeometry/Sites/Nisnevich/FieldLifting.lean`
at motivic commit a6805c4a87cdfd7717dd7a94039246a167f15380, lines 58-83.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Nisnevich

set_option backward.isDefEq.respectTransparency false in
/-- Joint lifting of all field-valued points proves the actual Nisnevich cover condition. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Nisnevich/FieldLifting.lean:58-83"
  "adaptation" "Field-valued lifting implies unchanged-residue-field lifts in the native site"]
theorem mem_precoverage_of_field_lifting {X : Scheme.{u}} {R : Presieve X}
    (he : ∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X), R f → Etale f)
    (hl : ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ X),
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X), R f ∧
        ∃ y : Spec (.of K) ⟶ Y, y ≫ f = x) : R ∈ precoverage X := by
  refine ⟨he, fun x ↦ ?_⟩
  obtain ⟨Y, f, hf, g, hgf⟩ := hl (X.residueField x) (X.fromSpecResidueField x)
  obtain ⟨⟨y, b⟩, rfl⟩ := (Scheme.SpecToEquivOfField (X.residueField x) Y).symm.surjective g
  have hy : f y = x := by
    have := congrArg (fun h : Spec (X.residueField x) ⟶ X ↦
      h (IsLocalRing.closedPoint (X.residueField x))) hgf
    change f (Y.fromSpecResidueField y (Spec.map b
      (IsLocalRing.closedPoint (X.residueField x)))) =
      X.fromSpecResidueField x (IsLocalRing.closedPoint (X.residueField x)) at this
    simpa only [Scheme.fromSpecResidueField_apply] using this
  refine ⟨Y, f, hf, y, hy, ?_⟩
  subst x
  have hcomp : f.residueFieldMap y ≫ b = 𝟙 _ := by
    rw [← Spec.map_inj]
    apply (cancel_mono (X.fromSpecResidueField (f y))).mp
    change Spec.map b ≫ Y.fromSpecResidueField y ≫ f = _ at hgf
    rw [Spec.map_comp, Category.assoc,
      f.SpecMap_residueFieldMap_fromSpecResidueField y, Spec.map_id]
    exact hgf.trans (Category.id_comp _).symm
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap y).hom.injective, fun z ↦ ⟨b z, ?_⟩⟩
  apply b.hom.injective
  exact congrArg (fun t : X.residueField (f y) ⟶ X.residueField (f y) ↦ t (b z)) hcomp

/-- The actual cover condition is equivalent to etaleness and field-valued lifting. -/
theorem mem_precoverage_iff_field_lifting {X : Scheme.{u}} {R : Presieve X} :
    R ∈ precoverage X ↔
      (∀ ⦃Y : Scheme.{u}⦄ (f : Y ⟶ X), R f → Etale f) ∧
        ∀ (K : Type u) [Field K] (x : Spec (.of K) ⟶ X),
          ∃ (Y : Scheme.{u}) (f : Y ⟶ X), R f ∧
            ∃ y : Spec (.of K) ⟶ Y, y ≫ f = x :=
  ⟨fun h ↦ ⟨h.1, exists_lift_of_mem_precoverage h⟩,
    fun h ↦ mem_precoverage_of_field_lifting h.1 h.2⟩

end AlgebraicGeometry.Nisnevich
