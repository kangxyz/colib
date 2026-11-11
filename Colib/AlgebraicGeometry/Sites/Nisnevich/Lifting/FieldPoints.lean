/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Nisnevich.Basic
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Actual field-point lifting from the native Nisnevich residue condition

This is the field-point argument of native `Lifting.FiniteSubfamily`, with an
arbitrary presieve in place of an indexed family. The native precoverage is
unchanged: its residue-field isomorphism constructs the literal Spec K lift.
No auxiliary field-lifting topology is defined. Source-only; uncompiled.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Nisnevich

/-- Every original field point lifts along an actual arrow of a Nisnevich presieve. -/
theorem exists_lift_of_field_point {X : Scheme.{u}} {P : Presieve X}
    (hP : P ∈ precoverage X) (K : Type u) [Field K] (a : Spec (.of K) ⟶ X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), P f ∧ ∃ b : Spec (.of K) ⟶ Y, b ≫ f = a := by
  obtain ⟨⟨x, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective a
  obtain ⟨Y, f, hf, y, rfl, hi⟩ := (mem_precoverage_iff.mp hP).2 x
  let := hi
  refine ⟨Y, f, hf, Spec.map (inv (f.residueFieldMap y) ≫ a) ≫
    Y.fromSpecResidueField y, ?_⟩
  change (Spec.map (inv (f.residueFieldMap y) ≫ a) ≫
    Y.fromSpecResidueField y) ≫ f = Spec.map a ≫ X.fromSpecResidueField (f y)
  rw [Category.assoc, ← f.SpecMap_residueFieldMap_fromSpecResidueField y,
    ← Spec.map_comp_assoc]
  simp

end AlgebraicGeometry.Nisnevich
