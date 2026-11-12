/-
Copyright (c) 2026 Colib and AxiomMath/Stacks contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.ResidueField.FieldPoint
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.SeparableDegree
/-! # Étale neighborhoods preserve the original base-field residue separability

All scalar actions are the native maps `fieldToResidue` and `residueFieldMap`.
The structural composition identity is extracted from pinned Stacks
`EtaleCohomology/Trace/FinitePushforwardLFunction.lean:53-59`, without importing
its trace or big-site development. Mathlib supplies separability of the residue
map for a formally unramified, locally finite-type morphism. The actual scalar
compatibility gives the tower used to transport separability over the original
base field; the conclusion is not an additional assumption.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry
/-- The native structural residue-field map composes with the actual residue map. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/FinitePushforwardLFunction.lean:53-59"
  "adaptation" "native structural residue composition without trace dependencies"]
theorem fieldToResidue_comp_native {F : Type u} [Field F] {A X : Scheme.{u}}
    (g : A ⟶ X) (f : X ⟶ Spec (.of F)) (a : A) :
    fieldToResidue (g ≫ f) a = fieldToResidue f (g a) ≫ g.residueFieldMap a := by
  simp only [fieldToResidue, fieldToStalk, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.residue_residueFieldMap]
  congr 2
  exact (g.germ_stalkMap_assoc ⊤ a trivial _).symm

/-- An actual étale neighborhood preserves separability over the original base field. -/
theorem isSeparable_residueField_of_etale_over_field
    {F : Type u} [Field F] {A X : Scheme.{u}}
    (f : X ⟶ Spec (.of F)) (g : A ⟶ X) [Etale g] (a : A)
    (hs : letI := (fieldToResidue f (g a)).hom.toAlgebra
      Algebra.IsSeparable F (X.residueField (g a))) :
    letI := (fieldToResidue (g ≫ f) a).hom.toAlgebra
    Algebra.IsSeparable F (A.residueField a) := by
  let : Algebra F (X.residueField (g a)) := (fieldToResidue f (g a)).hom.toAlgebra
  let : Algebra F (A.residueField a) := (fieldToResidue (g ≫ f) a).hom.toAlgebra
  let : Algebra (X.residueField (g a)) (A.residueField a) :=
    (g.residueFieldMap a).hom.toAlgebra
  let : Algebra.IsSeparable F (X.residueField (g a)) := hs
  have : IsScalarTower F (X.residueField (g a)) (A.residueField a) := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    change (fieldToResidue (g ≫ f) a).hom r = _
    rw [fieldToResidue_comp_native]
    rfl
  let : Algebra.IsSeparable (X.residueField (g a)) (A.residueField a) := inferInstance
  exact Algebra.IsSeparable.trans F (X.residueField (g a)) (A.residueField a)
end AlgebraicGeometry
