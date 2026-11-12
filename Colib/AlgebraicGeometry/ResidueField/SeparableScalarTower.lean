/-
Copyright (c) 2026 Colib and AxiomMath/Stacks contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.ResidueField.FieldPoint
public import Mathlib.FieldTheory.SeparableDegree

/-! # Native separable residue fields along a coefficient-field tower

The structural scalar-map identity is the lower-level calculation from pinned
Stacks `EtaleCohomology/Trace/PointwiseMixedBaseField.lean:33-40`, without importing
its trace applications. The residue field and its structural actions are unchanged.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry

/-- Restriction to the ground field composes the actual residue scalar maps. -/
theorem fieldToResidue_scalarTower {K E : Type u} [Field K] [Field E]
    [Algebra K E] {X : Scheme.{u}} (f : X ⟶ Spec (.of E)) (x : X) :
    fieldToResidue (f ≫ Spec.map (CommRingCat.ofHom (algebraMap K E))) x =
      CommRingCat.ofHom (algebraMap K E) ≫ fieldToResidue f x := by
  unfold fieldToResidue fieldToStalk
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  rw [← Category.assoc (Scheme.ΓSpecIso _).inv (Scheme.Hom.appTop (Spec.map _)),
    ← Scheme.ΓSpecIso_inv_naturality]
  simp only [Category.assoc]

/-- Separable coefficient and native residue extensions give the original native
separable residue extension; no alternate scalar action is chosen. -/
theorem isSeparable_residueField_over_subfield {K E : Type u} [Field K] [Field E]
    [Algebra K E] [Algebra.IsSeparable K E] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of E)) (x : X)
    (hs : letI := (fieldToResidue f x).hom.toAlgebra
      Algebra.IsSeparable E (X.residueField x)) :
    letI := (fieldToResidue (f ≫ Spec.map (CommRingCat.ofHom (algebraMap K E))) x).hom.toAlgebra
    Algebra.IsSeparable K (X.residueField x) := by
  let : Algebra E (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  let : Algebra K (X.residueField x) :=
    (fieldToResidue (f ≫ Spec.map (CommRingCat.ofHom (algebraMap K E))) x).hom.toAlgebra
  let : IsScalarTower K E (X.residueField x) := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (fieldToResidue_scalarTower f x))
  let : Algebra.IsSeparable E (X.residueField x) := hs
  exact Algebra.IsSeparable.trans K E (X.residueField x)

end AlgebraicGeometry
