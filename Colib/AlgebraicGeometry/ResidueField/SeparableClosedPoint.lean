/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.ResidueField.FieldPoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FunctionFieldEssFiniteType
public import Mathlib.RingTheory.Unramified.Field

/-! # A separable actual residue field gives a closed point

For a separated scheme locally of finite type over a field, separability of the
native residue extension already gives finiteness and closedness. In particular
one need not add closedness as a new hypothesis after changing the coefficient field.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry

/-- A separable native residue extension is finite at a locally finite-type point. -/
theorem finite_residueField_overField_of_isSeparable
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x : X)
    (hs : letI := (fieldToResidue f x).hom.toAlgebra
      Algebra.IsSeparable k (X.residueField x)) :
    letI := (fieldToResidue f x).hom.toAlgebra
    Module.Finite k (X.residueField x) := by
  let := (fieldToResidue f x).hom.toAlgebra
  let : Algebra.IsSeparable k (X.residueField x) := hs
  let : Algebra.EssFiniteType k (X.residueField x) := essFiniteType_residueField (.of k) f x
  let : Algebra.FormallyUnramified k (X.residueField x) :=
    Algebra.FormallyUnramified.of_isSeparable k (X.residueField x)
  exact Algebra.FormallyUnramified.finite_of_free k (X.residueField x)

/-- Closedness is a consequence of the actual separable residue condition. -/
theorem isClosed_of_isSeparable_residueField
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IsSeparated f] (x : X)
    (hs : letI := (fieldToResidue f x).hom.toAlgebra
      Algebra.IsSeparable k (X.residueField x)) : IsClosed ({x} : Set X) := by
  let := (fieldToResidue f x).hom.toAlgebra
  let : Module.Finite k (X.residueField x) := finite_residueField_overField_of_isSeparable f x hs
  have h := isClosed_image_of_finite_fieldPoint (k := k) (K := X.residueField x)
    f (X.fromSpecResidueField x)
    (Scheme.fromSpecResidueField_comp_eq_spec_fieldToResidue f x)
  exact (congrArg (fun y : X => IsClosed ({y} : Set X))
    (X.fromSpecResidueField_apply x (IsLocalRing.closedPoint (X.residueField x)))).mp h

end AlgebraicGeometry
