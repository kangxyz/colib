/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenComparisonSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.FieldPresentation
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

/-!
# Transitivity and algebra-equivalence naturality of the native finite Milnor norm

The original recursive chosen norm is transitive in finite separable
towers with their original scalar actions. Choose actual presentations only for
the lower and total extensions; the upper presentation is the constructed
canonical factor pulled back to the original intermediate field. The chosen
comparison and the unrestricted simple tower prove the equation.

The proof does not import polynomial presentation independence. All fields are
in the same universe, as required by the native chosen-norm API. The endpoints
include the original additive maps and every homogeneous Milnor group.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

section Equivariance

/-- The original chosen norm is unchanged under an actual base-algebra equivalence. -/
theorem milnorKNormRing_map_algEquiv_of_isSeparable
    {k L M : Type u} [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra.IsSeparable k L]
    [FiniteDimensional k L] [FiniteDimensional k M]
    (f : L ≃ₐ[k] M) (x : MilnorKRing L) :
    milnorKNormRing k M (milnorKRingMap f.toRingHom x) = milnorKNormRing k L x := by
  let : Algebra.IsSeparable k M := AlgEquiv.Algebra.isSeparable f
  obtain ⟨d, p, ⟨ε⟩⟩ := exists_monicIrreducible_presentation k L
  let η : M ≃ₐ[k] AdjoinRoot (poly p) := f.symm.trans ε
  have hcomp : η.toRingHom.comp f.toRingHom = ε.toRingHom := by
    ext a
    change ε (f.symm (f a)) = ε a
    rw [f.symm_apply_apply]
  rw [milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable p η,
    milnorKRingMap_comp_apply, hcomp,
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable p ε]

/-- Actual algebra-equivalence naturality for the original additive norm maps. -/
theorem milnorKNormRing_comp_map_algEquiv_of_isSeparable
    {k L M : Type u} [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra.IsSeparable k L]
    [FiniteDimensional k L] [FiniteDimensional k M] (f : L ≃ₐ[k] M) :
    (milnorKNormRing k M).comp (milnorKRingMap f.toRingHom).toAddMonoidHom =
      milnorKNormRing k L := by
  ext x
  exact milnorKNormRing_map_algEquiv_of_isSeparable f x

/-- Actual algebra-equivalence naturality in every homogeneous degree. -/
theorem milnorKNorm_map_algEquiv_of_isSeparable
    {k L M : Type u} [Field k] [Field L] [Field M]
    [Algebra k L] [Algebra k M] [Algebra.IsSeparable k L]
    [FiniteDimensional k L] [FiniteDimensional k M]
    (f : L ≃ₐ[k] M) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm k M n (milnorKTheoryMap f.toRingHom n x) = milnorKNorm k L n x := by
  rw [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  exact milnorKNormRing_map_algEquiv_of_isSeparable f (x : MilnorKRing L)

end Equivariance

section Tower

/-- The original recursive chosen norms compose in every finite separable tower. -/
theorem milnorKNormRing_tower_of_isSeparable
    {k M L : Type u} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [Algebra.IsSeparable k L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] (x : MilnorKRing L) :
    milnorKNormRing k M (milnorKNormRing M L x) = milnorKNormRing k L x := by
  let : Algebra.IsSeparable k M := Algebra.isSeparable_tower_bot_of_isSeparable k M L
  let : Algebra.IsSeparable M L := Algebra.isSeparable_tower_top_of_isSeparable k M L
  obtain ⟨d, p, ⟨ε⟩⟩ := exists_monicIrreducible_presentation k M
  obtain ⟨e, h, ⟨η⟩⟩ := exists_monicIrreducible_presentation k L
  obtain ⟨rDegree, r, g, hnorm⟩ :=
    exists_simpleMilnorNorm_tower_presentation_of_isSeparable p h ε η
  rw [milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable p ε,
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable r g,
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable h η]
  exact hnorm x

/-- Transitivity as equality of the original whole-ring additive norm maps. -/
theorem milnorKNormRing_comp_milnorKNormRing_of_isSeparable
    {k M L : Type u} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [Algebra.IsSeparable k L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] :
    (milnorKNormRing k M).comp (milnorKNormRing M L) = milnorKNormRing k L := by
  ext x
  exact milnorKNormRing_tower_of_isSeparable x

/-- The native norm is transitive on every homogeneous Milnor group. -/
theorem milnorKNorm_tower_of_isSeparable
    {k M L : Type u} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [Algebra.IsSeparable k L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L]
    (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm k M n (milnorKNorm M L n x) = milnorKNorm k L n x := by
  apply Subtype.ext
  exact milnorKNormRing_tower_of_isSeparable (x : MilnorKRing L)

/-- Transitivity as equality of the original homogeneous additive norm maps. -/
theorem milnorKNorm_comp_milnorKNorm_of_isSeparable
    {k M L : Type u} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [Algebra.IsSeparable k L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] (n : ℕ) :
    (milnorKNorm k M n).comp (milnorKNorm M L n) = milnorKNorm k L n := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKNorm_tower_of_isSeparable n x

end Tower

attribute [colib_tag "COL-0396",
  colib_ref "aglib_milnor_norm_52e09db4"
    "Aglib/KTheory/MilnorK/Norm/FiniteExtension/Basic.lean:26-80" "adaptation"
    "Presentation comparison: the source uses its own characteristic-zero norm; this proves \
      finite separable comparison for the original recursive Stacks norm, not equality with \
      the Aglib model",
  colib_ref "axiom_stacks_milnor_norm_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/Chow/MilnorNorm/SimpleNorm.lean:176-206" "ingredient"
    "The unchanged simple norm is negative infinity residue on a single-residue lift and \
      preserves the grading; this source does not prove chosen-norm presentation \
      independence"]
  milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable
  milnorKNormRing_eq_comp_simpleMilnorNorm_of_algEquiv_of_isSeparable
  coe_milnorKNorm_eq_simpleMilnorNorm_of_algEquiv_of_isSeparable
  milnorKNormRing_eq_simpleMilnorNorm_of_isSeparable

attribute [colib_tag "COL-0396",
  colib_ref "aglib_milnor_norm_52e09db4"
    "Aglib/KTheory/MilnorK/Norm/FiniteExtension/Equiv.lean:104-113" "adaptation"
    "Upper-field algebra-equivalence naturality: the source assumes characteristic zero in \
      its own model; this is the finite separable result for the original Stacks norm"]
  milnorKNormRing_map_algEquiv_of_isSeparable
  milnorKNormRing_comp_map_algEquiv_of_isSeparable
  milnorKNorm_map_algEquiv_of_isSeparable

attribute [colib_tag "COL-0396",
  colib_ref "aglib_milnor_norm_52e09db4"
    "Aglib/KTheory/MilnorK/Norm/FiniteExtension/Tower.lean:146-183" "adaptation"
    "The source proves characteristic-zero transitivity for its finiteExtensionNorm; this \
      proves the same tower equation for the original Stacks norm in finite separable scope, \
      with the original scalar actions and all natural degrees"]
  milnorKNormRing_tower_of_isSeparable
  milnorKNormRing_comp_milnorKNormRing_of_isSeparable
  milnorKNorm_tower_of_isSeparable
  milnorKNorm_comp_milnorKNorm_of_isSeparable

attribute [stacks 0EAY
  "Background on the Milnor groups, tame residues and norm maps only; not the chosen-norm \
    presentation, naturality or tower theorem"]
  milnorKNorm_comp_milnorKNorm_of_isSeparable

end Stacks.Chow

end
