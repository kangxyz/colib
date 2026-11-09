/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenComparison
public import Colib.RingTheory.KTheory.MilnorK.Norm.FieldPresentation
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

/-!
# Transitivity and algebra-equivalence naturality of the native finite Milnor norm

The original recursive chosen norm is transitive in finite characteristic-zero
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
theorem milnorKNormRing_map_algEquiv
    {k L M : Type u} [Field k] [Field L] [Field M] [CharZero k]
    [Algebra k L] [Algebra k M] [FiniteDimensional k L] [FiniteDimensional k M]
    (f : L ≃ₐ[k] M) (x : MilnorKRing L) :
    milnorKNormRing k M (milnorKRingMap f.toRingHom x) = milnorKNormRing k L x := by
  obtain ⟨d, p, ⟨ε⟩⟩ := exists_monicIrreducible_presentation k L
  let η : M ≃ₐ[k] AdjoinRoot (poly p) := f.symm.trans ε
  have hcomp : η.toRingHom.comp f.toRingHom = ε.toRingHom := by
    ext a
    change ε (f.symm (f a)) = ε a
    rw [f.symm_apply_apply]
  rw [milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv p η,
    milnorKRingMap_comp_apply, hcomp,
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv p ε]

/-- Actual algebra-equivalence naturality for the original additive norm maps. -/
theorem milnorKNormRing_comp_map_algEquiv
    {k L M : Type u} [Field k] [Field L] [Field M] [CharZero k]
    [Algebra k L] [Algebra k M] [FiniteDimensional k L] [FiniteDimensional k M] (f : L ≃ₐ[k] M) :
    (milnorKNormRing k M).comp (milnorKRingMap f.toRingHom).toAddMonoidHom =
      milnorKNormRing k L := by
  ext x
  exact milnorKNormRing_map_algEquiv f x

/-- Actual algebra-equivalence naturality in every homogeneous degree. -/
theorem milnorKNorm_map_algEquiv
    {k L M : Type u} [Field k] [Field L] [Field M] [CharZero k]
    [Algebra k L] [Algebra k M] [FiniteDimensional k L] [FiniteDimensional k M]
    (f : L ≃ₐ[k] M) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm k M n (milnorKTheoryMap f.toRingHom n x) = milnorKNorm k L n x := by
  rw [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  exact milnorKNormRing_map_algEquiv f (x : MilnorKRing L)

end Equivariance

section Tower

/-- The original recursive chosen norms compose in every finite characteristic-zero tower. -/
theorem milnorKNormRing_tower
    {k M L : Type u} [Field k] [Field M] [Field L] [CharZero k]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] (x : MilnorKRing L) :
    milnorKNormRing k M (milnorKNormRing M L x) = milnorKNormRing k L x := by
  let hCharZero : CharZero M := Algebra.charZero_of_charZero k M
  obtain ⟨d, p, ⟨ε⟩⟩ := exists_monicIrreducible_presentation k M
  obtain ⟨e, h, ⟨η⟩⟩ := exists_monicIrreducible_presentation k L
  obtain ⟨rDegree, r, g, hnorm⟩ :=
    exists_simpleMilnorNorm_tower_presentation p h ε η
  rw [milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv p ε,
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv r g,
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv h η]
  exact hnorm x

/-- Transitivity as equality of the original whole-ring additive norm maps. -/
theorem milnorKNormRing_comp_milnorKNormRing
    {k M L : Type u} [Field k] [Field M] [Field L] [CharZero k]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] :
    (milnorKNormRing k M).comp (milnorKNormRing M L) = milnorKNormRing k L := by
  ext x
  exact milnorKNormRing_tower x

/-- The native norm is transitive on every homogeneous Milnor group. -/
theorem milnorKNorm_tower
    {k M L : Type u} [Field k] [Field M] [Field L] [CharZero k]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L]
    (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNorm k M n (milnorKNorm M L n x) = milnorKNorm k L n x := by
  apply Subtype.ext
  exact milnorKNormRing_tower (x : MilnorKRing L)

/-- Transitivity as equality of the original homogeneous additive norm maps. -/
theorem milnorKNorm_comp_milnorKNorm
    {k M L : Type u} [Field k] [Field M] [Field L] [CharZero k]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L] (n : ℕ) :
    (milnorKNorm k M n).comp (milnorKNorm M L n) = milnorKNorm k L n := by
  apply AddMonoidHom.ext
  intro x
  exact milnorKNorm_tower n x

end Tower

end Stacks.Chow

end
