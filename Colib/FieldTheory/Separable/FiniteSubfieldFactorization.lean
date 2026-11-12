/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.FiniteType

/-!
# Exact finite-subfield factorization of finite-type algebra points

Finite generators of the source and a prescribed finite parameter set determine an actual
intermediate field. The factor map composes with its original inclusion to the original point.
No assumption that the base field is infinite is used. Finiteness and separability of these
stages in a separable algebraic extension are supplied by `FiniteSubfields`.
-/

@[expose] public noncomputable section

universe u

namespace IntermediateField
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
/-- A finite-type algebra point factors through an actual finitely generated intermediate field
containing any prescribed finite set of scalar parameters. -/
theorem exists_finsetAdjoin_algHom {B : Type u} [CommRing B] [Algebra K B] [Algebra.FiniteType K B]
    (φ : B →ₐ[K] L) (s : Finset L) :
    ∃ (t : Finset L), s ⊆ t ∧ ∃ ψ : B →ₐ[K] adjoin K (t : Set L),
      (adjoin K (t : Set L)).val.comp ψ = φ := by
  classical
  obtain ⟨g, hg⟩ := Algebra.FiniteType.out (R := K) (A := B)
  let t := s ∪ g.image φ
  have h : Algebra.adjoin K (g : Set B) ≤ ((adjoin K (t : Set L)).toSubalgebra).comap φ := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    exact subset_adjoin K _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
  have hφ (x : B) : φ x ∈ adjoin K (t : Set L) :=
    h (hg.symm ▸ (show x ∈ (⊤ : Subalgebra K B) from trivial))
  exact ⟨t, Finset.subset_union_left, φ.codRestrict _ hφ, rfl⟩
end IntermediateField
