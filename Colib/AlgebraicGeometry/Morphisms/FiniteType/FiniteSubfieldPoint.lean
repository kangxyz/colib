/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.Separable.FiniteSubfieldFactorization
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Original affine scheme points at actual finite-subfield stages

The spectrum functor's actual preimage recovers the original algebra point. Restricting its
codomain to the generated intermediate field preserves the original base map and gives an
exact factorization of the original scheme morphism, not only its underlying point.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A morphism of affine spectra over the original base is the spectrum of an algebra map. -/
theorem exists_algHom_of_spec_map_over (K L B : Type u) [Field K] [Field L] [Algebra K L]
    [CommRing B] [Algebra K B]
    (ξ : Spec (.of L) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ φ : B →ₐ[K] L, Spec.map (CommRingCat.ofHom φ.toRingHom) = ξ := by
  let f := (Scheme.Spec.preimage ξ).unop.hom
  have hf : Spec.map (CommRingCat.ofHom f) = ξ := Scheme.Spec.map_preimage ξ
  have hscalar : f.comp (algebraMap K B) = algebraMap K L := by
    have hc : CommRingCat.ofHom (f.comp (algebraMap K B)) =
        CommRingCat.ofHom (algebraMap K L) := by
      apply Spec.map_injective
      simpa only [CommRingCat.ofHom_comp, Spec.map_comp, hf] using hξ
    exact congrArg CommRingCat.Hom.hom hc
  exact ⟨{ f with commutes' := fun k => congrArg (fun g : K →+* L => g k) hscalar }, hf⟩

/-- The original extension-field point descends to an actual finitely generated subfield
containing the chosen parameters, preserving both its structure map and exact scheme marking. -/
theorem exists_point_finsetSubfield (K L B : Type u) [Field K] [Field L] [Algebra K L]
    [CommRing B] [Algebra K B] [Algebra.FiniteType K B]
    (ξ : Spec (.of L) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))) (s : Finset L) :
    ∃ (t : Finset L), s ⊆ t ∧ ∃ ψ : Spec (.of (IntermediateField.adjoin K (t : Set L))) ⟶
        Spec (.of B),
      ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
        Spec.map (CommRingCat.ofHom (algebraMap K (IntermediateField.adjoin K (t : Set L)))) ∧
      Spec.map (CommRingCat.ofHom (IntermediateField.adjoin K (t : Set L)).val.toRingHom) ≫ ψ =
        ξ := by
  obtain ⟨φ, hφ⟩ := exists_algHom_of_spec_map_over K L B ξ hξ
  obtain ⟨t, hst, ψ, hψ⟩ := IntermediateField.exists_finsetAdjoin_algHom K L φ s
  refine ⟨t, hst, Spec.map (CommRingCat.ofHom ψ.toRingHom), ?_, ?_⟩
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun f : K →+* IntermediateField.adjoin K (t : Set L) =>
      Spec.map (CommRingCat.ofHom f)) ψ.comp_algebraMap
  · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change Spec.map (CommRingCat.ofHom ((IntermediateField.adjoin K (t : Set L)).val.comp
      ψ).toRingHom) = ξ
    rw [hψ]
    exact hφ
end AlgebraicGeometry.Scheme
