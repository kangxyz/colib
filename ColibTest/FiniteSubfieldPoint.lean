/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Morphisms.FiniteType.FiniteSubfieldPoint
import Colib.AlgebraicGeometry.Limits.FiniteSubfieldBaseChange

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

/-- The same finite stage contains prescribed scalar parameters and the actual point,
and it is finite étale whenever the original extension is separable. -/
example (K L B : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing B] [Algebra K B] [Algebra.FiniteType K B]
    (ξ : Spec (.of L) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L))) (s : Finset L) :
    ∃ (t : Finset L), s ⊆ t ∧
      Etale (Spec.map (CommRingCat.ofHom
        (algebraMap K (IntermediateField.adjoin K (t : Set L))))) ∧
      IsFinite (Spec.map (CommRingCat.ofHom
        (algebraMap K (IntermediateField.adjoin K (t : Set L))))) ∧
      ∃ ψ : Spec (.of (IntermediateField.adjoin K (t : Set L))) ⟶ Spec (.of B),
        ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
          Spec.map (CommRingCat.ofHom (algebraMap K (IntermediateField.adjoin K (t : Set L)))) ∧
        Spec.map (CommRingCat.ofHom (IntermediateField.adjoin K (t : Set L)).val.toRingHom) ≫ ψ =
          ξ := by
  obtain ⟨t, ht, ψ, hp, hψ⟩ := Scheme.exists_point_finsetSubfield K L B ξ hξ s
  exact ⟨t, ht, etale_finsetSubfieldSpec K L t, isFinite_finsetSubfieldSpec K L t,
    ψ, hp, hψ⟩

/-- Algebraic-closure markings are transported through the actual separable-closure inclusion.
The two fields and their spectra are never identified, and the base field need not be infinite. -/
example (K B : Type u) [Field K] [CommRing B] [Algebra K B] [Algebra.FiniteType K B]
    (ξ : Spec (.of (SeparableClosure K)) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K))))
    (ξbar : Spec (.of (AlgebraicClosure K)) ⟶ Spec (.of B))
    (hmark : Spec.map (CommRingCat.ofHom
        (separableClosure K (AlgebraicClosure K)).val.toRingHom) ≫ ξ = ξbar)
    (s : Finset (SeparableClosure K)) :
    ∃ (t : Finset (SeparableClosure K)), s ⊆ t ∧
      ∃ ψ : Spec (.of (IntermediateField.adjoin K (t : Set (SeparableClosure K)))) ⟶
          Spec (.of B),
        Spec.map (CommRingCat.ofHom (separableClosure K (AlgebraicClosure K)).val.toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (IntermediateField.adjoin K (t : Set (SeparableClosure K))).val.toRingHom) ≫ ψ =
          ξbar := by
  obtain ⟨t, ht, ψ, _, hψ⟩ := Scheme.exists_point_finsetSubfield K (SeparableClosure K) B ξ hξ s
  exact ⟨t, ht, ψ, by rw [hψ]; exact hmark⟩

#print axioms IntermediateField.exists_finsetAdjoin_algHom
#print axioms Scheme.exists_point_finsetSubfield

end
