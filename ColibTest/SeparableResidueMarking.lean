/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.ResidueField.SeparableMarking
import Colib.AlgebraicGeometry.Morphisms.FiniteType.FiniteSubfieldPoint
import Colib.FieldTheory.Separable.FiniteSubfields

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme IntermediateField
universe u

/-- The original arbitrary Omega marking survives every finite-parameter descent.
The chosen field L is infinite, but the original field k need not be infinite. -/
example (k Ω B : Type u) [Field k] [Field Ω] [IsSepClosed Ω]
    [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (ξ : Spec (.of Ω) ⟶ Spec (.of B))
    (hs : letI := (fieldToResidue (Spec.map (CommRingCat.ofHom (algebraMap k B)))
      (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable k ((Spec (.of B)).residueField (ξ (IsLocalRing.closedPoint Ω)))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      IsSepClosed L ∧ Infinite L ∧ Algebra.IsSeparable k L ∧
      ∃ e : L →+* Ω, ∀ s : Finset L, ∃ t : Finset L, s ⊆ t ∧
        Module.Finite k (adjoin k (t : Set L)) ∧
        Algebra.IsSeparable k (adjoin k (t : Set L)) ∧
        ∃ ψ : Spec (.of (adjoin k (t : Set L))) ⟶ Spec (.of B),
          ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) =
            Spec.map (CommRingCat.ofHom (algebraMap k (adjoin k (t : Set L)))) ∧
          Spec.map (CommRingCat.ofHom (e.comp (adjoin k (t : Set L)).val.toRingHom)) ≫ ψ =
            ξ := by
  obtain ⟨L, hField, hAlg, hClosed, hInf, hSep, e, x, hx, he⟩ :=
    exists_separable_residue_marking (Spec.map (CommRingCat.ofHom (algebraMap k B))) ξ hs
  let := hField
  let := hAlg
  let := hSep
  refine ⟨L, hField, hAlg, hClosed, hInf, hSep, e, ?_⟩
  intro s
  obtain ⟨t, ht, ψ, hψ, hfac⟩ := exists_point_finsetSubfield k L B x hx s
  refine ⟨t, ht, finite_finsetAdjoinDiagram_obj k L t,
    isSeparable_finsetAdjoinDiagram_obj k L t, ψ, hψ, ?_⟩
  rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hfac, he]
