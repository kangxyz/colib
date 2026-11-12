/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Presenting the actual finite boundary over an affine base

The original finite scheme is preserved by an actual isomorphism, including its
structural morphism. No reduced boundary or chosen finite set replaces it.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry.Scheme

/-- Every actual finite scheme over `Spec R` is the spectrum of a finite `R`-algebra,
with the exact original structural map retained. -/
theorem exists_finiteAlgebra_presentation
    (R : Type u) [CommRing R] {Z : Scheme.{u}}
    (q : Z ⟶ Spec (.of R)) [IsFinite q] :
    ∃ (C : CommRingCat.{u}) (f : R →+* C) (e : Z ≅ Spec C),
      letI := f.toAlgebra
      Module.Finite R C ∧ e.inv ≫ q = Spec.map (CommRingCat.ofHom f) := by
  let : IsAffine Z := isAffine_of_isAffineHom q
  let e := Z.isoSpec
  obtain ⟨f, hf⟩ := Spec.map_surjective (e.inv ≫ q)
  have hfinite : IsFinite (Spec.map f) := hf.symm ▸ inferInstance
  refine ⟨_, f.hom, e, ?_, ?_⟩
  · exact (IsFinite.SpecMap_iff f).mp hfinite
  · exact hf.symm

end AlgebraicGeometry.Scheme
