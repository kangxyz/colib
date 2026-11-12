/-
Copyright (c) 2026 Colib contributors and AxiomMath/Stacks contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Local fixed relative dimension for an actual smooth morphism

This lower interface extracts the native standard-smooth proof of
`Smooth.exists_smoothOfRelativeDimension_nbhd` from
StacksFrontier/AlgebraicGeometry/Crystalline/FrobeniusAlphaPCoverSmooth.lean at the pinned
Stacks revision 5ed82d14634e8d9576bb844c7bd4e3da66d450e7. It avoids importing the unrelated
crystalline site and de Rham constructions above that elementary lemma. The original open
subscheme, its inclusion and its composed structure morphism are retained.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Every point has an original open neighborhood on which the smooth structure morphism has
some fixed relative dimension. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Crystalline/FrobeniusAlphaPCoverSmooth.lean:64-85"
  "adaptation" "lower-interface extraction of Smooth.exists_smoothOfRelativeDimension_nbhd"]
theorem Smooth.exists_relativeDimension_neighborhood {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ ∃ n : ℕ, SmoothOfRelativeDimension n (V.ι ≫ f) := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := Smooth.exists_isStandardSmooth f x
  obtain ⟨n, hn⟩ : ∃ n, (f.appLE U V e).hom.IsStandardSmoothOfRelativeDimension n := by
    let := (f.appLE U V e).hom.toAlgebra
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := hf.toAlgebra.out
    exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp
      (HasRingHomProperty.isLocal_ringHomProperty (@SmoothOfRelativeDimension n)).respectsIso
  have h : SmoothOfRelativeDimension n (f.resLE U V e) := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension n)]
    exact (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty
      (RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)))
      (arrowResLEAppIso f U V e)).mpr
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hn)
  refine ⟨V, hx, n, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  exact inferInstanceAs (SmoothOfRelativeDimension (n + 0) _)

end AlgebraicGeometry
