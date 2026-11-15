/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SmoothClosedImmersionCoordinates

/-!
# Étale coordinate charts for smooth closed pairs

The coordinate chart of a smooth closed immersion is cartesian, and both
horizontal maps are étale over the original base. This form retains the
actual restricted immersion and the base equation for the closed subscheme.
It is the geometric input for the common étale neighborhoods used in purity.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Stacks.AlgebraicGeometry

/-- A smooth closed pair admits a cartesian étale coordinate chart over the base,
with both horizontal arrows étale and the original maps on the closed subscheme. -/
theorem exists_etale_coordinateSubspaceEmbedding_isPullback_over
    {S X Z : Scheme.{u}} (p : X ⟶ S) (i : Z ⟶ X)
    [IsClosedImmersion i] [Smooth p] [Smooth (i ≫ p)] (z : Z) :
    ∃ (m n : ℕ) (U : X.Opens) (_ : z ∈ i ⁻¹ᵁ U)
      (a : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin (m + n))) S)
      (b : (i ⁻¹ᵁ U).toScheme ⟶ AffineSpace (ULift.{u} (Fin m)) S),
      Etale a ∧ Etale b ∧
        a ≫ (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom = U.ι ≫ p ∧
        b ≫ (AffineSpace.over (ULift.{u} (Fin m)) S).hom =
          (i ⁻¹ᵁ U).ι ≫ i ≫ p ∧
        IsPullback (i.resLE U (i ⁻¹ᵁ U) le_rfl) b a
          (coordinateSubspaceEmbedding S m n) := by
  obtain ⟨m, n, U, hz, a, b, ha, hover, hpb⟩ :=
    exists_etale_coordinateSubspaceEmbedding_isPullback p i z
  have hb : Etale b := MorphismProperty.of_isPullback hpb ha
  refine ⟨m, n, U, hz, a, b, ha, hb, hover, ?_, hpb⟩
  have hcoord : coordinateSubspaceEmbedding S m n ≫
      (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom =
      (AffineSpace.over (ULift.{u} (Fin m)) S).hom :=
    AffineSpace.homOfVector_over _ _
  calc
    b ≫ (AffineSpace.over (ULift.{u} (Fin m)) S).hom =
        b ≫ coordinateSubspaceEmbedding S m n ≫
          (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom := by rw [hcoord]
    _ = (i.resLE U (i ⁻¹ᵁ U) le_rfl) ≫ a ≫
          (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom := by
      rw [← Category.assoc, ← hpb.w, Category.assoc]
    _ = (i ⁻¹ᵁ U).ι ≫ i ≫ p := by
      rw [hover, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]

end Stacks.AlgebraicGeometry

end
