/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AlgebraicSimplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Cartesian coefficient change for barycentric coordinate rings

The square formed by the actual coefficient and barycentric homomorphisms is
an honest categorical pushout for every commutative-ring homomorphism.
No flatness, injectivity, field or finite-type assumption is required.

Adapted from the ring-theoretic part of the separate motivic repository's
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Simplex/BaseChange.lean:37-79`
at revision a6805c4a87cdfd7717dd7a94039246a167f15380. This lower result does not
import schemes or assert a comparison for a replacement coordinate model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicSimplex

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The coefficient square retains the actual constant and barycentric maps. -/
theorem mapCoefficients_square (c : R →+* S) (n : ℕ) :
    CommRingCat.ofHom c ≫ CommRingCat.ofHom (constant S n) =
      CommRingCat.ofHom (constant R n) ≫ CommRingCat.ofHom (mapCoefficients c n) := by
  apply CommRingCat.hom_ext
  exact RingHom.ext (fun r => (mapCoefficients_constant c n r).symm)

/-- The literal barycentric coefficient square is a pushout for any ring map. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Simplex/BaseChange.lean:37-79"
  "adaptation" "The exact barycentric coefficient square is a pushout for every ring map"]
theorem mapCoefficients_isPushout (c : R →+* S) (n : ℕ) :
    IsPushout (CommRingCat.ofHom c) (CommRingCat.ofHom (constant R n))
      (CommRingCat.ofHom (constant S n)) (CommRingCat.ofHom (mapCoefficients c n)) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (mapCoefficients_square c n))
  apply PushoutCocone.isColimitAux'
  intro s
  have hx : ∑ i, s.inr (coordinate R n i) = 1 := by
    rw [← map_sum, sum_coordinate, map_one]
  let d : CommRingCat.of (CoordinateRing S n) ⟶ s.pt :=
    CommRingCat.ofHom (lift s.inl.hom (fun i => s.inr (coordinate R n i)) hx)
  refine ⟨d, ?_, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    exact RingHom.ext (fun r => lift_constant _ _ hx r)
  · apply CommRingCat.hom_ext
    apply ringHom_ext
    · intro r
      change lift _ _ hx (mapCoefficients c n (constant R n r)) = _
      rw [mapCoefficients_constant, lift_constant]
      exact congrArg (fun f => f r) s.condition
    · intro i
      change lift _ _ hx (mapCoefficients c n (coordinate R n i)) = _
      rw [mapCoefficients_coordinate, lift_coordinate]
  · intro h hl hr
    apply CommRingCat.hom_ext
    apply ringHom_ext
    · intro r
      change h (constant S n r) = lift _ _ hx (constant S n r)
      rw [lift_constant]
      exact congrArg (fun f => f r) hl
    · intro i
      change h (coordinate S n i) = lift _ _ hx (coordinate S n i)
      rw [lift_coordinate]
      have hi := congrArg (fun f => f (coordinate R n i)) hr
      change h (mapCoefficients c n (coordinate R n i)) = _ at hi
      rwa [mapCoefficients_coordinate] at hi

end AlgebraicSimplex
