/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AlgebraicSimplex.CoefficientPushout
public import Colib.AlgebraicGeometry.Simplex.AlgebraicSimplexScheme
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual coefficient-change squares of algebraic simplices

The original coefficient map and structure map exhibit the simplex after any
commutative-ring homomorphism as the scheme-theoretic pullback of the original
simplex. This applies to non-flat maps, including reduction modulo a composite.
The two projections are the literal maps of the barycentric quotient, not maps
transported from a different affine-space model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicSimplex

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Applying spectrum gives the original coefficient-change Cartesian square. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Simplex/BaseChange.lean:81-85"
  "adaptation" "The literal coefficient-change square is Cartesian in every degree"]
theorem mapCoefficients_isPullback (c : R →+* S) (n : ℕ) :
    IsPullback (Spec.map (CommRingCat.ofHom (mapCoefficients c n)))
      (structureMap S n) (structureMap R n) (Spec.map (CommRingCat.ofHom c)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (mapCoefficients_isPushout c n)).flip

/-- The actual simplex over the new ring identifies with the chosen scheme pullback. -/
def coefficientPullbackIso (c : R →+* S) (n : ℕ) :
    Spec (.of (CoordinateRing S n)) ≅
      CategoryTheory.Limits.pullback (structureMap R n) (Spec.map (CommRingCat.ofHom c)) :=
  (mapCoefficients_isPullback c n).isoPullback

@[reassoc (attr := simp)]
theorem coefficientPullbackIso_hom_fst (c : R →+* S) (n : ℕ) :
    (coefficientPullbackIso c n).hom ≫
      pullback.fst (structureMap R n) (Spec.map (CommRingCat.ofHom c)) =
        Spec.map (CommRingCat.ofHom (mapCoefficients c n)) :=
  (mapCoefficients_isPullback c n).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem coefficientPullbackIso_hom_snd (c : R →+* S) (n : ℕ) :
    (coefficientPullbackIso c n).hom ≫
      pullback.snd (structureMap R n) (Spec.map (CommRingCat.ofHom c)) =
        structureMap S n :=
  (mapCoefficients_isPullback c n).isoPullback_hom_snd

end AlgebraicSimplex

attribute [colib_tag "COL-0347"] AlgebraicSimplex.mapCoefficients_isPullback
attribute [colib_tag "COL-0347"] AlgebraicSimplex.coefficientPullbackIso
