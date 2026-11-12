/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Bertini.QuadraticClosedCoordinateFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # The actual finite quadratic maps for the relative-curve producer

These are affine-scheme translations of proved algebraic finiteness. The
normalization and relative projective-line compactification are separate
consumers; no compactification or finite-map existence is assumed here.
-/
@[expose] public noncomputable section
open AlgebraicGeometry
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)

/-- The original bad quotient has its actual finite map to the tail affine space. -/
theorem quadraticClosedTuple_isFinite [IsNoetherianRing R] (I : Ideal R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (c : Fin d × Exponent σ → k) (hc : NoCommonClosedInfinityZero k R I g d c) :
    IsFinite (Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k R g d c)))) :=
  (IsFinite.SpecMap_iff _).mpr (quadraticClosedCoordinateHom_finite k R g d I hg c hc)

/-- The chosen auxiliary row supplies a finite map to the actual relative affine line. -/
theorem quadraticRelativeTuple_isFinite [IsDomain R]
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : Exponent σ → k) (c : Fin d × Exponent σ → k)
    (h : NoCommonInfinityZero k R g d (prependParameters k d a c)) :
    IsFinite (Spec.map (CommRingCat.ofHom
      (quadraticRelativeCoordinateHom k R g d a c))) :=
  (IsFinite.SpecMap_iff _).mpr (quadraticRelativeCoordinateHom_finite k R g d hg a c h)

end QuadraticIncidence.InfinityChart
