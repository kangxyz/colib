/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Bertini.QuadraticCoordinateFinite
public import Colib.RingTheory.Bertini.QuadraticClosedInfinityAvoidance
public import Colib.RingTheory.Bertini.QuadraticQuotientCoordinates
public import Colib.RingTheory.FiniteType.MinimalComponents.Quotient

/-! # Finiteness on the original nonreduced bad quotient

The original minimal components first inherit the actual finite tail map.
Their finite product controls the original quotient modulo a nilpotent kernel.
Finiteness therefore holds on the entire unchanged quotient, not its reduction.
-/
@[expose] public noncomputable section
universe u
namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  [IsNoetherianRing R] {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)

/-- The unchanged quadratic tail is finite on the full specified quotient. -/
theorem quadraticClosedCoordinateHom_finite (I : Ideal R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (c : Fin d × Exponent σ → k) (hc : NoCommonClosedInfinityZero k R I g d c) :
    ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k R g d c)).Finite := by
  apply RingHom.finite_quotient_of_minimal_components
  intro P hP
  let : P.IsPrime := hP.isPrime
  rw [← quadraticCoordinateHom_quotient]
  exact quadraticCoordinateHom_finite_of_no_infinity k (R ⧸ P)
    (Ideal.Quotient.mk P ∘ g) d (quadraticGenerators_quotient k R g P hg) c (hc ⟨P, hP⟩)

end QuadraticIncidence.InfinityChart
