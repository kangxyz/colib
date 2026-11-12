/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Bertini.NormalizedMovingPointEvaluation
public import Colib.RingTheory.Bertini.QuadraticIncidenceParameterMap

/-! # The literal original parameter map on a normalized moving-point chart

These definitions are separated from their transcendence-degree calculation.
The incidence ring is the full quotient, including its nilpotents. It retains
all original generators, monomials, and normalized weight coordinates.
-/
@[expose] public noncomputable section
universe u
namespace QuadraticIncidence.MovingPointChart
variable (k R B : Type u) [CommRing k] [CommRing R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
  {σ : Type u} [Fintype σ]

/-- The full original incidence quotient on an actual normalized chart. -/
abbrev incidenceRing (g : σ → R) (a : σ → B) (d : ℕ) (i₀ : Fin d) (j : σ) :=
  let t := algebraMap R B (g j) - a j
  let A := Ring B d i₀ t
  CoordinateRing k R A g (algebraMap B A ∘ a) d (weight B d i₀ t)

/-- The actual ground-coefficient parameter map for the original normalized chart. -/
def chartParameterMap (g : σ → R) (a : σ → B) (d : ℕ) (i₀ : Fin d) (j : σ) :
    MvPolynomial (Fin d × Exponent σ) k →ₐ[k] incidenceRing k R B g a d i₀ j :=
  let t := algebraMap R B (g j) - a j
  let A := Ring B d i₀ t
  parameterMap k R A g (algebraMap B A ∘ a) d (weight B d i₀ t)

end QuadraticIncidence.MovingPointChart
