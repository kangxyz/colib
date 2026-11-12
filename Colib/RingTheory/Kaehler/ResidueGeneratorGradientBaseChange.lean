/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Kaehler.ResidueGeneratorGradient

/-! # Actual residue-generator gradients commute with scalar extension

This minimal leaf is separated from incidence-coordinate definitions so that
scalar cotangent proofs need no parameter-chart or non-dominance hypotheses.
-/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential
universe u v w x z
namespace QuadraticIncidence

variable (k : Type u) (R : Type v) (A : Type w) (K : Type x)
  [CommRing k] [CommRing R] [CommRing A] [CommRing K]
  [Algebra k R] [Algebra R A] [Algebra R K] [Algebra A K]
  [IsScalarTower R A K] {σ : Type z} [Fintype σ]

/-- Cancellation of scalar extension transports the actual generator gradient. -/
theorem baseChange_residueGeneratorGradient (g : σ → R) (c : σ → A) :
    AlgebraTensorModule.cancelBaseChange R A K K Ω[R⁄k]
        (1 ⊗ₜ[A] residueGeneratorGradient k R A g c) =
      residueGeneratorGradient k R K g (algebraMap A K ∘ c) := by
  simp only [residueGeneratorGradient, Fintype.linearCombination_apply,
    tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [smul_tmul', Algebra.smul_def]

end QuadraticIncidence
