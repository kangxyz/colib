/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Bertini.MovingPointBadPointExclusion
public import Colib.RingTheory.Bertini.MovingPointParameterAvoidance
public import Colib.RingTheory.Bertini.QuadraticParameterTuple

/-! # Actual quadratic tuples avoid every off-diagonal bad point

A common nonzero relation is constructed from the original incidence charts.
Its nonvanishing controls the literal original monomial tuple over every field
of a moving point. The field is not chosen before the parameter coefficients.
-/
@[expose] public noncomputable section
open _root_.MvPolynomial TensorProduct KaehlerDifferential
universe u
namespace QuadraticIncidence.MovingPointChart
variable (k R B : Type u) [Field k] [CommRing R] [IsDomain R] [CommRing B]
  [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
  [Module.Finite R B] [Algebra.Smooth k R] {σ : Type u} [Fintype σ]

/-- A nonzero open in the original parameter algebra excludes every off-diagonal
bad point of the literal tuple, over all moving-point fields simultaneously. -/
theorem exists_nonzero_offDiagonal_parameterTuple_open
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → B) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ)) :
    ∃ f : MvPolynomial (Fin d × Exponent σ) k, f ≠ 0 ∧
      ∀ (c : Fin d × Exponent σ → k), eval c f ≠ 0 →
      ∀ (K : Type u) [Field K] [Algebra k K] [Algebra R K] [Algebra B K]
        [IsScalarTower k B K] [IsScalarTower R B K],
      (fun j => algebraMap R K (g j)) ≠ algebraMap B K ∘ a →
      (∀ i, eval (fun j => algebraMap R K (g j))
          (parameterTuple K σ d (algebraMap k K ∘ c) i).val =
        eval (algebraMap B K ∘ a) (parameterTuple K σ d (algebraMap k K ∘ c) i).val) →
      LinearIndependent K (fun i => residueGeneratorGradient k R K g
        (fun j => eval (fun l => algebraMap R K (g l))
          (pderiv j (parameterTuple K σ d (algebraMap k K ∘ c) i).val))) := by
  obtain ⟨f, hf, hz⟩ := exists_nonzero_common_parameter_relation k R B g hg a d hd
  refine ⟨f, hf, ?_⟩
  intro c hc K _ _ _ _ _ _ hab hvalue
  exact linearIndependent_of_parameter_relation_ne_zero k R B K g a d f c hc hz
    (parameterTuple K σ d (algebraMap k K ∘ c))
    (fun q => parameterTuple_repr K σ d (algebraMap k K ∘ c) q) hab hvalue

/-- Over an infinite ground field one unchanged quadratic tuple simultaneously
satisfies any prescribed nonempty principal open and avoids every off-diagonal
bad point over every moving-point field. No incidence relation is an input. -/
theorem exists_parameterTuple_offDiagonal_independent [Infinite k]
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a : σ → B) (d : ℕ) (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ c : Fin d × Exponent σ → k, eval c q ≠ 0 ∧
      ∀ (K : Type u) [Field K] [Algebra k K] [Algebra R K] [Algebra B K]
        [IsScalarTower k B K] [IsScalarTower R B K],
      (fun j => algebraMap R K (g j)) ≠ algebraMap B K ∘ a →
      (∀ i, eval (fun j => algebraMap R K (g j))
          (parameterTuple K σ d (algebraMap k K ∘ c) i).val =
        eval (algebraMap B K ∘ a) (parameterTuple K σ d (algebraMap k K ∘ c) i).val) →
      LinearIndependent K (fun i => residueGeneratorGradient k R K g
        (fun j => eval (fun l => algebraMap R K (g l))
          (pderiv j (parameterTuple K σ d (algebraMap k K ∘ c) i).val))) := by
  obtain ⟨f, c, _, hcf, hcq, hz⟩ :=
    exists_parameter_choice_avoiding_charts k R B g hg a d hd q hq
  refine ⟨c, hcq, ?_⟩
  intro K _ _ _ _ _ _ hab hvalue
  exact linearIndependent_of_parameter_relation_ne_zero k R B K g a d f c hcf hz
    (parameterTuple K σ d (algebraMap k K ∘ c))
    (fun q => parameterTuple_repr K σ d (algebraMap k K ∘ c) q) hab hvalue

end QuadraticIncidence.MovingPointChart
