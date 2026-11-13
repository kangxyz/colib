/-
Copyright (c) 2026 kangxyz, Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Bertini.QuadraticIncidenceAlgebra
public import Mathlib.LinearAlgebra.StdBasis

/-! # The universal quadratic coefficients have the proved incidence rank -/
@[expose] public noncomputable section
open _root_.MvPolynomial Module TensorProduct KaehlerDifferential LinearMap
universe u v w z
namespace QuadraticIncidence

variable (k : Type u) (R : Type v) (K : Type w)
  [CommRing k] [CommRing R] [Field K] [Algebra k R] [Algebra R K]
  {σ : Type z} [Fintype σ]

/-- Each literal universal coefficient is the corresponding monomial's actual
value and cotangent image under the normalized constraint map. -/
theorem coefficientVector_eq_constraint (g : σ → R) (a : σ → K)
    (d : ℕ) (w : Fin d → K) (q : Fin d × Exponent σ) :
    coefficientVector k R K g a d w q =
      normalizedJetConstraints
        (quadraticResidueJet k R K g a (fun i => algebraMap R K (g i))) w
        (Pi.single q.1 ((monomialBasis K σ) q.2)) := by
  classical
  let J := quadraticResidueJet k R K g a (fun i => algebraMap R K (g i))
  have hs (x : restrictTotalDegree σ K 2) (i₀ : Fin d) :
      normalizedJetConstraints J w (Pi.single i₀ x) =
        (Pi.single i₀ (J x).1, w i₀ • (J x).2) := by
    apply Prod.ext
    · ext i
      by_cases h : i = i₀
      · subst i
        simp [normalizedJetConstraints]
      · simp [normalizedJetConstraints, Pi.single_apply, h]
    · change (∑ i, w i • (J ((Pi.single i₀ x : Fin d → restrictTotalDegree σ K 2) i)).2) = _
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro i _ hi
        simp [hi]
      · simp
  change coefficientVector k R K g a d w q = normalizedJetConstraints J w _
  rw [hs]
  let b := fun i => algebraMap R K (g i)
  change (Pi.single (M := fun _ : Fin d => K) q.1
    (eval b (monomial q.2.val 1) - eval a (monomial q.2.val 1)),
    w q.1 • residueGeneratorGradient k R K g
      (fun i => eval b (pderiv i (monomial q.2.val 1)))) =
    (Pi.single (M := fun _ : Fin d => K) q.1 (eval b (monomialBasis K σ q.2).val -
      eval a (monomialBasis K σ q.2).val),
    w q.1 • residueGeneratorGradient k R K g
      (fun i => eval b (pderiv i (monomialBasis K σ q.2).val)))
  rw [monomialBasis_coe]


/-- All original universal coefficient vectors span the full incidence equation
module at every second geometric point distinct from the fixed point. -/
theorem span_coefficientVector (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (a : σ → K)
    (hab : a ≠ fun i => algebraMap R K (g i))
    (d : ℕ) (w : Fin d → K) (i₀ : Fin d) (hw : w i₀ = 1) :
    Submodule.span K (Set.range (coefficientVector k R K g a d w)) = ⊤ := by
  let J := normalizedJetConstraints
    (quadraticResidueJet k R K g a (fun i => algebraMap R K (g i))) w
  have hJ : Function.Surjective J := normalizedJetConstraints_surjective _
    (quadraticResidueJet_surjective k R K g hg a _ hab) w i₀ hw
  have hv : coefficientVector k R K g a d w = J ∘ parameterBasis K σ d := by
    funext q
    simpa [J] using coefficientVector_eq_constraint k R K g a d w q
  rw [hv, Set.range_comp, ← Submodule.map_span, (parameterBasis K σ d).span_eq,
    Submodule.map_top, LinearMap.range_eq_top.mpr hJ]

end QuadraticIncidence
