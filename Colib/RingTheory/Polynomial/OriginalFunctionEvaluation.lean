/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Evaluation of the unchanged original polynomial function -/
@[expose] public noncomputable section
open _root_.MvPolynomial
universe u
namespace QuadraticIncidence

/-- Polynomial evaluation at an actual algebra-valued point retains the original function. -/
theorem eval_map_original_function {k R K σ : Type u}
    [CommRing k] [CommRing R] [CommRing K] [Algebra k R] [Algebra k K]
    (s : R →ₐ[k] K) (g : σ → R) (p : MvPolynomial σ k) :
    eval (fun j => s (g j)) (MvPolynomial.map (algebraMap k K) p) = s (aeval g p) := by
  rw [eval_map]
  exact (comp_aeval_apply g s p).symm

end QuadraticIncidence
