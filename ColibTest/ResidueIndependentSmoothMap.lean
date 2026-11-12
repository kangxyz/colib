/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.RelativeCurve.Presentation.ResidueIndependentSmoothMap

open Module TensorProduct KaehlerDifferential AlgebraicGeometry
universe u

/-- The output uses the original tail map and keeps the selected prime. -/
example
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (p : Ideal R) [p.IsPrime] (d : ℕ) (f : Fin d → R)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (hf : LinearIndependent p.ResidueField
      (fun i => (1 ⊗ₜ[R] D k R (f i) : p.ResidueField ⊗[R] Ω[R⁄k]))) :
    ∃ r ∉ p, SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
        (MvPolynomial.aeval (R := k) f).toRingHom))) := by
  exact exists_smooth_one_of_residue_independent k R p d f hd hf

#print axioms Algebra.exists_etale_polynomial_map_of_residue_differential_basis
#print axioms Algebra.cotangent_finrank_eq_trdeg_toNat
#print axioms Algebra.exists_etale_cons_of_residue_independent
#print axioms AlgebraicGeometry.exists_smooth_one_of_residue_independent
