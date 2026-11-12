/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # The actual polynomial projection is smooth of relative dimension one

This uses the native standard-smooth polynomial presentation, without a
compactification or any chosen projective chart.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineLineEtaleCompactification

/-- The literal polynomial affine line is smooth of relative dimension one. -/
theorem polynomialProjection_smooth_one (k : Type u) [CommRing k] :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap k (Polynomial k))
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial PUnit.{u + 1} k) := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial k PUnit.{u + 1}
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
    (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1})

end AlgebraicGeometry.Scheme.AffineLineEtaleCompactification
