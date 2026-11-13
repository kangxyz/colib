/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.RingTheory.Kaehler.ResidueIndependentSmoothMap
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Prescribed independent residue coordinates produce a local smooth curve

Adapted from the Motivic 2026-10-21 checkpoint, with the compactification imports
replaced by native smoothness of a polynomial projection. The original tuple is unchanged.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry

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

/- The relative-curve existence theorem is publicly re-exported from the canonical
ring-theoretic module above, together with its catalog attribution. -/

end AlgebraicGeometry
