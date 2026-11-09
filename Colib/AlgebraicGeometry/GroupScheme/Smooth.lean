/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.GroupScheme.LaurentOpen
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Smoothness of the existing native additive and multiplicative group schemes

Use Stacks' existing integral schemes and their actual base changes. The Laurent
projection factors through Colib's existing positive Laurent open. This adapts
the smoothness argument of motivic_source_a6805c4,
`Motivic/Aglib/AlgebraicGeometry/Spec/PolynomialLaurent/Torus.lean`,
without introducing a second polynomial/Laurent scheme model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The native integral affine-line structure map is smooth. -/
instance smooth_additiveGroup_projection :
    Smooth (additiveGroup.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  change (algebraMap (ULift.{u} ℤ) (Polynomial (ULift.{u} ℤ))).Smooth
  rw [RingHom.smooth_algebraMap]
  exact ⟨inferInstance, inferInstance⟩

/-- The native multiplicative projection is the smooth positive-open composite. -/
instance smooth_multiplicativeGroup_projection :
    Smooth (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  rw [← multiplicativeGroupToAdditive_over]
  infer_instance

instance separated_additiveGroup_projection :
    IsSeparated (additiveGroup.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  change IsSeparated (Spec.map (CommRingCat.ofHom Polynomial.C))
  infer_instance

instance separated_multiplicativeGroup_projection :
    IsSeparated (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  change IsSeparated (Spec.map (CommRingCat.ofHom LaurentPolynomial.C))
  infer_instance

instance quasiCompact_additiveGroup_projection :
    QuasiCompact (additiveGroup.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom Polynomial.C))
  infer_instance

instance quasiCompact_multiplicativeGroup_projection :
    QuasiCompact (multiplicativeGroupULift.{u} ↘ Spec (.of (ULift.{u} ℤ))) := by
  change QuasiCompact (Spec.map (CommRingCat.ofHom LaurentPolynomial.C))
  infer_instance

end AlgebraicGeometry
