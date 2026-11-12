/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization

/-! # Base units in the actual etale local ring

The original structure morphism to an affine base gives a ring homomorphism
into the actual etale local ring by full faithfulness of Spec. Invertibility
of the torsion exponent is transported along this map, without assuming a
separate unit witness on the strict henselization or choosing an algebra.
-/
@[expose] public noncomputable section
open CategoryTheory
universe u
namespace AlgebraicGeometry

/-- The ring homomorphism corresponding to the actual strict-local structure
map to the original affine base. -/
def strictHenselizationBaseRingHom (B : BigEtaleSite.{u})
    (X : Scheme.{u}) (hX : B.Contains X) (s : GeometricPoint X)
    {R : CommRingCat.{u}} (p : X ⟶ Spec R) :
    R →+* ↥(etaleLocalRing B X hX s) :=
  (Scheme.Spec.preimage (strictHenselizationToBase B X hX s ≫ p)).unop.hom

/-- The ring homomorphism recovers the original composite scheme map exactly. -/
theorem specMap_strictHenselizationBaseRingHom (B : BigEtaleSite.{u})
    (X : Scheme.{u}) (hX : B.Contains X) (s : GeometricPoint X)
    {R : CommRingCat.{u}} (p : X ⟶ Spec R) :
    Spec.map (CommRingCat.ofHom (strictHenselizationBaseRingHom B X hX s p)) =
      strictHenselizationToBase B X hX s ≫ p :=
  Scheme.Spec.map_preimage _

/-- An exponent invertible on the original affine base is invertible in the
actual etale local ring. For a smooth-site object over Spec K, use its own
structure map as p; no extra local-unit hypothesis is needed. -/
theorem isUnit_natCast_etaleLocalRing_of_spec_structure (B : BigEtaleSite.{u})
    (X : Scheme.{u}) (hX : B.Contains X) (s : GeometricPoint X)
    {R : CommRingCat.{u}} (p : X ⟶ Spec R) (n : ℕ) (hn : IsUnit (n : R)) :
    IsUnit (n : ↥(etaleLocalRing B X hX s)) := by
  simpa only [map_natCast] using hn.map (strictHenselizationBaseRingHom B X hX s p)

end AlgebraicGeometry
