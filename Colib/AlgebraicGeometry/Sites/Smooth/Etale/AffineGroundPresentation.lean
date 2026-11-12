/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.FiniteIntegralChartPreimage

/-! # Preserve the original ground site under an actual affine presentation -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The actual scheme structural square forces compatibility of the two native
scalar actions. No replacement of the original K-algebra is made. -/
theorem scalarTower_of_spec_structure_square
    (K E B : Type u) [Field K] [Field E] [CommRing B]
    [Algebra K E] [Algebra E B] [Algebra K B]
    (h : Spec.map (CommRingCat.ofHom (algebraMap E B)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K E)) =
      Spec.map (CommRingCat.ofHom (algebraMap K B))) : IsScalarTower K E B := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp] at h
  have heq := Spec.map_injective h
  apply IsScalarTower.of_algebraMap_eq
  intro x
  exact (congrArg (fun f => f.hom x) heq).symm

variable (K B : Type u) [Field K] [CommRing B] [Algebra K B] [Algebra.Smooth K B]
    (X : SmoothSite (Spec (.of K))) (i : Spec (.of B) ≅ X.left)
    (hi : i.hom ≫ X.hom = Spec.map (CommRingCat.ofHom (algebraMap K B)))

/-- The actual affine scheme isomorphism lifts to the unchanged original K-site. -/
def affineGroundPresentationIso : originalAffineTargetSite K B ≅ X :=
  MorphismProperty.Over.isoMk i hi

@[simp] theorem affineGroundPresentationIso_hom_left :
    (affineGroundPresentationIso K B X i hi).hom.left = i.hom := rfl

/-- The representative is transported by the presheaf along this exact site
isomorphism, and the marking is transported by the same underlying map. -/
theorem affineGroundPresentation_representative [IsAffine X.left]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (η : Spec (.of Ω) ⟶ Spec (.of B))
    (Q : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    let : IsAffine (originalAffineTargetSite K B).left :=
      inferInstanceAs (IsAffine (Spec (.of B)))
    toEtaleNeighborhoodValueFromObject X (η ≫ i.hom) Q ≫
      etaleNeighborhoodValuePullback (affineGroundPresentationIso K B X i hi).hom
        (ξ := η) (η := η ≫ i.hom) rfl Q =
      Q.map (affineGroundPresentationIso K B X i hi).hom.op ≫
        toEtaleNeighborhoodValueFromObject (originalAffineTargetSite K B) η Q := by
  let : IsAffine (originalAffineTargetSite K B).left :=
    inferInstanceAs (IsAffine (Spec (.of B)))
  exact toEtaleNeighborhoodValueFromObject_pullback
    (X := originalAffineTargetSite K B) (Y := X)
    (affineGroundPresentationIso K B X i hi).hom (ξ := η) (η := η ≫ i.hom) rfl Q

include hi in
omit [Algebra.Smooth K B] in
/-- The same actual marking also has exactly the original ground-field point. -/
theorem affineGroundPresentation_mark_base
    {Ω : Type u} [Field Ω] (η : Spec (.of Ω) ⟶ Spec (.of B)) :
    (η ≫ i.hom) ≫ X.hom =
      η ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
  rw [Category.assoc, hi]
end AlgebraicGeometry.Scheme.SmoothSite
