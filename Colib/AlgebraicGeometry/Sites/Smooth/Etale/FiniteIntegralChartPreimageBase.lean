/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.FiniteIntegralChartPreimage
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodPreimageBaseTransport

/-! # Keep the actual integral component while transporting its lower base point -/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry IntermediateField Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
local instance nativePreimageBaseAlgebra (E L : Type u) [Field E] [Field L]
    [Algebra E L] (t : Finset L) : Algebra E (adjoin E (t : Set L)) :=
  (adjoin E (t : Set L)).toSubalgebra.algebra

variable (K E L B : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E]
    [Algebra E L] [Algebra K L] [IsScalarTower K E L] [Algebra.IsSeparable E L]
    [CommRing B] [Algebra E B] [Algebra K B] [IsScalarTower K E B]
    [Algebra.Smooth E B] [Algebra.Smooth K B]
    (t : Finset L) (e : (adjoin E (t : Set L)) ⊗[E] B)
    [Algebra.Smooth K (Localization.Away e)]


local instance preimageBaseTargetAffine (A : Type u) [CommRing A]
    [Algebra K A] [Algebra.Smooth K A] : IsAffine (originalAffineTargetSite K A).left :=
  inferInstanceAs (IsAffine (Spec (.of A)))
local instance ground_affine : IsAffine (base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

/-- A rational-positive preimage on this exact component, at its own structural
base point, supplies the original representative preimage after equality transport. -/
theorem finiteIntegralChart_preimage_at_own_base
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (φ : L →+* Ω) (x₁ : Spec (.of L) ⟶ Spec (.of (Localization.Away e)))
    (ξ : Spec (.of Ω) ⟶ Spec (.of B))
    (hmark : (Spec.map (CommRingCat.ofHom φ) ≫ x₁) ≫
      finsetLocalizationToBase E L B t e = ξ)
    (Q : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (b : Q.obj (op (originalAffineTargetSite K B)))
    (hcomponent : ∃ z : etaleNeighborhoodValue (base (Spec (.of K)))
        ((Spec.map (CommRingCat.ofHom φ) ≫ x₁) ≫
          (originalAffineTargetSite K (Localization.Away e)).hom) Q,
      etaleNeighborhoodValuePullback
        (homMk (originalAffineTargetSite K (Localization.Away e)).hom
          (by exact Category.comp_id _) :
          originalAffineTargetSite K (Localization.Away e) ⟶ base (Spec (.of K)))
        (ξ := Spec.map (CommRingCat.ofHom φ) ≫ x₁) rfl Q z =
      toEtaleNeighborhoodValueFromObject (originalAffineTargetSite K (Localization.Away e))
        (Spec.map (CommRingCat.ofHom φ) ≫ x₁) Q
        (Q.map (finiteIntegralChartToOriginal K E L B t e).op b)) :
    ∃ z : etaleNeighborhoodValue (base (Spec (.of K)))
        (ξ ≫ (originalAffineTargetSite K B).hom) Q,
      etaleNeighborhoodValuePullback
        (homMk (originalAffineTargetSite K B).hom (by exact Category.comp_id _) :
          originalAffineTargetSite K B ⟶ base (Spec (.of K))) (ξ := ξ) rfl Q z =
      toEtaleNeighborhoodValueFromObject (originalAffineTargetSite K B) ξ Q b := by
  exact exists_original_preimage_of_etale_chart_preimage_at_own_base
    (T := base (Spec (.of K)))
    (finiteIntegralChartToOriginal K E L B t e)
    (homMk (originalAffineTargetSite K B).hom (by exact Category.comp_id _))
    (homMk (originalAffineTargetSite K (Localization.Away e)).hom
      (by exact Category.comp_id _))
    (finiteIntegralChartToOriginal_structure K E L B t e)
    (Spec.map (CommRingCat.ofHom φ) ≫ x₁) ξ hmark Q b hcomponent
end AlgebraicGeometry.Scheme.SmoothSite
