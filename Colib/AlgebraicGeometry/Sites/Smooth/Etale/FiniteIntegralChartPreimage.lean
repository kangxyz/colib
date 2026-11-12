/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Limits.FiniteIntegralChartGround
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodEtalePreimage
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStageOriginalTarget

/-! # Reflect the same preimage along the actual finite integral component chart

This is a reflection lemma, not a positive-dimensional existence hypothesis or
an assertion that the induction is complete.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry IntermediateField Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

local instance nativeChartAlgebra (E L : Type u) [Field E] [Field L]
    [Algebra E L] (t : Finset L) : Algebra E (adjoin E (t : Set L)) :=
  (adjoin E (t : Set L)).toSubalgebra.algebra

variable (K E L B : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E]
    [Algebra E L] [Algebra K L] [IsScalarTower K E L] [Algebra.IsSeparable E L]
    [CommRing B] [Algebra E B] [Algebra K B] [IsScalarTower K E B]
    [Algebra.Smooth E B] [Algebra.Smooth K B]
    (t : Finset L) (e : (adjoin E (t : Set L)) ⊗[E] B)
    [Algebra.Smooth K (Localization.Away e)]

/-- The actual finite localized tensor chart as a map in the original K-site. -/
def finiteIntegralChartToOriginal :
    originalAffineTargetSite K (Localization.Away e) ⟶ originalAffineTargetSite K B :=
  homMk (finsetLocalizationToBase E L B t e)
    (finiteIntegralChart_smooth_ground_and_square K E L B t e).2

instance finiteIntegralChartToOriginal_etale :
    Etale (finiteIntegralChartToOriginal K E L B t e).left :=
  etale_finsetLocalizationToBase E L B t e

/-- Its composite with the original structural arrow is the actual component
structural arrow, so a lower preimage can be reused without changing z. -/
theorem finiteIntegralChartToOriginal_structure :
    finiteIntegralChartToOriginal K E L B t e ≫
      (homMk (originalAffineTargetSite K B).hom (by exact Category.comp_id _) :
        originalAffineTargetSite K B ⟶ base (Spec (.of K))) =
      (homMk (originalAffineTargetSite K (Localization.Away e)).hom (by exact Category.comp_id _) :
        originalAffineTargetSite K (Localization.Away e) ⟶ base (Spec (.of K))) := by
  apply MorphismProperty.Over.Hom.ext
  exact (finiteIntegralChart_smooth_ground_and_square K E L B t e).2

local instance originalAffineTargetSite_affine (A : Type u) [CommRing A]
    [Algebra K A] [Algebra.Smooth K A] : IsAffine (originalAffineTargetSite K A).left :=
  inferInstanceAs (IsAffine (Spec (.of A)))

/-- Retain the exact original marking and the exact lower element z. -/
theorem finiteIntegralChart_reflect_preimage
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (φ : L →+* Ω) (x₁ : Spec (.of L) ⟶ Spec (.of (Localization.Away e)))
    (ξ : Spec (.of Ω) ⟶ Spec (.of B))
    (hmark : (Spec.map (CommRingCat.ofHom φ) ≫ x₁) ≫
      finsetLocalizationToBase E L B t e = ξ)
    {T : SmoothSite (Spec (.of K))} [IsAffine T.left]
    (g : originalAffineTargetSite K B ⟶ T)
    (ζ : Spec (.of Ω) ⟶ T.left) (hg : ξ ≫ g.left = ζ)
    (Q : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (b : Q.obj (op (originalAffineTargetSite K B)))
    (z : etaleNeighborhoodValue T ζ Q)
    (hz : etaleNeighborhoodValuePullback
        (finiteIntegralChartToOriginal K E L B t e ≫ g)
        (by change (Spec.map (CommRingCat.ofHom φ) ≫ x₁) ≫
              (finsetLocalizationToBase E L B t e ≫ g.left) = ζ
            erw [← Category.assoc, hmark, hg]) Q z =
      toEtaleNeighborhoodValueFromObject (originalAffineTargetSite K (Localization.Away e))
        (Spec.map (CommRingCat.ofHom φ) ≫ x₁) Q
        (Q.map (finiteIntegralChartToOriginal K E L B t e).op b)) :
    etaleNeighborhoodValuePullback g hg Q z =
      toEtaleNeighborhoodValueFromObject (originalAffineTargetSite K B) ξ Q b := by
  exact original_preimage_of_etale_chart_preimage
    (finiteIntegralChartToOriginal K E L B t e) g
    (Spec.map (CommRingCat.ofHom φ) ≫ x₁) ξ ζ hmark hg Q b z hz

end AlgebraicGeometry.Scheme.SmoothSite
