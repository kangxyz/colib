/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.BoundedFiberSupport
public import Colib.Topology.Realization.FiniteDeformationSupport

/-!
# Bounded supports for a finite deformation witness on a site fiber

The retraction and its homotopy on one finite target subcomplex are
represented by bounded simplicial subpresheaves of the original source
and target. Their original realized values are retained. This is one
enlargement witness in Jardine, *Simplicial presheaves*, Lemma 2.4,
pp. 65–66. https://doi.org/10.1016/0022-4049(87)90100-9
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
universe t w v u

namespace CategoryTheory.SimplicialSubpresheaf

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C} {P Q : Cᵒᵖ ⥤ SSet.{w}}

/-- On a finite subcomplex of the target fiber, the original retraction
and homotopy both have bounded subpresheaf supports. -/
theorem exists_bounded_deformation_witness
    (Φ : J.Point.{w}) (f : P ⟶ Q)
    (R : TopCat.CylinderStrongDeformationRetract (SSet.toTop.map (Φ.presheafFiber.map f)))
    (A : (Φ.presheafFiber.obj Q).Subcomplex) [SSet.Finite A]
    (κ : Cardinal.{t}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (hC : ∀ q : Cᵒᵖ × SimplexCategoryᵒᵖ,
      HasCardinalLT (Σ r : Cᵒᵖ × SimplexCategoryᵒᵖ, q ⟶ r) κ) :
    ∃ B : Subpresheaf P, HasBoundedSections B κ ∧
      ∃ D : Subpresheaf Q, HasBoundedSections D κ ∧
        ∃ (r : SSet.toTop.obj A ⟶ SSet.toTop.obj (Φ.presheafFiber.obj (toPresheaf B)))
          (H : SSet.toTop.obj A ⊗ TopCat.I ⟶ SSet.toTop.obj (Φ.presheafFiber.obj (toPresheaf D))),
          r ≫ SSet.toTop.map (Φ.presheafFiber.map (inclusion B)) = SSet.toTop.map A.ι ≫ R.r ∧
            H ≫ SSet.toTop.map (Φ.presheafFiber.map (inclusion D)) =
              (SSet.toTop.map A.ι ▷ TopCat.I) ≫ R.H := by
  obtain ⟨B₀, hB₀, D₀, hD₀, r, H, hr, hH⟩ := SSet.finiteSubcomplex_deformationRetract_support R A
  let : SSet.Finite B₀ := hB₀
  let : SSet.Finite D₀ := hD₀
  obtain ⟨B, hB, b, hb⟩ := exists_boundedSubpresheaf_factorization_of_finite Φ B₀.ι κ hκ hC
  obtain ⟨D, hD, d, hd⟩ := exists_boundedSubpresheaf_factorization_of_finite Φ D₀.ι κ hκ hC
  refine ⟨B, hB, D, hD, r ≫ SSet.toTop.map b, H ≫ SSet.toTop.map d, ?_, ?_⟩
  · rw [Category.assoc, ← Functor.map_comp, hb, hr]
  · rw [Category.assoc, ← Functor.map_comp, hd, hH]

end CategoryTheory.SimplicialSubpresheaf
