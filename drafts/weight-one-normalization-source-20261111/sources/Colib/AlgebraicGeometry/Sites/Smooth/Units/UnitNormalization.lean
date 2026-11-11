/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Units.UnitSheafification

/-!
# Degree-zero normalization of the actual units contraction

The degree-zero component of `unitSingularSheafHomotopyEquiv` is the inverse
of the genuine simplex projection pullback. The calculation unfolds the
existing constant extra-degeneracy contraction; it does not choose a new
comparison map. The canonical `singleObjXSelf` coordinate is retained in the
projection formula.

The actual `unitSheafifiedSingularIso` is also normalized termwise by the
sheafification adjunction's counit. These are supporting calculations for the
existing unit sheaf constructions, with no affine or connectedness hypothesis.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- The existing contraction uses the inverse of the actual zero-simplex pullback. -/
theorem unitSingularSheafHomotopyEquiv_hom_f_zero :
    (unitSingularSheafHomotopyEquiv k).hom.f 0 = inv (unitsSimplexPullback k 0) := by
  change (constantUnitSimplicialSheafIso k).inv.app (op ⦋0⦌) ≫
      (AlternatingFaceMapComplex.ε.app
        (SimplicialObject.Augmented.const.obj (largeUnitsSheaf (Spec (.of k))))).f 0 =
    inv (unitsSimplexPullback k 0)
  rw [AlternatingFaceMapComplex.ε_app_f_zero]
  change inv (unitsSimplexPullback k 0) ≫ 𝟙 _ = inv (unitsSimplexPullback k 0)
  exact Category.comp_id _

/-- The inverse pullback calculation in the canonical single-complex coordinate. -/
theorem unitSingularSheafHomotopyEquiv_hom_f_zero_projection :
    (unitSingularSheafHomotopyEquiv k).hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.down ℕ) 0
        (largeUnitsSheaf (Spec (.of k)))).hom = inv (unitsSimplexPullback k 0) := by
  rw [ChainComplex.single₀ObjXSelf]
  change (unitSingularSheafHomotopyEquiv k).hom.f 0 ≫ 𝟙 _ = _
  rw [Category.comp_id, unitSingularSheafHomotopyEquiv_hom_f_zero]

/-- Actual simplex pullback followed by the fixed contraction is the identity on units. -/
@[reassoc]
theorem unitsSimplexPullback_zero_projection :
    unitsSimplexPullback k 0 ≫ (unitSingularSheafHomotopyEquiv k).hom.f 0 ≫
      (HomologicalComplex.singleObjXSelf (.down ℕ) 0
        (largeUnitsSheaf (Spec (.of k)))).hom = 𝟙 _ := by
  rw [unitSingularSheafHomotopyEquiv_hom_f_zero_projection]
  exact IsIso.hom_inv_id _

/-- The existing sheafified units comparison is the actual adjunction counit in each degree. -/
theorem unitSheafifiedSingularIso_hom_f (n : ℕ) :
    (unitSheafifiedSingularIso k).hom.f n =
      (sheafificationAdjunction (nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).counit.app ((unitSingularSheafComplex k).X n) := by
  change (presheafToSheaf (nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}).map ((unitRawComplexIso k).hom.f n) ≫
      (sheafificationAdjunction (nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).counit.app ((unitSingularSheafComplex k).X n) = _
  rw [unitRawComplexIso_hom_f, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The raw units term maps to the existing sheafified comparison by the native triangle law. -/
@[reassoc]
theorem toSheafify_unitSheafifiedSingularIso_hom_f (n : ℕ) :
    toSheafify (nisnevichTopology (Spec (.of k)))
        (((_root_.AlgebraicSimplex.singularChainsFunctor k).obj
          (largeUnitsPresheaf (Spec (.of k)))).X n) ≫
      ((unitSheafifiedSingularIso k).hom.f n).hom = 𝟙 _ := by
  change toSheafify (nisnevichTopology (Spec (.of k)))
      ((unitSingularSheafComplex k).X n).obj ≫
      ((unitSheafifiedSingularIso k).hom.f n).hom = _
  rw [unitSheafifiedSingularIso_hom_f]
  exact (sheafificationAdjunction (nisnevichTopology (Spec (.of k)))
    AddCommGrpCat.{u + 1}).right_triangle_components ((unitSingularSheafComplex k).X n)

end AlgebraicGeometry.Scheme.SmoothSite
