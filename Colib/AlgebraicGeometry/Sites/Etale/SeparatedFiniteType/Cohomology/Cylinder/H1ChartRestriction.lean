/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.Inputs
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Contraction.ProjectionExcision
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.ChartCoefficientRestriction
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.H1PunctureRecognition
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.LocalEffacement
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.MarkedBaseBoundary
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.PositivePunctureRecognition

/-!
# Degree-one puncture restriction on a marked product chart

The degree-one ordinary edge identifies the original puncture kernel.
The coefficient localization sequence and an actual marked-base lift of
its boundary section kill the kernel on the whole cylinder.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/Cylinder/H1ChartVanishing.lean`
and `Motivic/Cohomology/A1/Cartier/Restriction/H1RestrictionInputs.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open _root_.Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary

open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.SmoothSite.Contraction

local instance chartHasExt (S : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives _

variable {k : Type u} [Field k]
  (hD : PresheafWithTransfers.IntegralAffineLocalZero k)
  (hEpi : OriginalPresheaf.CanonicalBoundaryEpi k)
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  (X : SmoothSite (Spec (.of k))) {E U : SmoothSite (Spec (.of k))}
  (b : E ⟶ affineLineCylinder.obj X) [Etale b.left]
  (F : SheafWithTransfers.{u + 1} k) (j : U ⟶ E) (q : U ⟶ torusCylinder.obj X)
  (hj : IsPullback q j (openInclusion.app X) b)
  (hF : F.obj.IsA1Invariant)
  (Φ : (nisnevichTopology E.left).Point.{u + 1})

local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F
local notation "E₁" => affineLineCylinder.obj E
local notation "πE" =>
  NatTrans.app (projection (SmoothSite.additiveGroupObject (Spec (CommRingCat.of k)))) E
local notation "j₁" => affineLineCylinder.map j

omit [HasExt.{u + 1}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
include hD hEpi hj hF in
/-- The genuine coefficient kernel in degree one dies over an actual
marked-base refinement. -/
theorem exists_pointed_chart_H1_coefficient_kernel_restriction_zero
    (V : Φ.fiber.Elements)
    (x : (cohomologyPresheaf.{u + 1, u + 1} ((restrict E₁ AddCommGrpCat).obj G) 1).obj
      (op ((baseChange (πE).left).obj V.obj)))
    (hx : x.comp (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero 1) = 0) :
    ∃ (W : Φ.fiber.Elements) (a : W ⟶ V),
      (cohomologyPresheaf.{u + 1, u + 1} ((restrict E₁ AddCommGrpCat).obj G) 1).map
        ((baseChange (πE).left).map a.hom).op x = 0 := by
  let r := restrictionToDirectImage G j₁
  let := chartProduct_restrictionToDirectImage_mono hD X b F j q hj hF
  let S := ShortComplex.mk r (cokernel.π r) (cokernel.condition r)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  let V₁ := (baseChange (πE).left).obj V.obj
  obtain ⟨y, hy⟩ := markedBase_H1_kernel_has_connecting_section (πE).left Φ hS V x hx
  let c₁ := extSectionsAddEquiv.{u + 1, u + 1} V₁ S.X₃ y
  let : IsOpenImmersion j.left := MorphismProperty.of_isPullback
    ((SmoothSite.forgetScheme (Spec (.of k))).map_isPullback hj)
    (inferInstanceAs (IsOpenImmersion (openInclusion.app X).left))
  obtain ⟨W, a, w, t, ha, ht⟩ :=
    exists_pointed_a1_product_quotient_lift_of_chart X b F j q hj hF
      (contractionToBoundary_epi_of_canonicalBoundaryEpi hEpi X F hF)
      (contractionToBoundary_epi_of_canonicalBoundaryEpi hEpi (affineLineCylinder.obj X) F hF)
      Φ V.obj V.val c₁
  let M : Φ.fiber.Elements := Functor.elementsMk _ W w
  let f : M ⟶ V := Functor.Elements.homMk a ha
  refine ⟨M, f, ?_⟩
  have hz := markedBase_H1_boundary_restriction_zero (πE).left Φ hS f y
    ((a1PuncturedProjectionMap j G).hom.app (op W) t) ht
  rwa [hy] at hz

include hD hEpi hj hF in
/-- Every original degree-one puncture-zero representative dies at its full mark. -/
theorem pointedCylinder_H1_germ_zero_of_chart_puncture_restriction_zero
    (V : Φ.fiber.Elements)
    (s : (pointedCylinderValues (.of k) (X := E) Φ
      (cohomologyPresheaf.{u + 1, u + 1} G 1) (pointedBase (.of k) (X := E) Φ)).obj (op V))
    (hs : (pointedCylinderRestriction (.of k) j Φ
      (cohomologyPresheaf.{u + 1, u + 1} G 1)).app (op V) s = 0) :
    colimit.ι (pointedCylinderValues (.of k) (X := E) Φ
      (cohomologyPresheaf.{u + 1, u + 1} G 1) (pointedBase (.of k) (X := E) Φ)) (op V) s = 0 := by
  have hx := pointedCylinder_H1_coefficient_kernel_of_puncture_restriction_zero
    (.of k) j G Φ V s hs
  obtain ⟨W, a, ha⟩ := exists_pointed_chart_H1_coefficient_kernel_restriction_zero
    hD hEpi X b F j q hj hF Φ V ((pointedCylinderOrdinaryIso (.of k) E Φ G 1).hom.app (op V) s)
    hx
  exact pointedCylinder_germ_eq_zero_of_ordinary_base_refinement (.of k) E Φ G 1 a s ha

include hD hEpi hj hF in
/-- The degree-one puncture map is monic on the original marked colimit. -/
theorem pointedCylinderRestriction_H1_colimit_mono_of_chart :
    Mono (colim.map (pointedCylinderRestriction (.of k) j Φ
      (cohomologyPresheaf.{u + 1, u + 1} G 1))) :=
  pointedCylinderRestriction_colimit_mono_of_local_kernel (.of k) j Φ
    (cohomologyPresheaf.{u + 1, u + 1} G 1)
    (pointedCylinder_H1_germ_zero_of_chart_puncture_restriction_zero
      hD hEpi X b F j q hj hF Φ)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
