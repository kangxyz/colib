/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.ChartCoefficientRestriction
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.ChartHigherImages
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.LocalEffacement
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.PositivePunctureRecognition
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.PositiveSupport

/-!
# Positive puncture restriction on a marked product chart

The lower higher-image window identifies the original puncture kernel
with a coefficient kernel. The localization sequence then reduces this
kernel to lower-degree supported cohomology on the full marked base.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/Cylinder/PositiveRestriction.lean`
and `Motivic/Cohomology/A1/Cartier/Restriction/PositiveRestrictionInputs.lean`
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

local instance positiveChartHasExt (S : Scheme.{u}) :
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
  (d : X ⟶ E) (hd : IsPullback d (𝟙 X) b (nativeAffineSection (.of k) X 0))
  (hF : F.obj.IsA1Invariant)
  (K : Type u) [Field K] (c : Spec (.of K) ⟶ X.left) (n : ℕ)
  (hContract : (SheafCohomology.withTransfers k (SheafWithTransfers.contraction F hF)
    (n + 1)).IsA1Invariant)

local notation "G" => Functor.obj (SheafWithTransfers.toSheaf k) F
local notation "E₁" => affineLineCylinder.obj E
local notation "πE" =>
  NatTrans.app (projection (SmoothSite.additiveGroupObject (Spec (CommRingCat.of k)))) E
local notation "j₁" => affineLineCylinder.map j
local notation "Φ" => relativeFieldPoint (c ≫ d.left) K (𝟙 _)

include hD hEpi hj hd hF hContract in
/-- A coefficient kernel class becomes zero on the whole cylinder after
an actual refinement of the original field-valued base mark. -/
theorem exists_pointed_chart_positive_coefficient_kernel_restriction_zero
    (V : (Φ).fiber.Elements)
    (x : (cohomologyPresheaf.{u + 1, u + 1} ((restrict E₁ AddCommGrpCat).obj G)
      (n + 2)).obj (op ((baseChange (πE).left).obj V.obj)))
    (hx : x.comp (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero (n + 2)) = 0) :
    ∃ (W : (Φ).fiber.Elements) (a : W ⟶ V),
      (cohomologyPresheaf.{u + 1, u + 1} ((restrict E₁ AddCommGrpCat).obj G) (n + 2)).map
        ((baseChange (πE).left).map a.hom).op x = 0 := by
  let J := nisnevichTopology (E₁).left
  let r := restrictionToDirectImage G j₁
  let := chartProduct_restrictionToDirectImage_mono hD X b F j q hj hF
  let S := ShortComplex.mk r (cokernel.π r) (cokernel.condition r)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
    ((freeYoneda.{u + 1} J).obj ((baseChange (πE).left).obj V.obj)) hS x hx rfl
  obtain ⟨W, a, ha⟩ := exists_pointed_chartProductSupport_restriction_zero
    X b F j q hj d hd hF
    (contractionToBoundary_epi_of_canonicalBoundaryEpi hEpi (affineLineCylinder.obj X) F hF)
    K c n hContract V y
  refine ⟨W, a, ?_⟩
  rw [← hy, cohomologyPresheaf_map_apply,
    ← Ext.comp_assoc _ _ _ (zero_add (n + 1)) rfl (by omega)]
  change ((cohomologyPresheaf.{u + 1, u + 1}
      (boundaryAmbientCokernel G j₁) (n + 1)).map
      ((baseChange (πE).left).map a.hom).op y).comp hS.extClass rfl = 0
  rw [ha, Ext.zero_comp]

variable (hLow : ∀ m : ℕ, 0 < m → m < n + 2 →
  (SheafCohomology.withTransfers k F m).IsA1Invariant)

include hD hEpi hj hd hF hContract hLow in
/-- A positive puncture-zero representative dies on the original marked base. -/
theorem pointedCylinder_positive_germ_zero_of_chart_puncture_restriction_zero
    (V : (Φ).fiber.Elements)
    (s : (pointedCylinderValues (.of k) (X := E) Φ
      (cohomologyPresheaf.{u + 1, u + 1} G (n + 2)) (pointedBase (.of k) (X := E) Φ)).obj (op V))
    (hs : (pointedCylinderRestriction (.of k) j Φ
      (cohomologyPresheaf.{u + 1, u + 1} G (n + 2))).app (op V) s = 0) :
    colimit.ι (pointedCylinderValues (.of k) (X := E) Φ
      (cohomologyPresheaf.{u + 1, u + 1} G (n + 2))
      (pointedBase (.of k) (X := E) Φ)) (op V) s = 0 := by
  let x := (pointedCylinderOrdinaryIso (.of k) E Φ G (n + 2)).hom.app (op V) s
  have hx : x.comp (Ext.mk₀ (restrictionToDirectImage G j₁)) (add_zero (n + 2)) = 0 := by
    apply pointedCylinder_coefficient_kernel_of_puncture_restriction_zero (.of k) j G
      (n + 2) Φ V _ s hs
    intro m hm hmn
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    exact chartProduct_higherDirectImage_isZero_succ hD hEpi X b F j q hj d hd r
      (hLow (r + 1) (Nat.succ_pos r) hmn)
  obtain ⟨W, a, hz⟩ := exists_pointed_chart_positive_coefficient_kernel_restriction_zero
    hD hEpi X b F j q hj d hd hF K c n hContract V x hx
  exact pointedCylinder_germ_eq_zero_of_ordinary_base_refinement
    (.of k) E Φ G (n + 2) a s hz

include hD hEpi hj hd hF hContract hLow in
/-- The positive-degree puncture map is monic at the unchanged full field-valued mark. -/
theorem pointedCylinderRestriction_positive_colimit_mono_of_chart :
    Mono (colim.map (pointedCylinderRestriction (.of k) j Φ
      (cohomologyPresheaf.{u + 1, u + 1} G (n + 2)))) :=
  pointedCylinderRestriction_colimit_mono_of_local_kernel (.of k) j Φ
    (cohomologyPresheaf.{u + 1, u + 1} G (n + 2))
    (pointedCylinder_positive_germ_zero_of_chart_puncture_restriction_zero
      hD hEpi X b F j q hj d hd hF K c n hContract hLow)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.Boundary
