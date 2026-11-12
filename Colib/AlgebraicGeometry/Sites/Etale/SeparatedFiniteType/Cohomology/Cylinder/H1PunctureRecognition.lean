/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.EdgeWindow
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.OrdinaryComparison
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.A1PunctureBaseChange

/-!
# The literal H1 puncture kernel in native ordinary coordinates

Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Cylinder/H1ChartVanishing.lean`,
blob `7a0194ccd6de70359095e949bd15f6462ffc9bb6`.

This extracts the actual edge-injection and geometric puncture triangle from
pointedCylinder_H1_germ_zero_of_chart_puncture_restriction_zero. Neither the
chart quotient lift nor coefficient restriction monicity is needed for this
kernel-recognition step. The actual ordinary H1 edge has an empty positive
lower-degree window. No current-degree invariance or puncture monomorphism
is assumed. The final coefficient-kernel effacement is a separate step.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open Stacks.Cohomology.FreeYonedaUnivLE

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

/-- The ordinary H1 restriction kernel maps into the literal coefficient kernel,
using the genuine counit edge rather than an assumed cohomology comparison. -/
theorem H1_coefficient_kernel_of_original_restriction_zero
    {B : Scheme.{u}} [IsAffine B] {Y U : SmoothSite B} (j : U ⟶ Y)
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf (nisnevichTopology U.left) AddCommGrpCat.{u + 1})]
    (V : EtaleSeparatedFiniteType Y.left)
    (x : (cohomologyPresheaf.{u + 1, u + 1} F 1).obj (op ((toSmoothSite Y).obj V)))
    (hx : (cohomologyPresheaf.{u + 1, u + 1} F 1).map
      ((restrictionProjection j).app V).op x = 0) :
    (cohomologyRestrictionEquiv Y F 1 V x).comp
      (Ext.mk₀ (restrictionToDirectImage F j)) (add_zero 1) = 0 := by
  apply ordinaryEdgeMap_one_injective j.left V ((restrict U AddCommGrpCat).obj F)
  rw [map_zero]
  have he := ordinaryEdgeMap_restrictionToDirectImage j F 1 V x
  rw [hx, map_zero] at he
  exact he

/-- The original marked-cylinder puncture-zero representative has zero image
under the actual coefficient restriction after the genuine base-change comparison. -/
theorem pointedCylinder_H1_coefficient_kernel_of_puncture_restriction_zero
    (R : CommRingCat.{u}) {E U : SmoothSite (Spec R)} (j : U ⟶ E)
    (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
    [HasExt.{u + 1}
      (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj E).left)
        AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf
      (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj U).left)
        AddCommGrpCat.{u + 1})]
    (Φ : (nisnevichTopology E.left).Point.{u + 1}) (V : Φ.fiber.Elements)
    (s : (pointedCylinderValues R Φ (cohomologyPresheaf.{u + 1, u + 1} F 1)
      (pointedBase R Φ)).obj (op V))
    (hs : (pointedCylinderRestriction R j Φ
      (cohomologyPresheaf.{u + 1, u + 1} F 1)).app (op V) s = 0) :
    ((pointedCylinderOrdinaryIso R E Φ F 1).hom.app (op V) s).comp
      (Ext.mk₀ (restrictionToDirectImage F
        (SmoothSite.Contraction.affineLineCylinder.map j))) (add_zero 1) = 0 := by
  let P := cohomologyPresheaf.{u + 1, u + 1} F 1
  let π := (SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app E
  let j₁ := SmoothSite.Contraction.affineLineCylinder.map j
  let V₁ := (baseChange π.left).obj V.obj
  let t := P.map (a1BaseChangeIso R E V.obj).hom.op s
  have ht : P.map ((restrictionProjection j₁).app V₁).op t = 0 := by
    change P.map ((restrictionProjection j₁).app V₁).op
      (P.map (a1BaseChangeIso R E V.obj).hom.op s) = 0
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      a1PunctureProjectionBaseChangeIso_restriction]
    change P.map (SmoothSite.Contraction.affineLineCylinder.map
      ((restrictionProjection j).app V.obj)).op s = 0 at hs
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    erw [hs]
    simp only [map_zero]
  exact H1_coefficient_kernel_of_original_restriction_zero j₁ F V₁ t ht

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
