/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.PointDiagrams
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.PointDiagram
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.A1BaseChangeNaturality
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Original.MapAtBase

/-! # The pointed cylinder diagram retains actual big/small ordinary restrictions -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Cylinder/OrdinaryComparison.lean`, blob `9869c01b930cc7c89cd0a004e66a114d59653563`.
The comparison is natural on the original marked BASE index, and uses the
actual native additive cylinder. The later higher-image fiber identification
is deliberately not asserted by this lower leaf.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
  (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X).left) AddCommGrpCat.{u + 1})]

/-- The original big/small comparison is natural on the exact existing point-neighborhood index. -/
def pointedCylinderBaseChangeOrdinaryIso (n : ℕ) :
    ((Functor.Elements.π Φ.fiber ⋙ baseChange ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app X).left ⋙
      toSmoothSite (SmoothSite.Contraction.affineLineCylinder.obj X)).op ⋙
        cohomologyPresheaf.{u + 1, u + 1} F n) ≅
    ordinaryPointCohomologyDiagram ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app X).left Φ
      (F := (restrict (SmoothSite.Contraction.affineLineCylinder.obj X) AddCommGrpCat).obj F) n :=
  NatIso.ofComponents (fun V =>
    (cohomologyRestrictionEquiv (SmoothSite.Contraction.affineLineCylinder.obj X) F n
      ((baseChange ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app X).left).obj V.unop.obj)).toAddCommGrpIso) (by
    intro V W f
    ext x
    exact cohomologyRestrictionEquiv_restriction F n
      ((baseChange ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app X).left).map
        ((Functor.Elements.π Φ.fiber).map f.unop)) x)

/-- Geometric base change identifies cylinder cohomology with the existing diagram. -/
def pointedCylinderOrdinaryIso (n : ℕ) :
    pointedCylinderValues R Φ
      (cohomologyPresheaf.{u + 1, u + 1} F n) (pointedBase R Φ) ≅
      ordinaryPointCohomologyDiagram ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app X).left Φ
        (F := (restrict (SmoothSite.Contraction.affineLineCylinder.obj X) AddCommGrpCat).obj F) n :=
  Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerLeft (Functor.Elements.π Φ.fiber)
    (a1BaseChangeNatIso R X))) _ ≪≫ pointedCylinderBaseChangeOrdinaryIso R X Φ F n

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
