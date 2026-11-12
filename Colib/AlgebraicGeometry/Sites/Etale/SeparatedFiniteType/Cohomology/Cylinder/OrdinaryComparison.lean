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
`Motivic/Cohomology/A1/LocalVanishing/Cylinder/OrdinaryComparison.lean`, blob
`9869c01b930cc7c89cd0a004e66a114d59653563`.
The comparison is natural on the original marked BASE index, and uses the
actual native additive cylinder. The later higher-image fiber identification
is deliberately not asserted by this lower leaf.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE
section PointBaseChange

variable {R : CommRingCat.{u}} {S : Scheme.{u}} (Y : SmoothSite (Spec R)) (b : Y.left ⟶ S)
  (Φ : (nisnevichTopology S).Point.{u + 1})
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
  [hLarge : HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
  [hSmall : HasExt.{u + 1}
    (Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1})]

/-- The ordinary cohomology comparison on the original point index commutes
with geometric base change. -/
def ordinaryPointBaseChangeIso (n : ℕ) :
    ((Functor.Elements.π Φ.fiber ⋙ baseChange b ⋙ toSmoothSite Y).op ⋙
      cohomologyPresheaf.{u + 1, u + 1} F n) ≅
    @ordinaryPointCohomologyDiagram.{u} S Y.left b Φ
      ((restrict Y AddCommGrpCat.{u + 1}).obj F) hSmall n := by
  refine NatIso.ofComponents (fun V ↦ ?_) ?_
  · exact (@cohomologyRestrictionEquiv.{u + 1, u + 1, u}
      (Spec R) Y hLarge hSmall F n ((baseChange b).obj V.unop.obj)).toAddCommGrpIso
  · intro V W f
    ext x
    exact cohomologyRestrictionEquiv_restriction (B := Spec R) (X := Y) F n
      ((baseChange b).map ((Functor.Elements.π Φ.fiber).map f.unop)) x

/-- An isomorphism of original neighborhood functors transports the ordinary
comparison along the same point index. -/
def ordinaryPointCohomologyIsoOfBaseChange
    {D : Φ.fiber.Elements ⥤ SmoothSite (Spec R)}
    (e : Functor.Elements.π Φ.fiber ⋙ baseChange b ⋙ toSmoothSite Y ≅ D) (n : ℕ) :
    (D.op ⋙ cohomologyPresheaf.{u + 1, u + 1} F n) ≅
      @ordinaryPointCohomologyDiagram.{u} S Y.left b Φ
        ((restrict Y AddCommGrpCat.{u + 1}).obj F) hSmall n :=
  Functor.isoWhiskerRight (NatIso.op e) (cohomologyPresheaf.{u + 1, u + 1} F n) ≪≫
    ordinaryPointBaseChangeIso Y b Φ F n

end PointBaseChange

variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))

variable (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
  [hLarge : HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
  [hSmall : HasExt.{u + 1}
    (Sheaf (nisnevichTopology
      ((SmoothSite.Contraction.affineLineCylinder (S := Spec R)).obj X).left)
      AddCommGrpCat.{u + 1})]

/-- Geometric base change identifies cylinder cohomology with the existing diagram. -/
abbrev pointedCylinderOrdinaryIso (n : ℕ) :=
  let Y : SmoothSite (Spec R) := (SmoothSite.Contraction.affineLineCylinder (S := Spec R)).obj X
  let p : Y.left ⟶ X.left :=
    ((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))).app X).left
  let D : Φ.fiber.Elements ⥤ SmoothSite (Spec R) :=
    pointedBase R (X := X) Φ ⋙ SmoothSite.Contraction.affineLineCylinder
  let e : Functor.Elements.π Φ.fiber ⋙ baseChange p ⋙ toSmoothSite Y ≅ D :=
    Functor.isoWhiskerLeft (Functor.Elements.π Φ.fiber) (a1BaseChangeNatIso R X)
  @ordinaryPointCohomologyIsoOfBaseChange.{u}
    (R := R) (S := X.left) Y p Φ F hLarge hSmall D e n

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
