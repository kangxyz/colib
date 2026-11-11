/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Cokernel
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-! # Original restrictions on actual pointed cylinder diagrams

The index is the unchanged native point-neighborhood category.
No global dimension drop on a finite-stage puncture is asserted.
-/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Puncture/PointDiagrams.lean`, blob `dd2775346278c19a5a32ed24c081c7cf0f451835`.
The canonical native objects and displayed maps are retained. Source candidate only.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable (R : CommRingCat.{u}) {X U : SmoothSite (Spec R)} (j : U ⟶ X)
  (Φ : (nisnevichTopology X.left).Point.{u + 1})
  (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1})

/-- The original smooth neighborhood diagram on the existing point index. -/
def pointedBase : Φ.fiber.Elements ⥤ SmoothSite (Spec R) :=
  Functor.Elements.π Φ.fiber ⋙ toSmoothSite X

/-- The actual puncture of every existing point neighborhood, by geometric base change. -/
def pointedPuncture : Φ.fiber.Elements ⥤ SmoothSite (Spec R) :=
  Functor.Elements.π Φ.fiber ⋙ baseChange j.left ⋙ toSmoothSite U

/-- The literal inclusions of pulled-back punctured neighborhoods. -/
def pointedPunctureInclusion : pointedPuncture R j Φ ⟶ pointedBase R Φ :=
  Functor.whiskerLeft (Functor.Elements.π Φ.fiber) (restrictionProjection j)

/-- Original presheaf values on the actual base neighborhoods. -/
def pointedBaseValues : Φ.fiber.Elementsᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (pointedBase R Φ).op ⋙ P

/-- Original presheaf values on the actual punctured neighborhoods. -/
def pointedPunctureValues : Φ.fiber.Elementsᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (pointedPuncture R j Φ).op ⋙ P

/-- Actual original restrictions to the puncture on the same index. -/
def pointedRestriction : pointedBaseValues R Φ P ⟶ pointedPunctureValues R j Φ P :=
  Functor.whiskerRight (NatTrans.op (pointedPunctureInclusion R j Φ)) P

/-- The original cylinder values, on the same pointed-neighborhood index. -/
def pointedCylinderValues (G : Φ.fiber.Elements ⥤ SmoothSite (Spec R)) :
    Φ.fiber.Elementsᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  (G ⋙ SmoothSite.Contraction.affineLineCylinder).op ⋙ P

/-- The actual original cylinder restriction induced by the puncture inclusion. -/
def pointedCylinderRestriction :
    pointedCylinderValues R Φ P (pointedBase R Φ) ⟶
      pointedCylinderValues R Φ P (pointedPuncture R j Φ) :=
  Functor.whiskerRight (NatTrans.op (Functor.whiskerRight
    (pointedPunctureInclusion R j Φ) (SmoothSite.Contraction.affineLineCylinder))) P

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
