/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.Point.Basic
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ImageAdjunction
public import Mathlib.CategoryTheory.Sites.Point.Comap

/-!
Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Field/Point/InverseImage.lean`,
blob `b7bf564fbdcd976de657151558fad0e06895ab70`.

 # Field evaluation of the genuine small-site inverse image -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : S ⟶ T) (K : Type u) [Field K]
  (q : Spec (.of K) ⟶ S) [Etale q] [IsSeparated q] [QuasiCompact q]

instance relativeFieldPoint_initiallySmall :
    InitiallySmall.{u + 1} (baseChange b ⋙ (fieldPoint K q).fiber).Elements :=
  initiallySmall_of_essentiallySmall _

/-- The actual point induced by field-valued points on base-changed étale neighborhoods. -/
def relativeFieldPoint : (nisnevichTopology T).Point.{u + 1} :=
  (fieldPoint K q).comap (baseChange b)
    (CoverPreserving.of_isContinuous (baseChange b) _ _)

/-- Evaluation of the original inverse image is the original comapped point fiber.
The inverse image is the genuine left adjoint, not naive restriction along `b`. -/
def relativeFieldPointInverseImageIso :
    (relativeFieldPoint b K q).sheafFiber (A := AddCommGrpCat.{u + 1}) ≅
      inverseImage b ⋙ sheafToPresheaf (nisnevichTopology S) AddCommGrpCat.{u + 1} ⋙
        (CategoryTheory.evaluation (EtaleSeparatedFiniteType S)ᵒᵖ AddCommGrpCat.{u + 1}).obj
          (op (fieldObject K q))
            :=
  (fieldPoint K q).sheafFiberComapIso (baseChange b)
      (CoverPreserving.of_isContinuous (baseChange b) _ _) AddCommGrpCat.{u + 1} ≪≫
    Functor.isoWhiskerLeft (inverseImage b) (fieldPointSheafFiberIso K q AddCommGrpCat.{u + 1})

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
