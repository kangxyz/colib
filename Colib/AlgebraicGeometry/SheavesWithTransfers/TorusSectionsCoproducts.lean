/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.EnoughInjectives
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsFunctor
import Colib.AlgebraicGeometry.SheavesWithTransfers.UnderlyingExactness
import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.CoproductSections

/-!
# Direct sums of torus sections with transfers

Smooth Nisnevich sections preserve direct sums. Evaluation on each
actual smooth torus product then shows that torus reindexing preserves
direct sums of Nisnevich sheaves with transfers.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]

/-- Forgetting the transfer-sheaf condition preserves direct sums of
the original transfer presheaves. -/
theorem forget_preservesCoproducts (I : Type w)
    [HasColimitsOfShape (Discrete I) AddCommGrpCat.{u + 1}] :
    PreservesColimitsOfShape (Discrete I) (SheafWithTransfers.forget.{u + 1} k) := by
  let A := AddCommGrpCat.{u + 1}
  let U : SheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
    SheafWithTransfers.forget k
  let V : PresheafWithTransfers.{u + 1} k ⥤ (Cor k)ᵒᵖ ⥤ A :=
    PresheafWithTransfers.forget
  let : ReflectsColimitsOfShape (Discrete I) V := by
    let e := ObjectProperty.fullyFaithfulι (additiveFunctor (Cor k)ᵒᵖ A)
    let : V.Full := e.full
    let : V.Faithful := e.faithful
    exact (fullyFaithful_reflectsColimits V).reflectsColimitsOfShape
  let F := U ⋙ V
  let : PreservesColimitsOfShape (Discrete I) F := by
    refine preservesColimitsOfShape_of_evaluation F (Discrete I) (fun X => ?_)
    let J := SmoothSite.nisnevichTopology (Spec (.of k))
    let E := (sheafSections J A).obj (op X.unop.toSmoothSite)
    let : PreservesColimitsOfShape (Discrete I) E :=
      SmoothSite.nisnevichSheafSections_preservesCoproducts X.unop.toSmoothSite I
    change PreservesColimitsOfShape (Discrete I) (toSheaf k ⋙ E)
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves U V

/-- Actual torus reindexing on Nisnevich sheaves with transfers preserves
direct sums. -/
theorem torusSectionsFunctor_preservesCoproducts (I : Type w)
    [HasColimitsOfShape (Discrete I) AddCommGrpCat.{u + 1}]
    [HasColimitsOfShape (Discrete I) (SheafWithTransfers.{u + 1} k)] :
    PreservesColimitsOfShape (Discrete I)
      (torusSectionsFunctor k : SheafWithTransfers.{u + 1} k ⥤ _) := by
  let A := AddCommGrpCat.{u + 1}
  let U : SheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k :=
    SheafWithTransfers.forget k
  let V : PresheafWithTransfers.{u + 1} k ⥤ (Cor k)ᵒᵖ ⥤ A :=
    PresheafWithTransfers.forget
  let H := U ⋙ V
  let R : SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k :=
    torusSectionsFunctor k
  let G := SmoothSite.multiplicativeGroupObject (Spec (.of k))
  let W := (Functor.whiskeringLeft _ _ A).obj (Cor.parameterProduct G).op
  let : PreservesColimitsOfShape (Discrete I) U := forget_preservesCoproducts k I
  let e : H.FullyFaithful :=
    (ObjectProperty.fullyFaithfulι (PresheafWithTransfers.IsNisnevichSheaf k)).comp
      (ObjectProperty.fullyFaithfulι (additiveFunctor (Cor k)ᵒᵖ A))
  let : H.Full := e.full
  let : H.Faithful := e.faithful
  let : ReflectsColimitsOfShape (Discrete I) H :=
    (fullyFaithful_reflectsColimits H).reflectsColimitsOfShape
  let : PreservesColimitsOfShape (Discrete I) (R ⋙ H) := by
    change PreservesColimitsOfShape (Discrete I) (H ⋙ W)
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves R H

end AlgebraicGeometry.SheafWithTransfers
