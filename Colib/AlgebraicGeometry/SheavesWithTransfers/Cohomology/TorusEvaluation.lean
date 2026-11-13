/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Representable
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsFunctor

/-! # The original represented evaluation of torus sections -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "J" => SmoothSite.nisnevichTopology S

/-- The actual torus functor on underlying ordinary Nisnevich sheaves. -/
abbrev ordinaryTorusSectionsFunctor :
    Sheaf J AddCommGrpCat.{u + 1} ⥤ Sheaf J AddCommGrpCat.{u + 1} :=
  (SmoothSite.Contraction.parameterProduct G).sheafPushforwardContinuous _ J J

/-- Forgetting transfers gives the same torus restrictions on every
original smooth graph. -/
def torusSectionsToSheafIso :
    torusSectionsFunctor k ⋙ toSheaf k ≅ toSheaf k ⋙ ordinaryTorusSectionsFunctor k :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (PresheafWithTransfers.withParameterUnderlyingIso F.obj G))
    (fun f => by
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext X
      rfl)

/-- The actual evaluation functor represented by the sheafified transfer representable. -/
abbrev transferEvaluationFunctor (X : SmoothSite S) :
    SheafWithTransfers.{u + 1} k ⥤ AddCommGrpCat.{u + 1} :=
  preadditiveCoyoneda.obj (op ((transferRepresentable k).obj (Cor.mk X)))

/-- The exact degree-zero comparison for evaluation on the torus product. -/
def torusSectionsTransferEvaluationIso (X : SmoothSite S) :
    torusSectionsFunctor k ⋙ transferEvaluationFunctor k X ≅
      transferEvaluationFunctor k (SmoothSite.product X G) := by
  let Y := SmoothSite.product X G
  let B := torusSectionsFunctor k
  let E (I : SheafWithTransfers.{u + 1} k) :=
    (transferSectionsEquiv k (Cor.mk X) (B.obj I)).trans (transferSectionsEquiv k (Cor.mk Y) I).symm
  refine NatIso.ofComponents (fun I => (E I).toAddCommGrpIso) ?_
  intro I I' f
  ext a
  change E I' (a ≫ B.map f) = E I a ≫ f
  apply (transferSectionsEquiv k (Cor.mk Y) I').injective
  change (transferSectionsEquiv k (Cor.mk Y) I')
      ((transferSectionsEquiv k (Cor.mk Y) I').symm
        (transferSectionsEquiv k (Cor.mk X) (B.obj I') (a ≫ B.map f))) =
    transferSectionsEquiv k (Cor.mk Y) I' (E I a ≫ f)
  rw [AddEquiv.apply_symm_apply, transferSectionsEquiv_comp, transferSectionsEquiv_comp]
  change f.hom.hom.app (op (Cor.mk Y)) (transferSectionsEquiv k (Cor.mk X) (B.obj I) a) =
    f.hom.hom.app (op (Cor.mk Y)) (transferSectionsEquiv k (Cor.mk Y) I (E I a))
  exact congrArg (f.hom.hom.app (op (Cor.mk Y)))
    ((transferSectionsEquiv k (Cor.mk Y) I).apply_symm_apply _).symm

end AlgebraicGeometry.SheafWithTransfers
