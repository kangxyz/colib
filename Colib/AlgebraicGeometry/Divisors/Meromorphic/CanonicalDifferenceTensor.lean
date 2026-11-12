/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalDifferenceRegular
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CanonicalBoundaryEvaluation

/-!
# The canonical difference as an original pure tensor

The Cartier evaluation isomorphism cancels a local ideal section with ambient
value one against the original canonical positive section. This identifies the
ordinary canonical difference with a pure tensor, before any boundary pullback.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Invertible

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D E : X.IdealSheafData)
  [IsEffectiveCartierDivisor D] [IsEffectiveCartierDivisor E]

omit [IsEffectiveCartierDivisor D] in
/-- Cartier evaluation cancels the original ideal's section one. -/
theorem differenceSheafTensorPositiveIso_tensor_one (U : X.Opens)
    (a : Γ(divisorSheaf D, U)) (b : Γ(negativeTwist' E, U))
    (hb : idealSheafSection E b = (1 : Γ(X, U))) :
    (differenceSheafTensorPositiveIso D E).hom.app U
      (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
        (differenceSheaf D E) (divisorSheaf E)
        (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
          (divisorSheaf D) (negativeTwist' E) a b)
        ((canonicalSection' E).eval (op U))) = a := by
  have := isTensorInvertible_negativeTwist E
  let F := divisorSheaf D
  let G := negativeTwist' E
  let H := divisorSheaf E
  let e := Stacks.SheafOfModules.tensorSheafBraiding X.sheaf.obj
    X.ringCatSheaf.property G H ≪≫ Stacks.SheafOfModules.Scheme.evaluationIso X G
  change (tensorProductRightUnitor X.sheaf.obj X.ringCatSheaf.property F).hom.val.app (op U)
    ((tensorProductIso X.sheaf.obj X.ringCatSheaf.property (Iso.refl F) e).hom.val.app (op U)
      ((tensorProductAssociator X.sheaf.obj X.ringCatSheaf.property F G H).hom.val.app (op U)
        _)) = a
  refine (congrArg (fun z =>
    (tensorProductRightUnitor X.sheaf.obj X.ringCatSheaf.property F).hom.val.app (op U)
      ((tensorProductIso X.sheaf.obj X.ringCatSheaf.property (Iso.refl F) e).hom.val.app
        (op U) z))
    (Stacks.SheafOfModules.tensorSections_associatorAt X.sheaf.obj X.ringCatSheaf.property
      (op U) F G H a b ((canonicalSection' E).eval (op U)))).trans ?_
  refine (congrArg
    ((tensorProductRightUnitor X.sheaf.obj X.ringCatSheaf.property F).hom.val.app (op U))
    (Stacks.SheafOfModules.tensorSections_tensorProductIsoAt X.sheaf.obj
      X.ringCatSheaf.property (op U) _ _ _ _ (Iso.refl F) e a _)).trans ?_
  have he : e.hom.val.app (op U)
      (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
        G H b ((canonicalSection' E).eval (op U))) = (1 : Γ(X, U)) := by
    change (Stacks.SheafOfModules.Scheme.evaluationIso X G).hom.val.app (op U)
      ((Stacks.SheafOfModules.tensorSheafBraiding
        X.sheaf.obj X.ringCatSheaf.property G H).hom.val.app (op U) _) = _
    refine (congrArg ((Stacks.SheafOfModules.Scheme.evaluationIso X G).hom.val.app (op U))
      (Stacks.SheafOfModules.tensorSections_braidingAt X.sheaf.obj X.ringCatSheaf.property
        (op U) G H b ((canonicalSection' E).eval (op U)))).trans ?_
    exact (Stacks.SheafOfModules.evaluation_tensorPt X.presheaf X.ringCatSheaf.property
      G (op U) ((canonicalSection' E).eval (op U)) b).trans hb
  refine (congrArg (fun z =>
    (tensorProductRightUnitor X.sheaf.obj X.ringCatSheaf.property F).hom.val.app (op U)
      (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
        F (SheafOfModules.unit X.ringCatSheaf) a z)) he).trans ?_
  exact Stacks.SheafOfModules.tensorSections_rightUnitorAt X.sheaf.obj
    X.ringCatSheaf.property (op U) F a

omit [IsEffectiveCartierDivisor D] in
/-- After local cancellation, the ordinary quotient is the literal tensor of the
positive canonical section and the original ideal section one. -/
theorem regularCanonicalQuotient_eq_tensor (U : X.Opens)
    [IsIso (((divisorSheaf E).unitHomEquiv.symm (canonicalSection' E)).over U)]
    (b : Γ(negativeTwist' E, U)) (hb : idealSheafSection E b = (1 : Γ(X, U))) :
    Scheme.Modules.regularTensorQuotientOnOpen X (differenceSheaf D E) (divisorSheaf E)
      (canonicalSection' E) U
      ((Scheme.Modules.tensorObj (differenceSheaf D E) (divisorSheaf E)).presheaf.map
        (homOfLE le_top).op (canonicalDifferenceGlobalNumerator D E)) =
    Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
      (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) b := by
  let e := Scheme.Modules.tensorSectionQuotientIsoOver X (differenceSheaf D E)
    (divisorSheaf E) (canonicalSection' E) U
  let a := (Scheme.Modules.tensorObj (differenceSheaf D E) (divisorSheaf E)).presheaf.map
    (homOfLE (le_top : U ≤ ⊤)).op (canonicalDifferenceGlobalNumerator D E)
  let m := Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
    (divisorSheaf D) (negativeTwist' E) ((canonicalSection' D).eval (op U)) b
  have hleft : Function.LeftInverse (e.hom.val.app (op (Over.mk (𝟙 U))))
      (e.inv.val.app (op (Over.mk (𝟙 U)))) := fun z =>
    congrArg (fun f => f.val.app (op (Over.mk (𝟙 U))) z) e.inv_hom_id
  have hnum : (differenceSheafTensorPositiveIso D E).hom.app U a =
      (canonicalSection' D).eval (op U) := by
    refine (PresheafOfModules.naturality_apply (differenceSheafTensorPositiveIso D E).hom.val
      (homOfLE (le_top : U ≤ ⊤)).op (canonicalDifferenceGlobalNumerator D E)).trans ?_
    have htop : (differenceSheafTensorPositiveIso D E).hom.app ⊤
        (canonicalDifferenceGlobalNumerator D E) = divisorSheafGlobalSection D :=
      congrArg (fun f => f.val.app (op (⊤ : X.Opens)) (divisorSheafGlobalSection D))
        (differenceSheafTensorPositiveIso D E).inv_hom_id
    exact (congrArg ((divisorSheaf D).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op) htop).trans
      ((canonicalSection' D).property (homOfLE (le_top : U ≤ ⊤)).op)
  have ht : Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property
      (op U) (differenceSheaf D E) (divisorSheaf E) m
      ((canonicalSection' E).eval (op U)) = a :=
    injective_iso_hom_val_app (differenceSheafTensorPositiveIso D E) (op U)
      ((differenceSheafTensorPositiveIso_tensor_one D E U _ b hb).trans hnum.symm)
  have hinv : e.inv.val.app (op (Over.mk (𝟙 U))) m = a :=
    (Scheme.Modules.tensorSectionQuotientIsoOver_inv_apply X (differenceSheaf D E)
      (divisorSheaf E) (canonicalSection' E) U m).trans ht
  exact (congrArg (e.hom.val.app (op (Over.mk (𝟙 U)))) hinv).symm.trans (hleft m)

end Stacks.Divisors
