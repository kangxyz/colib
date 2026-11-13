/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.A1BaseChange
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Boundary.Cokernel
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant


/-! # The original degree-zero projection coefficient isomorphism for HI sheaves -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Sites/FiniteEtaleA1Coefficient.lean`, blob
`d2dd6fd691dc1c847917dad1313d661a1b46fe98`.
Native ordinary coefficient HI gives only the degree-zero projection coefficient isomorphism,
using the existing native A1.IsInvariant and actual cylinder.
Source candidate only; no elaboration result is asserted.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})

local notation "π" =>
  NatTrans.app (SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec R))) X

/-- On each genuine étale test object, the coefficient map is the original A1 projection
followed by restriction along the actual base-change/product comparison. -/
theorem a1RestrictionCoefficient_app (V : EtaleSeparatedFiniteType X.left) :
    (restrictionToDirectImage F π).hom.app (op V) =
      _root_.AlgebraicGeometry.A1.projectionPullback R F.obj ((toSmoothSite X).obj V) ≫
        F.obj.map (a1BaseChangeIso R X V).hom.op := by
  change F.obj.map ((restrictionProjection π).app V).op = _
  rw [← a1BaseChangeIso_hom_projection, op_comp, Functor.map_comp]
  rfl

/-- Original HI supplies the degree-zero sheaf iso, without any inverse-image coefficient iso. -/
theorem a1RestrictionCoefficient_isIso (hF : _root_.AlgebraicGeometry.A1.IsInvariant R F.obj) :
    IsIso (restrictionToDirectImage F π) := by
  have happ (V : (EtaleSeparatedFiniteType X.left)ᵒᵖ) :
      IsIso ((restrictionToDirectImage F π).hom.app V) := by
    let : IsIso (_root_.AlgebraicGeometry.A1.projectionPullback R F.obj
      ((toSmoothSite X).obj V.unop)) := hF _
    change IsIso ((restrictionToDirectImage F π).hom.app (op V.unop))
    rw [a1RestrictionCoefficient_app R X F V.unop]
    infer_instance
  let U := sheafToPresheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1}
  let : IsIso (U.map (restrictionToDirectImage F π)) :=
    (NatTrans.isIso_iff_isIso_app _).mpr happ
  exact isIso_of_reflects_iso (restrictionToDirectImage F π) U

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
