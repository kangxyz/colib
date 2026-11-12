/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Germs.Envelope.Acyclic
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.CohomologyComparison
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ImageExact
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Injectives
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import StacksFrontier.Algebra.Homology.DerivedCategory.HasRightDerivedFunctorPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitHelpers
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE
import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.AbelianHigherDirectImageSheafification

/-! # Small-site torus direct image of a transfer injective -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE
open Stacks.Cohomology.SheafifiedHigherDirectImage

universe u

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S

variable [HasExt.{u + 1}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- On the small Nisnevich site, the underlying transfer injective is
acyclic for sections over every actual neighborhood. -/
theorem restricted_injective_cohomology_isZero (I : SheafWithTransfers.{u + 1} k)
    [Injective I] (Y : SmoothSite S) (n : ℕ) (V : EtaleSeparatedFiniteType Y.left) :
    let R := EtaleSeparatedFiniteType.restrict Y AddCommGrpCat.{u + 1}
    let JY := EtaleSeparatedFiniteType.nisnevichTopology Y.left
    IsZero ((((sheafSections JY AddCommGrpCat.{u + 1}).obj (op V)).rightDerived (n + 1)).obj
      (R.obj ((toSheaf k).obj I))) := by
  let JY := EtaleSeparatedFiniteType.nisnevichTopology Y.left
  let FY := (EtaleSeparatedFiniteType.restrict Y AddCommGrpCat.{u + 1}).obj ((toSheaf k).obj I)
  let : HasExt.{u + 1} (Sheaf JY AddCommGrpCat.{u + 1}) := hasExt_of_enoughInjectives _
  let e := EtaleSeparatedFiniteType.cohomologyRestrictionEquiv Y ((toSheaf k).obj I) (n + 1) V
  let j := cohomologyPresheafObjIsoRightDerivedSections.{u + 1} JY FY (n + 1) V
  apply AddCommGrpCat.isZero_iff_subsingleton.2
  refine ⟨fun a b => (e.trans j.addCommGroupIsoToAddEquiv).symm.injective ?_⟩
  exact (injective_underlying_H_succ_eq_zero k I ((EtaleSeparatedFiniteType.toSmoothSite Y).obj V)
    n ((e.trans j.addCommGroupIsoToAddEquiv).symm a)).trans
      (injective_underlying_H_succ_eq_zero k I ((EtaleSeparatedFiniteType.toSmoothSite Y).obj V)
        n ((e.trans j.addCommGroupIsoToAddEquiv).symm b)).symm

/-- The actual small-site torus projection has no higher direct images
on the restriction of a transfer injective. -/
theorem restricted_injective_directImage_rightAcyclic
    (I : SheafWithTransfers.{u + 1} k) [Injective I] (X : SmoothSite S)
    [HasDerivedCategory (Sheaf (EtaleSeparatedFiniteType.nisnevichTopology X.left)
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (EtaleSeparatedFiniteType.nisnevichTopology
      (SmoothSite.product X G).left) AddCommGrpCat.{u + 1})] :
    let Y := SmoothSite.product X G
    let p := (SmoothSite.productFst X G).left
    (EtaleSeparatedFiniteType.directImage p).rightAcyclic
      ((EtaleSeparatedFiniteType.restrict Y AddCommGrpCat.{u + 1}).obj ((toSheaf k).obj I)) := by
  let Y := SmoothSite.product X G
  let p := (SmoothSite.productFst X G).left
  let JX := EtaleSeparatedFiniteType.nisnevichTopology X.left
  let JY := EtaleSeparatedFiniteType.nisnevichTopology Y.left
  let FY := (EtaleSeparatedFiniteType.restrict Y AddCommGrpCat.{u + 1}).obj ((toSheaf k).obj I)
  let q := EtaleSeparatedFiniteType.baseChange p
  let A := AddCommGrpCat.{u + 1}
  let : q.IsContinuous JX JY := EtaleSeparatedFiniteType.baseChange_isContinuous p
  apply (CategoryTheory.rightAcyclic_iff_isZero_rightDerived
    (EtaleSeparatedFiniteType.directImage p) FY).2
  intro m hm
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  let D := pushforwardCohomologyPresheaf (K := JY) A q
  have hD : IsZero ((D.rightDerived (n + 1)).obj FY) := (Functor.isZero_iff _).2 (by
    intro V
    let e := (pushforwardCohomologyPresheafEvaluationIso A q (n + 1) V.unop).app FY
    exact (restricted_injective_cohomology_isZero k I Y n (q.obj V.unop)).of_iso e.symm)
  exact ((presheafToSheaf JX A).map_isZero hD).of_iso
    ((rightDerivedPushforwardIso A q (n + 1)).app FY)

end AlgebraicGeometry.SheafWithTransfers
