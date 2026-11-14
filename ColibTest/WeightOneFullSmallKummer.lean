/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneFullSmallKummer

/-! # The original full-small weight-one comparison is the native Kummer cone comparison -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
universe u w w'
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]


variable (X : SmoothSite (Spec (.of k)))
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'}
  (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CochainComplex.finiteCoefficients

example (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    DerivedCategory.Q.map (weightOneFiniteFullSmallKummerComparison k X n) ≫
      (Stacks.Kummer.kummerSingleFiniteIso X.left n hn
        (by simpa only [map_natCast] using hunit.map X.hom.appTop.hom)).hom =
      (weightOneFiniteFullSmallRootsIso k X n hn hunit).hom :=
  weightOneFiniteFullSmallRootsIso_eq_kummer k X n hn hunit

end AlgebraicGeometry.MotivicCohomology.WeightOne
