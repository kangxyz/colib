/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneIntegralBaseSource
public import Colib.AlgebraicGeometry.EtaleCohomology.KummerSourceEquality
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneIntegralBoundary
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneBaseSource
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.IntegralReductionDerived
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.NormSections

/-! # The original finite weight-one comparison agrees with the original Kummer boundary -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType CochainComplex.finiteCoefficients
open Stacks.Cohomology.FreeYonedaUnivLE Stacks.Cohomology.Corepresented
universe u wN wE wS wH
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable [HasDerivedCategory.{wN}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{wE}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [hSmall : HasDerivedCategory.{wS}
  (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]
variable [HasExt.{wH} (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1})]

@[reducible] local instance : HasDerivedCategory.{wS}
    (Sheaf (base (Spec (.of k))).left.smallEtaleTopology AddCommGrpCat.{u + 1}) := hSmall

local instance : HasExt.{wH}
    (Sheaf (base (Spec (.of k))).left.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  inferInstanceAs (HasExt.{wH}
    (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{u + 1}))

set_option maxHeartbeats 1600000 in
-- The original comparison composes derived functors on three distinct sites.
/-- The original finite comparison on an integral class is its actual unit Kummer class. -/
lemma weightOneFiniteEtaleCohomologyMap_integral_unitKummerClass
    (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : Γ(Spec (.of k), ⊤)))
    (x : motivicCohomology k 1 1 (base (Spec (.of k)))) :
    weightOneFiniteEtaleCohomologyMap k (base (Spec (.of k))) 1 n hn hunit
      (motivicBaseIntegralReduction k 1 1 n x) =
    Stacks.Kummer.unitKummerClass.{wH, u, 0} (Spec (.of k)) hn hunit
      ((shiftedUnitsBaseHomologyIso k).hom
        (hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) 1
          (derivedWeightOneComparison k 1 x))).down := by
  let s := (shiftedUnitsBaseHomologyIso k).hom
    (hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) 1
      (derivedWeightOneComparison k 1 x))
  have hs := weightOneFullSmallIntegralBase_source k x
  have ht := Stacks.Kummer.terminalDerived_unitKummerClass_of_source_eq
    (Spec (.of k)) n hn hunit s.down _ hs
  rw [motivicBaseIntegralReduction_eq_postcompose,
    weightOneFiniteEtaleCohomologyMap_integral_boundary]
  simp only [Category.assoc] at ht
  convert ht using 1; rfl

/-- The actual finite comparison uses the existing geometric norm and the original Kummer class. -/
lemma weightOneFiniteEtaleCohomologyMap_integral_norm
    (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : Γ(Spec (.of k), ⊤)))
    (x : motivicCohomology k 1 1 (base (Spec (.of k)))) :
    weightOneFiniteEtaleCohomologyMap k (base (Spec (.of k))) 1 n hn hunit
      (motivicBaseIntegralReduction k 1 1 n x) =
    Stacks.Kummer.unitKummerClass.{wH, u, 0} (Spec (.of k)) hn hunit
      (Additive.ofMul (specGlobalUnit (motivicNorm k x).toMul)) := by
  rw [weightOneFiniteEtaleCohomologyMap_integral_unitKummerClass,
    derivedWeightOneComparison_globalUnit]

end AlgebraicGeometry.MotivicCohomology.WeightOne
