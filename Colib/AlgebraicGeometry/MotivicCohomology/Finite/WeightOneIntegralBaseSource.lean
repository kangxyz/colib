/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneIntegralSource
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneBaseSource
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.ComparisonPostcompose

/-! # The original integral weight-one source on the full small site -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType CochainComplex.finiteCoefficients
open Stacks.Cohomology.FreeYonedaUnivLE Stacks.Cohomology.Corepresented
universe u wN wE wS
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
/-- Reuse the given small-etale derived category at the definitional base object. -/
@[reducible] local instance weightOneIntegralBaseSourceSmallDerived : HasDerivedCategory.{wS}
    (Sheaf (base (Spec (.of k))).left.smallEtaleTopology AddCommGrpCat.{u + 1}) := hSmall

/-- The original integral comparison at the base point is its original unit section. -/
lemma weightOneFullSmallIntegralBase_source
    (x : motivicCohomology k 1 1 (base (Spec (.of k)))) :
    fullSmallDerivedHomMapAtBase (base (Spec (.of k))) (motivicEtaleSheafComplex k 1) 1
        (nisnevichToEtaleDerivedHomMap (Spec (.of k)) (base (Spec (.of k)))
          (motivicSheafComplex k 1) 1 x) ≫
      (DerivedCategory.Q.map
        (((fullSmallEtaleRestrict (base (Spec (.of k)))).mapHomologicalComplex (.up ℤ)).map
          (weightOneEtaleSheafComparison k)))⟦(1 : ℤ)⟧' ≫
      (DerivedCategory.Q.map
        (fullSmallEtaleUnitsComplexIso k (base (Spec (.of k)))).hom)⟦(1 : ℤ)⟧' ≫
      (derivedSingleNegOneCancelIso
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} (base (Spec (.of k))).left)).hom =
    (DerivedCategory.singleFunctor _ 0).map
      ((sectionsEquiv.{u + 1} (Scheme.Etale.mk (𝟙 (Spec (.of k))))
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} (Spec (.of k)))).symm
        (ULift.up ((shiftedUnitsBaseHomologyIso k).hom
          (hypercohomologyBaseFieldAddEquiv k (shiftedUnitsSheafComplex k) 1
            (derivedWeightOneComparison k 1 x))).down)) := by
  let X := base (Spec (.of k))
  let z := derivedWeightOneComparison k 1 x
  have hz : x ≫ (DerivedCategory.Q.map (weightOneSheafComparison k))⟦(1 : ℤ)⟧' = z :=
    (derivedWeightOneComparison_eq_postcompose k 1 x).symm
  have hc := weightOneFullSmallIntegralSource k X 1 x
  rw [hz] at hc
  let tail := (DerivedCategory.Q.map (fullSmallEtaleUnitsComplexIso k X).hom)⟦(1 : ℤ)⟧' ≫
    (derivedSingleNegOneCancelIso (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left)).hom
  have ht := congrArg (fun f => f ≫ tail) hc
  have hb := weightOneBaseFullSmall_source k z
  calc
    _ = fullSmallDerivedHomMapAtBase X (weightOneEtaleUnitsComplex k) 1
        (nisnevichToEtaleDerivedHomMap (Spec (.of k)) X (weightOneUnitsComplex k) 1 z ≫
          (DerivedCategory.Q.map (weightOneUnitsChangeOfTopologyIso k).hom)⟦(1 : ℤ)⟧') ≫
        tail := by simpa only [X, tail, Category.assoc] using ht
    _ = _ := by convert hb using 1 <;> rfl

end AlgebraicGeometry.MotivicCohomology.WeightOne
