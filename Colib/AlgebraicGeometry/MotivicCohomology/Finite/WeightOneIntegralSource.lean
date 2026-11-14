/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneEtaleKernel
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.DerivedNaturality
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.DerivedRestrictionAtBaseNaturality

/-! # The actual weight-one coefficient comparison commutes with source transport -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
universe u wN wE wS
namespace AlgebraicGeometry.MotivicCohomology.WeightOne
variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory.{wN}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{wE}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The original étale weight-one coefficient map transports the original Nisnevich source. -/
lemma weightOneEtaleSheafComparison_source (X : SmoothSite (Spec (.of k))) (p : ℤ)
    (x : motivicCohomology k p 1 X) :
    nisnevichToEtaleDerivedHomMap (Spec (.of k)) X (motivicSheafComplex k 1) p x ≫
        (DerivedCategory.Q.map (weightOneEtaleSheafComparison k))⟦p⟧' =
      nisnevichToEtaleDerivedHomMap (Spec (.of k)) X (weightOneUnitsComplex k) p
        (x ≫ (DerivedCategory.Q.map (weightOneSheafComparison k))⟦p⟧') ≫
          (DerivedCategory.Q.map (weightOneUnitsChangeOfTopologyIso k).hom)⟦p⟧' := by
  have hN := nisnevichToEtaleDerivedHomMap_coefficient (Spec (.of k)) X
    (weightOneSheafComparison k) p x
  simpa only [weightOneEtaleSheafComparison, weightOneUnitsComplex,
    Functor.map_comp, Category.assoc] using
    congrArg (fun f => f ≫
      (DerivedCategory.Q.map (weightOneUnitsChangeOfTopologyIso k).hom)⟦p⟧') hN.symm

variable (X : SmoothSite (Spec (.of k)))
variable [HasDerivedCategory.{wS} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The actual full-small coefficient map preserves the original weight-one source morphism. -/
lemma weightOneFullSmallIntegralSource (p : ℤ) (x : motivicCohomology k p 1 X) :
    fullSmallDerivedHomMapAtBase X (motivicEtaleSheafComplex k 1) p
        (nisnevichToEtaleDerivedHomMap (Spec (.of k)) X (motivicSheafComplex k 1) p x) ≫
      (DerivedCategory.Q.map
        (((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).map
          (weightOneEtaleSheafComparison k)))⟦p⟧' =
    fullSmallDerivedHomMapAtBase X (weightOneEtaleUnitsComplex k) p
      (nisnevichToEtaleDerivedHomMap (Spec (.of k)) X (weightOneUnitsComplex k) p
        (x ≫ (DerivedCategory.Q.map (weightOneSheafComparison k))⟦p⟧') ≫
          (DerivedCategory.Q.map (weightOneUnitsChangeOfTopologyIso k).hom)⟦p⟧') := by
  have hc := fullSmallDerivedHomMapAtBase_coefficient X (weightOneEtaleSheafComparison k) p
    (nisnevichToEtaleDerivedHomMap (Spec (.of k)) X (motivicSheafComplex k 1) p x)
  calc
    _ = fullSmallDerivedHomMapAtBase X (weightOneEtaleUnitsComplex k) p
        (nisnevichToEtaleDerivedHomMap (Spec (.of k)) X (motivicSheafComplex k 1) p x ≫
          (DerivedCategory.Q.map (weightOneEtaleSheafComparison k))⟦p⟧') := by
      simpa only [motivicEtaleSheafComplex] using hc.symm
    _ = _ := congrArg (fullSmallDerivedHomMapAtBase X (weightOneEtaleUnitsComplex k) p)
      (weightOneEtaleSheafComparison_source k X p x)

end AlgebraicGeometry.MotivicCohomology.WeightOne
