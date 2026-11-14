/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneFullSmallKummer

/-! # The original finite full-small weight-one comparison retains integral reduction -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType CochainComplex.finiteCoefficients
universe u
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

/-- The existing finite étale comparison retains the original integral reduction. -/
@[reassoc]
lemma weightOneFiniteEtaleSheafComparison_integral (n : ℕ) :
    ((nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1}).mapHomologicalComplex
      (.up ℤ)).map (integral (motivicSheafComplex k 1) n) ≫
      weightOneFiniteEtaleSheafComparison k n =
    weightOneEtaleSheafComparison k ≫ integral (weightOneEtaleUnitsComplex k) n := by
  unfold weightOneFiniteEtaleSheafComparison
  rw [← Category.assoc, motivicFiniteEtaleSheafComplexIso_integral]
  exact integral_naturality n (weightOneEtaleSheafComparison k)

/-- The original full-small finite comparison retains actual reduction into the small units cone. -/
@[reassoc]
lemma weightOneFiniteFullSmallKummerComparison_integral
    (X : SmoothSite (Spec (.of k))) (n : ℕ) :
    ((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).map
      (((nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1}).mapHomologicalComplex
        (.up ℤ)).map (integral (motivicSheafComplex k 1) n)) ≫
      weightOneFiniteFullSmallKummerComparison k X n =
    ((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).map
      (weightOneEtaleSheafComparison k) ≫ (fullSmallEtaleUnitsComplexIso k X).hom ≫
      integral (((HomologicalComplex.single _ (.up ℤ) 0).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} X.left))⟦(-1 : ℤ)⟧) n := by
  unfold weightOneFiniteFullSmallKummerComparison
  rw [← Functor.map_comp_assoc, weightOneFiniteEtaleSheafComparison_integral]
  rw [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (mapIso_integral (fullSmallEtaleRestrict X) (weightOneEtaleUnitsComplex k) n)]
  rw [integral_naturality]

end AlgebraicGeometry.MotivicCohomology.WeightOne
