/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneEtaleKernel
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.Units
/-! # Actual full-small weight-one roots-of-unity comparison -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers
open AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
attribute [instance] CategoryTheory.sheafIsAbelian
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

/-- The literal restricted motivic complex, compared with existing small-site μ_n.
This result is in D(Ab), not in D(Z/n). -/
@[colib_tag "COL-1231", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:39-132" "ingredient"
  "Exact full-small restriction of the weight-one kernel comparison to the existing mu_n"]
def weightOneFiniteFullSmallRootsIso (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    DerivedCategory.Q.obj
      (((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).obj
        (motivicFiniteEtaleSheafComplex k 1 n)) ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left n)) :=
  ((fullSmallEtaleRestrict X).mapDerivedCategoryFactors.app _).symm ≪≫
    (fullSmallEtaleRestrict X).mapDerivedCategory.mapIso
      (weightOneFiniteEtaleKernelIso k n hn hunit) ≪≫
    (fullSmallEtaleRestrict X).mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (fullSmallEtaleRestrict X) (.up ℤ) 0).app _ ≪≫
        (HomologicalComplex.single _ (.up ℤ) 0).mapIso
          (fullSmallRootsOfUnityIso X n))

end AlgebraicGeometry.MotivicCohomology.WeightOne
