/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneModuleConcentration
public import Colib.CategoryTheory.Sites.Modules.RootsOfUnityULiftModule
public import Colib.CategoryTheory.Sites.Modules.ConcentratedDerivedIso

/-!
# Actual weight-one homology with coefficients

The H0 identification is induced from the original abelian derived comparison and
lifted in the sheaf category, where coefficient forgetting is genuinely fully faithful.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Cohomology.ZModSheaf

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable (X : SmoothSite (Spec (.of k)))

variable [HasDerivedCategory.{u + 2}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{u + 2}
  (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

variable [HasSheafify X.left.smallEtaleTopology CommRingCat.{u + 1}]
variable [X.left.smallEtaleTopology.WEqualsLocallyBijective CommRingCat.{u + 1}]
variable [X.left.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable (n : ℕ)
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1})]

variable [NeZero n]

/-- Actual H0 of the module model, after forgetting coefficients, is the original μn. -/
def weightOneModuleHomologyForgetIso (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    (Stacks.EtaleCohomology.etaleModuleForgetAb (ULift.{u + 1} (ZMod n)) X.left).obj
      ((motivicCoefficientFullSmallModuleComplex k X 1 n).homology 0) ≅
      Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left n := by
  let K := motivicCoefficientFullSmallModuleComplex k X 1 n
  let F := Stacks.EtaleCohomology.etaleModuleForgetAb (ULift.{u + 1} (ZMod n)) X.left
  exact ((K.sc 0).mapHomologyIso F).symm ≪≫
    (HomologicalComplex.homologyFunctor _ (.up ℤ) 0).mapIso
      (motivicCoefficientFullSmallModuleComplexUnderlyingIso k X 1 n) ≪≫
    ((DerivedCategory.homologyFunctorFactors _ 0).app
      (motivicCoefficientFullSmallEtaleComplex k X 1 n)).symm ≪≫
    (DerivedCategory.homologyFunctor _ 0).mapIso
      (weightOneCoefficientFullSmallRootsIso k X n (NeZero.ne n) hunit) ≪≫
    (DerivedCategory.homologyFunctorFactors _ 0).app _ ≪≫
    HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 _

/-- The actual module H0 identifies linearly with the original μn module with lifted scalars. -/
def weightOneModuleHomologyRootsIso (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    (motivicCoefficientFullSmallModuleComplex k X 1 n).homology 0 ≅
      Stacks.Kummer.rootsOfUnityULiftModule X.left n := by
  let F := Stacks.EtaleCohomology.etaleModuleForgetAb (ULift.{u + 1} (ZMod n)) X.left
  let hF := uliftZModSheafForgetFullyFaithful.{u + 1, u + 1}
    X.left.smallEtaleTopology n
  letI : F.Full := hF.full
  exact F.preimageIso (weightOneModuleHomologyForgetIso k X n hunit ≪≫
    (Stacks.Kummer.rootsOfUnityULiftModuleForgetIso X.left n).symm)

end AlgebraicGeometry.PresheafWithTransfers
