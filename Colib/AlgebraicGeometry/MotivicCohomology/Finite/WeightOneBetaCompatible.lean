/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneModuleForgotten
public import Colib.CategoryTheory.Sites.Modules.ConcentratedIsoLift

/-!
# Original beta1-compatible coefficient-linear identification

Calibrate in H0 using the original abelian comparison, then reconstruct only inside
the proved concentrated heart. Equality of the forgotten map is a theorem, not an input.
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

variable [HasDerivedCategory.{u + 2}
  (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))]


/-- The literal coefficient forgetful functor for the weight-one model. -/
abbrev weightOneForgetCoefficients :=
  Stacks.EtaleCohomology.etaleModuleForgetAb (ULift.{u + 1} (ZMod n)) X.left

/-- Source junction from the actual coefficient complex to the original quotient. -/
def weightOneModuleSourceForgetIso :
    (weightOneForgetCoefficients k X n).mapDerivedCategory.obj
      (DerivedCategory.Q.obj (motivicCoefficientFullSmallModuleComplex k X 1 n)) ≅
      DerivedCategory.Q.obj (motivicCoefficientFullSmallEtaleComplex k X 1 n) :=
  (weightOneForgetCoefficients k X n).mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso
      (motivicCoefficientFullSmallModuleComplexUnderlyingIso k X 1 n)

/-- Target junction to the original abelian roots-of-unity complex. -/
def weightOneModuleTargetForgetIso :
    (weightOneForgetCoefficients k X n).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj (Stacks.Kummer.rootsOfUnityULiftModule X.left n)) ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left n)) :=
  ((weightOneForgetCoefficients k X n).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      (Stacks.Kummer.rootsOfUnityULiftModuleForgetIso X.left n) ≪≫
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app _

/-- The original abelian comparison between the forgotten actual coefficient objects. -/
def weightOneOriginalRootsOnForgottenModules
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :=
  weightOneModuleSourceForgetIso k X n ≪≫
    weightOneCoefficientFullSmallRootsIso k X n (NeZero.ne n) hunit ≪≫
    (weightOneModuleTargetForgetIso k X n).symm

/-- Coefficient-linear identification calibrated to the original beta1 in H0. -/
def weightOneBetaCompatibleModuleIso (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    DerivedCategory.Q.obj (motivicCoefficientFullSmallModuleComplex k X 1 n) ≅
      (DerivedCategory.singleFunctor _ 0).obj (Stacks.Kummer.rootsOfUnityULiftModule X.left n) := by
  have := weightOneCoefficientModule_isGE k X n (NeZero.ne n) hunit
  have := weightOneCoefficientModule_isLE k X n (NeZero.ne n) hunit
  let F := Stacks.EtaleCohomology.etaleModuleForgetAb (ULift.{u + 1} (ZMod n)) X.left
  have : F.Full := (uliftZModSheafForgetFullyFaithful.{u + 1, u + 1}
    X.left.smallEtaleTopology n).full
  exact DerivedCategory.liftConcentratedIso F 0
    (weightOneOriginalRootsOnForgottenModules k X n hunit)

/-- The coefficient-linear map forgets to exactly the original specified comparison. -/
theorem weightOneBetaCompatibleModuleIso_map
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    (weightOneForgetCoefficients k X n).mapDerivedCategory.map
        (weightOneBetaCompatibleModuleIso k X n hunit).hom =
      (weightOneOriginalRootsOnForgottenModules k X n hunit).hom := by
  have := weightOneCoefficientModule_isGE k X n (NeZero.ne n) hunit
  have := weightOneCoefficientModule_isLE k X n (NeZero.ne n) hunit
  let F := Stacks.EtaleCohomology.etaleModuleForgetAb (ULift.{u + 1} (ZMod n)) X.left
  have : F.Full := (uliftZModSheafForgetFullyFaithful.{u + 1, u + 1}
    X.left.smallEtaleTopology n).full
  let Y := (DerivedCategory.singleFunctor _ 0).obj (Stacks.Kummer.rootsOfUnityULiftModule X.left n)
  let Z := DerivedCategory.Q.obj (motivicCoefficientFullSmallModuleComplex k X 1 n)
  let e : F.mapDerivedCategory.obj Y ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (F.obj (Stacks.Kummer.rootsOfUnityULiftModule X.left n)) :=
    (F.mapDerivedCategorySingleFunctor 0).app _
  have : DerivedCategory.IsGE (F.mapDerivedCategory.obj Y) 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
  have : DerivedCategory.IsLE (F.mapDerivedCategory.obj Y) 0 :=
    DerivedCategory.TStructure.t.isLE_of_iso e.symm 0
  have : DerivedCategory.IsGE (F.mapDerivedCategory.obj Z) 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (weightOneOriginalRootsOnForgottenModules k X n hunit).symm 0
  have : DerivedCategory.IsLE (F.mapDerivedCategory.obj Z) 0 :=
    DerivedCategory.TStructure.t.isLE_of_iso
      (weightOneOriginalRootsOnForgottenModules k X n hunit).symm 0
  exact DerivedCategory.liftConcentratedIso_map F 0
    (weightOneOriginalRootsOnForgottenModules k X n hunit)

end AlgebraicGeometry.PresheafWithTransfers
