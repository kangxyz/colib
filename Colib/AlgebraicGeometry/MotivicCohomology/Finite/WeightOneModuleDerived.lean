/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneModuleHomology

/-!
# Weight-one coefficient-linear derived identification

This is the actual transported coefficient model, internally truncated in its
module-sheaf category, followed by its proved linear H0 identification with μn.
The coefficient ring is explicitly ULift(Z/n); the target is the original μn
module restricted along ULift.ringEquiv. Compatibility with the original beta1
morphism is a separate statement, not claimed here.
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

/-- Internal coefficient-linear weight-one identification with the original roots module. -/
def weightOneModuleDerivedRootsIso (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    DerivedCategory.Q.obj (motivicCoefficientFullSmallModuleComplex k X 1 n) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        (Stacks.Kummer.rootsOfUnityULiftModule X.left n) := by
  have := weightOneCoefficientModule_isGE k X n (NeZero.ne n) hunit
  have := weightOneCoefficientModule_isLE k X n (NeZero.ne n) hunit
  exact DerivedCategory.concentratedComplexHomologyIso
    (motivicCoefficientFullSmallModuleComplex k X 1 n) 0 ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (weightOneModuleHomologyRootsIso k X n hunit)

end AlgebraicGeometry.PresheafWithTransfers
