/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneBetaCompatible

/-!
# Exact recovery of the original beta1 morphism

Both source and target junctions are retained. The finite-cone comparison is the
original one, not a newly chosen abelian isomorphism.
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


/-- On the actual quotient, the coefficient-linear iso recovers the original roots comparison. -/
theorem weightOneBetaCompatibleModuleIso_quotient
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    (weightOneModuleSourceForgetIso k X n).inv ≫
        (weightOneForgetCoefficients k X n).mapDerivedCategory.map
          (weightOneBetaCompatibleModuleIso k X n hunit).hom ≫
        (weightOneModuleTargetForgetIso k X n).hom =
      (weightOneCoefficientFullSmallRootsIso k X n (NeZero.ne n) hunit).hom := by
  rw [weightOneBetaCompatibleModuleIso_map]
  simp [weightOneOriginalRootsOnForgottenModules]

/-- Forgetting the calibrated linear identification gives exactly the original finite beta1. -/
theorem weightOneBetaCompatibleModuleIso_originalBeta
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    DerivedCategory.Q.map (motivicFiniteFullSmallToCoefficientQuotient k X 1 n) ≫
        (weightOneModuleSourceForgetIso k X n).inv ≫
        (weightOneForgetCoefficients k X n).mapDerivedCategory.map
          (weightOneBetaCompatibleModuleIso k X n hunit).hom ≫
        (weightOneModuleTargetForgetIso k X n).hom =
      (MotivicCohomology.WeightOne.weightOneFiniteFullSmallRootsIso k X n
        (NeZero.ne n) hunit).hom := by
  rw [weightOneBetaCompatibleModuleIso_quotient]
  have := motivicFiniteFullSmallToCoefficientQuotient_quasiIso k X 1 n (NeZero.ne n)
  change DerivedCategory.Q.map (motivicFiniteFullSmallToCoefficientQuotient k X 1 n) ≫
    inv (DerivedCategory.Q.map (motivicFiniteFullSmallToCoefficientQuotient k X 1 n)) ≫ _ = _
  exact IsIso.hom_inv_id_assoc _ _

end AlgebraicGeometry.PresheafWithTransfers
