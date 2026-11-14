/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneZModOriginalBeta
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneZModDerived
public import Colib.CategoryTheory.Sites.Modules.NormalizedConcentratedDerivedIso
public import Colib.CategoryTheory.Sites.Modules.ULiftCoefficientEquivalence

/-!
# Literal finite coefficient weight-one comparison

Transport the actual normalized module identification along
the proved scalar equivalence. No heart fullness is asserted on derived categories.
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

variable [HasDerivedCategory.{u + 2}
  (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n)))]

/-- Forgetting the literal ZMod comparison recovers exactly the original finite beta1. -/
@[colib_tag "COL-1231", colib_tag "COL-1227"]
theorem weightOneZModBetaCompatibleIso_originalBeta
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    DerivedCategory.Q.map (motivicFiniteFullSmallToCoefficientQuotient k X 1 n) ≫
        (weightOneZModSourceForgetIso k X n).inv ≫
        (weightOneZModForgetCoefficients k X n).mapDerivedCategory.map
          (weightOneZModBetaCompatibleIso k X n hunit).hom ≫
        (weightOneZModTargetForgetIso k X n).hom =
      (MotivicCohomology.WeightOne.weightOneFiniteFullSmallRootsIso k X n
        (NeZero.ne n) hunit).hom := by
  rw [weightOneZModBetaCompatibleIso_square, Iso.inv_hom_id_assoc]
  have := motivicFiniteFullSmallToCoefficientQuotient_quasiIso k X 1 n (NeZero.ne n)
  change DerivedCategory.Q.map (motivicFiniteFullSmallToCoefficientQuotient k X 1 n) ≫
    inv (DerivedCategory.Q.map (motivicFiniteFullSmallToCoefficientQuotient k X 1 n)) ≫ _ = _
  exact IsIso.hom_inv_id_assoc _ _

end AlgebraicGeometry.PresheafWithTransfers
