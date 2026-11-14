/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneOriginalBeta
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

/-- The calibrated comparison transported to literal finite coefficients. -/
@[colib_tag "COL-1231"]
def weightOneZModBetaCompatibleIso (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    DerivedCategory.Q.obj (weightOneZModComplex k X n) ≅
      (DerivedCategory.singleFunctor _ 0).obj (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.left n) :=
  ((weightOneRemoveULiftFunctor k X n).mapDerivedCategoryFactors.app _).symm ≪≫
    (weightOneRemoveULiftFunctor k X n).mapDerivedCategory.mapIso
      (weightOneBetaCompatibleModuleIso k X n hunit) ≪≫
    ((weightOneRemoveULiftFunctor k X n).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (weightOneRemoveULiftRootsIso k X n)


/-- Forgetting the literal finite coefficient action. -/
abbrev weightOneZModForgetCoefficients :=
  Stacks.EtaleCohomology.etaleModuleForgetAb (ZMod n) X.left

/-- Scalar removal does not change the underlying abelian sheaf functor. -/
def weightOneScalarForgetIso :
    weightOneRemoveULiftFunctor k X n ⋙ weightOneZModForgetCoefficients k X n ≅
      weightOneForgetCoefficients k X n :=
  Iso.refl _

/-- The actual derived scalar-forgetting junction. -/
def weightOneDerivedScalarForgetIso :
    (weightOneRemoveULiftFunctor k X n).mapDerivedCategory ⋙
      (weightOneZModForgetCoefficients k X n).mapDerivedCategory ≅
        (weightOneForgetCoefficients k X n).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso
    (weightOneRemoveULiftFunctor k X n) (weightOneZModForgetCoefficients k X n))

/-- Naturality gives the scalar-forgetting square for the calibrated comparison. -/
theorem weightOneDerivedScalarForget_beta
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    (weightOneZModForgetCoefficients k X n).mapDerivedCategory.map
        ((weightOneRemoveULiftFunctor k X n).mapDerivedCategory.map
          (weightOneBetaCompatibleModuleIso k X n hunit).hom) ≫
        (weightOneDerivedScalarForgetIso k X n).hom.app _ =
      (weightOneDerivedScalarForgetIso k X n).hom.app _ ≫
        (weightOneOriginalRootsOnForgottenModules k X n hunit).hom := by
  rw [← weightOneBetaCompatibleModuleIso_map]
  exact (weightOneDerivedScalarForgetIso k X n).hom.naturality
    (weightOneBetaCompatibleModuleIso k X n hunit).hom

end AlgebraicGeometry.PresheafWithTransfers
