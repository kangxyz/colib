/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneZModBeta
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

/-- Scalar-transported source junction to the original abelian quotient. -/
def weightOneZModSourceForgetIso :
    (weightOneZModForgetCoefficients k X n).mapDerivedCategory.obj
      (DerivedCategory.Q.obj (weightOneZModComplex k X n)) ≅
        DerivedCategory.Q.obj (motivicCoefficientFullSmallEtaleComplex k X 1 n) :=
  (weightOneZModForgetCoefficients k X n).mapDerivedCategory.mapIso
      ((weightOneRemoveULiftFunctor k X n).mapDerivedCategoryFactors.app _).symm ≪≫
    (weightOneDerivedScalarForgetIso k X n).app _ ≪≫
    weightOneModuleSourceForgetIso k X n

/-- Scalar-transported target junction to the original abelian roots complex. -/
def weightOneZModTargetForgetIso :
    (weightOneZModForgetCoefficients k X n).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.left n)) ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left n)) :=
  (weightOneZModForgetCoefficients k X n).mapDerivedCategory.mapIso
    ((((weightOneRemoveULiftFunctor k X n).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (weightOneRemoveULiftRootsIso k X n)).symm) ≪≫
    (weightOneDerivedScalarForgetIso k X n).app _ ≪≫
    weightOneModuleTargetForgetIso k X n

/-- The literal coefficient comparison has the specified original abelian square. -/
theorem weightOneZModBetaCompatibleIso_square
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    (weightOneZModForgetCoefficients k X n).mapDerivedCategory.map
        (weightOneZModBetaCompatibleIso k X n hunit).hom ≫
        (weightOneZModTargetForgetIso k X n).hom =
      (weightOneZModSourceForgetIso k X n).hom ≫
        (weightOneCoefficientFullSmallRootsIso k X n (NeZero.ne n) hunit).hom := by
  let G := (weightOneZModForgetCoefficients k X n).mapDerivedCategory
  let a := ((weightOneRemoveULiftFunctor k X n).mapDerivedCategoryFactors.app
    (motivicCoefficientFullSmallModuleComplex k X 1 n)).symm
  let b := ((weightOneRemoveULiftFunctor k X n).mapDerivedCategorySingleFunctor 0).app
      (Stacks.Kummer.rootsOfUnityULiftModule X.left n) ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (weightOneRemoveULiftRootsIso k X n)
  let c := (weightOneRemoveULiftFunctor k X n).mapDerivedCategory.mapIso
    (weightOneBetaCompatibleModuleIso k X n hunit)
  change G.map (a.hom ≫ c.hom ≫ b.hom) ≫
      (G.map b.inv ≫ (weightOneDerivedScalarForgetIso k X n).hom.app _ ≫
        (weightOneModuleTargetForgetIso k X n).hom) =
    (G.map a.hom ≫ (weightOneDerivedScalarForgetIso k X n).hom.app _ ≫
      (weightOneModuleSourceForgetIso k X n).hom) ≫
        (weightOneCoefficientFullSmallRootsIso k X n (NeZero.ne n) hunit).hom
  simp only [Functor.map_comp, Category.assoc]
  rw [← G.map_comp_assoc b.hom b.inv]
  simp only [Iso.hom_inv_id]
  have h := congrArg (fun f => G.map a.hom ≫ f ≫
    (weightOneModuleTargetForgetIso k X n).hom)
      (weightOneDerivedScalarForget_beta k X n hunit)
  dsimp only [G, c, Functor.mapIso]
  simpa [weightOneOriginalRootsOnForgottenModules, Category.assoc] using h

end AlgebraicGeometry.PresheafWithTransfers
