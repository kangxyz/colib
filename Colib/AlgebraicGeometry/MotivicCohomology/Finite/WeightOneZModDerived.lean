/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneModuleDerived
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

/-- Actual scalar removal on the coefficient site. -/
def weightOneRemoveULiftFunctor :
    Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) ⥤
      Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ZMod n)) :=
  removeULiftCoefficients X.left.smallEtaleTopology n

/-- Scalar removal is an equivalence, not merely a forgetful functor. -/
instance weightOneRemoveULiftFunctor_isEquivalence :
    (weightOneRemoveULiftFunctor k X n).IsEquivalence :=
  inferInstanceAs 
    ((removeULiftCoefficientEquivalence X.left.smallEtaleTopology n).functor.IsEquivalence)

/-- Actual scalar removal preserves addition. -/
instance weightOneRemoveULiftFunctor_additive : (weightOneRemoveULiftFunctor k X n).Additive where
  map_add := rfl

/-- The literal ZMod coefficient complex is transported from the actual lifted model. -/
def weightOneZModComplex :=
  ((weightOneRemoveULiftFunctor k X n).mapHomologicalComplex (.up ℤ)).obj
    (motivicCoefficientFullSmallModuleComplex k X 1 n)

/-- Explicitly normalized version of the proved internal lifted coefficient identification. -/
def weightOneModuleNormalizedDerivedRootsIso
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    DerivedCategory.Q.obj (motivicCoefficientFullSmallModuleComplex k X 1 n) ≅
      (DerivedCategory.singleFunctor _ 0).obj (Stacks.Kummer.rootsOfUnityULiftModule X.left n) := by
  have := weightOneCoefficientModule_isGE k X n (NeZero.ne n) hunit
  have := weightOneCoefficientModule_isLE k X n (NeZero.ne n) hunit
  exact DerivedCategory.normalizedConcentratedHomologyIso
      (DerivedCategory.Q.obj (motivicCoefficientFullSmallModuleComplex k X 1 n)) 0 ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((DerivedCategory.homologyFunctorFactors _ 0).app _ ≪≫
        weightOneModuleHomologyRootsIso k X n hunit)

/-- Removing lifted scalars recovers the original native roots-of-unity module. -/
def weightOneRemoveULiftRootsIso :
    (weightOneRemoveULiftFunctor k X n).obj (Stacks.Kummer.rootsOfUnityULiftModule X.left n) ≅
      Stacks.Kummer.rootsOfUnityModule.{u, 0} X.left n :=
  (removeULiftCoefficientEquivalence X.left.smallEtaleTopology n).counitIso.app
    (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.left n)

/-- The actual scalar-transported coefficient complex identifies with the original μn module. -/
def weightOneZModDerivedRootsIso (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    DerivedCategory.Q.obj (weightOneZModComplex k X n) ≅
      (DerivedCategory.singleFunctor _ 0).obj (Stacks.Kummer.rootsOfUnityModule.{u, 0} X.left n) :=
  ((weightOneRemoveULiftFunctor k X n).mapDerivedCategoryFactors.app _).symm ≪≫
    (weightOneRemoveULiftFunctor k X n).mapDerivedCategory.mapIso
      (weightOneModuleNormalizedDerivedRootsIso k X n hunit) ≪≫
    ((weightOneRemoveULiftFunctor k X n).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (weightOneRemoveULiftRootsIso k X n)

end AlgebraicGeometry.PresheafWithTransfers
