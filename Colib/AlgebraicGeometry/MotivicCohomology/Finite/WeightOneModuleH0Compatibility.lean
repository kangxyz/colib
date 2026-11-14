/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneZModDerived
public import Colib.CategoryTheory.Sites.Modules.ConcentratedHomologyFaithful

/-!
# Actual H0 normalization before the beta1 comparison

These are actual maps of the original model; neither H0
compatibility nor beta1 compatibility is taken as a hypothesis.
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

/-- Forgetting the proved linear H0 identification gives the explicit original H0 comparison. -/
theorem weightOneModuleHomologyRootsIso_forget
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    (Stacks.EtaleCohomology.etaleModuleForgetAb (ULift.{u + 1} (ZMod n)) X.left).map
        (weightOneModuleHomologyRootsIso k X n hunit).hom ≫
      (Stacks.Kummer.rootsOfUnityULiftModuleForgetIso X.left n).hom =
        (weightOneModuleHomologyForgetIso k X n hunit).hom := by
  let F := Stacks.EtaleCohomology.etaleModuleForgetAb (ULift.{u + 1} (ZMod n)) X.left
  let hF := uliftZModSheafForgetFullyFaithful.{u + 1, u + 1}
    X.left.smallEtaleTopology n
  have : F.Full := hF.full
  change F.map (F.preimage _) ≫ _ = _
  rw [F.map_preimage]
  simp

variable [HasDerivedCategory.{u + 2}
  (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))))]

/-- The normalized actual module derived map has exactly the proved H0 roots comparison. -/
theorem weightOneModuleNormalizedDerivedRootsIso_homology
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    (DerivedCategory.homologyFunctor _ 0).map
        (weightOneModuleNormalizedDerivedRootsIso k X n hunit).hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).hom.app
        (Stacks.Kummer.rootsOfUnityULiftModule X.left n) =
      (DerivedCategory.homologyFunctorFactors _ 0).hom.app
          (motivicCoefficientFullSmallModuleComplex k X 1 n) ≫
        (weightOneModuleHomologyRootsIso k X n hunit).hom := by
  have := weightOneCoefficientModule_isGE k X n (NeZero.ne n) hunit
  have := weightOneCoefficientModule_isLE k X n (NeZero.ne n) hunit
  let K := motivicCoefficientFullSmallModuleComplex k X 1 n
  let a := (DerivedCategory.homologyFunctorFactors _ 0).app K ≪≫
    weightOneModuleHomologyRootsIso k X n hunit
  let c := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) 0
  change (DerivedCategory.homologyFunctor _ 0).map
      ((DerivedCategory.normalizedConcentratedHomologyIso (DerivedCategory.Q.obj K) 0).hom ≫
        (DerivedCategory.singleFunctor _ 0).map a.hom) ≫ c.hom.app _ = a.hom
  rw [Functor.map_comp, Category.assoc]
  have hc := c.hom.naturality a.hom
  change (DerivedCategory.homologyFunctor _ 0).map
      ((DerivedCategory.singleFunctor _ 0).map a.hom) ≫ c.hom.app _ =
    c.hom.app _ ≫ a.hom at hc
  rw [hc, ← Category.assoc,
    DerivedCategory.normalizedConcentratedHomologyIso_homology, Category.id_comp]

end AlgebraicGeometry.PresheafWithTransfers
