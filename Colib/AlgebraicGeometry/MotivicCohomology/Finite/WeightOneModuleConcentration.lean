/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneCoefficientConcentration
public import Colib.CategoryTheory.Sites.Modules.ConcentrationReflection
public import Colib.CategoryTheory.Sites.Modules.ULiftZModHeartLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing

/-!
# Concentration of the actual weight-one module coefficient model

The original D(Ab) comparison supplies exactness of the forgotten complex, and
faithful exact coefficient forgetting reflects it. No coefficient-linear identification
or H0 isomorphism is an input.
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

/-- The actual weight-one module complex is exact in every nonzero degree. -/
theorem weightOneCoefficientModule_exactAt (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) (i : ℤ) (hi : i ≠ 0) :
    (motivicCoefficientFullSmallModuleComplex k X 1 n).ExactAt i := by
  let F := Stacks.EtaleCohomology.etaleModuleForgetAb (ULift.{u + 1} (ZMod n)) X.left
  apply CochainComplex.exactAt_of_exactAt_forget F
    (motivicCoefficientFullSmallModuleComplex k X 1 n) i
  have h : (motivicCoefficientFullSmallEtaleComplex k X 1 n).ExactAt i := by
    rcases lt_or_gt_of_ne hi with hi | hi
    · have := weightOneCoefficientFullSmall_isGE k X n hn hunit
      exact CochainComplex.exactAt_of_isGE _ 0 i hi
    · have := weightOneCoefficientFullSmall_isLE k X n hn hunit
      exact CochainComplex.exactAt_of_isLE _ 0 i hi
  exact h.of_iso (motivicCoefficientFullSmallModuleComplexUnderlyingIso k X 1 n).symm

/-- The actual module model has no negative-degree cohomology. -/
theorem weightOneCoefficientModule_isGE (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    CochainComplex.IsGE (motivicCoefficientFullSmallModuleComplex k X 1 n) 0 := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  exact weightOneCoefficientModule_exactAt k X n hn hunit i (ne_of_lt hi)

/-- The actual module model has no positive-degree cohomology. -/
theorem weightOneCoefficientModule_isLE (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    CochainComplex.IsLE (motivicCoefficientFullSmallModuleComplex k X 1 n) 0 := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  exact weightOneCoefficientModule_exactAt k X n hn hunit i (ne_of_gt hi)

end AlgebraicGeometry.PresheafWithTransfers
