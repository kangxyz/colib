/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.FullSmallCoefficientQuasiIso
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.WeightOneFullSmallRoots
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Concentration of the actual transported weight-one coefficient quotient

The comparison below remains in D(Ab). It is formed from the original finite-cone
comparison, not an assumed coefficient-linear identification.
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

/-- The actual transported quotient has the original weight-one roots comparison in D(Ab). -/
def weightOneCoefficientFullSmallRootsIso (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    DerivedCategory.Q.obj (motivicCoefficientFullSmallEtaleComplex k X 1 n) ≅
      DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X.left n)) := by
  have := motivicFiniteFullSmallToCoefficientQuotient_quasiIso k X 1 n hn
  exact (asIso (DerivedCategory.Q.map
    (motivicFiniteFullSmallToCoefficientQuotient k X 1 n))).symm ≪≫
      MotivicCohomology.WeightOne.weightOneFiniteFullSmallRootsIso k X n hn hunit

/-- The original transported quotient has no negative-degree cohomology in weight one. -/
theorem weightOneCoefficientFullSmall_isGE (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    CochainComplex.IsGE (motivicCoefficientFullSmallEtaleComplex k X 1 n) 0 := by
  rw [← DerivedCategory.isGE_Q_obj_iff]
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (weightOneCoefficientFullSmallRootsIso k X n hn hunit).symm 0

/-- The original transported quotient has no positive-degree cohomology in weight one. -/
theorem weightOneCoefficientFullSmall_isLE (n : ℕ) (hn : n ≠ 0)
    (hunit : IsUnit (n : Γ(Spec (.of k), ⊤))) :
    CochainComplex.IsLE (motivicCoefficientFullSmallEtaleComplex k X 1 n) 0 := by
  rw [← DerivedCategory.isLE_Q_obj_iff]
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (weightOneCoefficientFullSmallRootsIso k X n hn hunit).symm 0

end AlgebraicGeometry.PresheafWithTransfers
