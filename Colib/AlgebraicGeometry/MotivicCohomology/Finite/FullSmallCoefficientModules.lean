/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.CoefficientModules
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.FullSmallEtaleComparison
public import Colib.CategoryTheory.Sites.Modules.TorsionComplexTransport

/-!
# Actual coefficient quotient on the full small étale site

Apply the original change-of-topology and restriction functors to the original strict
coefficient quotient. Its coefficient action follows from termwise annihilation.
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

/-- The actual additive functor from smooth Nisnevich to the full small étale site. -/
def motivicFullSmallCoefficientTransport :=
  SmoothSite.nisnevichToEtaleSheaf (Spec (.of k)) AddCommGrpCat.{u + 1} ⋙
    EtaleSeparatedFiniteType.fullSmallEtaleRestrict X

/-- Actual change of topology and restriction is additive. -/
instance motivicFullSmallCoefficientTransport_additive :
    (motivicFullSmallCoefficientTransport k X).Additive := by
  unfold motivicFullSmallCoefficientTransport
  infer_instance

/-- The original strict quotient after actual change of topology and restriction. -/
def motivicCoefficientFullSmallEtaleComplex (q n : ℕ) :=
  ((motivicFullSmallCoefficientTransport k X).mapHomologicalComplex (.up ℤ)).obj
    (motivicCoefficientQuotient k q n)

/-- The transported original quotient retains sectionwise torsion. -/
theorem motivicCoefficientFullSmallEtaleComplex_torsion (q n : ℕ) (i : ℤ) :
    torsionSheafProperty X.left.smallEtaleTopology n
      ((motivicCoefficientFullSmallEtaleComplex k X q n).X i) :=
  transportedComplex_torsion _ _ (motivicFullSmallCoefficientTransport k X) n
    (motivicCoefficientQuotient k q n) (nsmul_id_motivicCoefficientQuotient_X k q n) i

variable [HasSheafify X.left.smallEtaleTopology CommRingCat.{u + 1}]
variable [X.left.smallEtaleTopology.WEqualsLocallyBijective CommRingCat.{u + 1}]
variable [X.left.smallEtaleTopology.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
variable (q n : ℕ)
variable [X.left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1})]

/-- Canonical coefficient structure on the actual full-small transported quotient. -/
def motivicCoefficientFullSmallModuleComplex :=
  torsionComplexModuleSheaf.{u + 1, u + 1} _ n
    (motivicCoefficientFullSmallEtaleComplex k X q n)
    (motivicCoefficientFullSmallEtaleComplex_torsion k X q n)

/-- Forgetting coefficients recovers the actual transported quotient as a complex. -/
def motivicCoefficientFullSmallModuleComplexUnderlyingIso :=
  torsionComplexModuleSheafUnderlyingIso.{u + 1, u + 1} _ n
    (motivicCoefficientFullSmallEtaleComplex k X q n)
    (motivicCoefficientFullSmallEtaleComplex_torsion k X q n)

end AlgebraicGeometry.PresheafWithTransfers
