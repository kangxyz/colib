/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.CoefficientModules
public import Colib.CategoryTheory.Sites.Modules.ZModSheafComplex

/-!
# The original motivic coefficient quotient as module-valued sheaves

This transports the actual coefficient model, not a replacement chosen from its
underlying abelian derived object.
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

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) CommRingCat.{u + 1}]
variable [(SmoothSite.nisnevichTopology (Spec (.of k))).WEqualsLocallyBijective
  CommRingCat.{u + 1}]
variable [(SmoothSite.nisnevichTopology (Spec (.of k))).WEqualsLocallyBijective
  AddCommGrpCat.{u + 1}]

variable (q n : ℕ)
variable [(SmoothSite.nisnevichTopology (Spec (.of k))).HasSheafCompose
  (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1})]

/-- The original strict motivic coefficient quotient as a module-valued sheaf complex. -/
def motivicCoefficientModuleSheafComplex :=
  torsionComplexModuleSheaf.{u + 1, u + 1} _ n (motivicCoefficientQuotient k q n)
    (motivicCoefficientQuotient_torsion k q n)

/-- The module-valued model recovers the original quotient, with its differential. -/
def motivicCoefficientModuleSheafComplexUnderlyingIso :=
  torsionComplexModuleSheafUnderlyingIso.{u + 1, u + 1} _ n
    (motivicCoefficientQuotient k q n) (motivicCoefficientQuotient_torsion k q n)

end AlgebraicGeometry.PresheafWithTransfers
