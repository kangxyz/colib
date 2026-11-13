/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.CoefficientQuotient
public import Colib.CategoryTheory.Sites.Modules.TorsionComplex

/-!
# The actual coefficient quotient as a module sheaf complex

This equips the strict quotient of the original motivic sheaf complex with
coefficients in the constant ring sheaf. It does not identify that quotient
with the original finite cone in the derived category.
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

/-- Every section of a term of the actual strict quotient is annihilated by its level. -/
theorem motivicCoefficientQuotient_torsion (q n : ℕ) (i : ℤ) :
    torsionSheafProperty (SmoothSite.nisnevichTopology (Spec (.of k))) n
      ((motivicCoefficientQuotient k q n).X i) := by
  intro X x
  have h := congrArg
    (fun f => (((sheafToPresheaf _ AddCommGrpCat).map f).app X).hom x)
    (nsmul_id_motivicCoefficientQuotient_X k q n i)
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
  simpa using h

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) CommRingCat.{u + 1}]
variable [(SmoothSite.nisnevichTopology (Spec (.of k))).WEqualsLocallyBijective
  CommRingCat.{u + 1}]
variable [(SmoothSite.nisnevichTopology (Spec (.of k))).WEqualsLocallyBijective
  AddCommGrpCat.{u + 1}]

/-- The actual strict coefficient quotient over the constant `ZMod n` ring sheaf. -/
def motivicCoefficientModuleComplex (q n : ℕ) :=
  torsionComplexToModules.{u + 1, u + 1} _ n (motivicCoefficientQuotient k q n)
    (motivicCoefficientQuotient_torsion k q n)

/-- Forgetting coefficients recovers the actual quotient, rather than an unrelated model. -/
def motivicCoefficientModuleComplexUnderlyingIso (q n : ℕ) :=
  torsionComplexToModulesUnderlyingIso.{u + 1, u + 1} _ n
    (motivicCoefficientQuotient k q n) (motivicCoefficientQuotient_torsion k q n)

/-- The original finite cone maps to the underlying actual coefficient module complex. -/
def motivicFiniteToCoefficientModuleComplex (q n : ℕ) :=
  motivicFiniteToCoefficientQuotient k q n ≫
    (motivicCoefficientModuleComplexUnderlyingIso k q n).inv

/-- The module-valued bridge recovers the original cone-to-quotient map. -/
@[reassoc (attr := simp)]
theorem motivicFiniteToCoefficientModuleComplex_underlying (q n : ℕ) :
    motivicFiniteToCoefficientModuleComplex k q n ≫
        (motivicCoefficientModuleComplexUnderlyingIso k q n).hom =
      motivicFiniteToCoefficientQuotient k q n := by
  simp [motivicFiniteToCoefficientModuleComplex]

end AlgebraicGeometry.PresheafWithTransfers
