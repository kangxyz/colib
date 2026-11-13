/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Complex
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Quotient

/-!
# Strict coefficient quotients of the actual motivic sheaf complex

The construction uses the original motivic complex and its multiplication cone.
It supplies a natural cone-to-quotient map and proves that the target is strictly
annihilated by the level in every degree. Proving that this map is a
quasi-isomorphism and upgrading the target to a sheaf of `ZMod n` modules are
separate coefficient-model bridges, not assumptions of this construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

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

/-- The strict coefficient quotient of the original ordinary motivic complex. -/
def motivicCoefficientQuotient (q n : ℕ) :
    CochainComplex (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}) ℤ :=
  CochainComplex.finiteCoefficients.quotient (motivicSheafComplex k q) n

/-- The actual finite cone maps canonically to its strict coefficient quotient. -/
def motivicFiniteToCoefficientQuotient (q n : ℕ) :
    motivicFiniteSheafComplex k q n ⟶ motivicCoefficientQuotient k q n :=
  CochainComplex.finiteCoefficients.toQuotient (motivicSheafComplex k q) n

/-- The coefficient quotient is strictly annihilated by the original level. -/
theorem nsmul_id_motivicCoefficientQuotient (q n : ℕ) :
    n • 𝟙 (motivicCoefficientQuotient k q n) = 0 :=
  CochainComplex.finiteCoefficients.nsmul_id_quotient (motivicSheafComplex k q) n

/-- The annihilation statement holds on each actual term, not only on cohomology. -/
theorem nsmul_id_motivicCoefficientQuotient_X (q n : ℕ) (i : ℤ) :
    n • 𝟙 ((motivicCoefficientQuotient k q n).X i) = 0 :=
  CochainComplex.finiteCoefficients.nsmul_id_quotient_X (motivicSheafComplex k q) n i

/-- Original integral reduction followed by the bridge is the cokernel projection. -/
@[reassoc]
theorem integral_motivicFiniteToCoefficientQuotient (q n : ℕ) :
    CochainComplex.finiteCoefficients.integral (motivicSheafComplex k q) n ≫
        motivicFiniteToCoefficientQuotient k q n =
      CochainComplex.finiteCoefficients.quotientπ (motivicSheafComplex k q) n :=
  CochainComplex.finiteCoefficients.integral_toQuotient (motivicSheafComplex k q) n

end AlgebraicGeometry.PresheafWithTransfers
