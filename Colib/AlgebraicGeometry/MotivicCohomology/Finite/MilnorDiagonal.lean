/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.MilnorEquivalence
public import Colib.AlgebraicGeometry.MotivicCohomology.FieldTopDegree

/-!
# Finite diagonal comparison from the original integral symbol

This consumer descends the existing arbitrary-field integral Milnor comparison along the
literal subgroup of multiples and the original finite-coefficient reduction. It does not
construct an étale realization, a norm-residue map, or a new product.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe w u

namespace AlgebraicGeometry.MotivicCohomology.FiniteMilnorDiagonal

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers
open DiagonalMilnorEquivalence

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The literal subgroup of multiples in the existing native Milnor group. -/
def milnorMultiples (q n : ℕ) : AddSubgroup (MilnorKTheory k q) :=
  (n • AddMonoidHom.id (MilnorKTheory k q)).range

/-- The existing Milnor group modulo its literal subgroup of multiples. -/
abbrev milnorModulo (q n : ℕ) := MilnorKTheory k q ⧸ milnorMultiples k q n

/-- The original integral symbol followed by the original finite coefficient reduction. -/
def symbolReduction (q n : ℕ) : MilnorKTheory k q →+
    motivicFiniteCohomology k (q : ℤ) q n (SmoothSite.base (Spec (.of k))) :=
  (motivicBaseIntegralReduction k (q : ℤ) q n).comp (motivicEquiv k q).toAddMonoidHom

/-- Every finite diagonal class is the reduction of an original Milnor symbol. -/
theorem symbolReduction_surjective (q n : ℕ) :
    Function.Surjective (symbolReduction k q n) :=
  (FieldTopDegree.integralReduction_surjective k q n).comp (motivicEquiv k q).surjective

/-- The kernel consists exactly of multiples in the native Milnor group. -/
theorem symbolReduction_ker (q n : ℕ) :
    (symbolReduction k q n).ker = milnorMultiples k q n := by
  ext x
  change motivicBaseIntegralReduction k (q : ℤ) q n (motivicEquiv k q x) = 0 ↔
    ∃ y : MilnorKTheory k q, n • y = x
  rw [FieldTopDegree.integralReduction_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(motivicEquiv k q).symm y, (motivicEquiv k q).injective ?_⟩
    simpa only [map_nsmul, AddEquiv.apply_symm_apply] using hy
  · rintro ⟨y, rfl⟩
    exact ⟨motivicEquiv k q y, (map_nsmul (motivicEquiv k q) n y).symm⟩

/-- Finite motivic diagonal cohomology is the native Milnor group modulo multiples.
No invertibility hypothesis on the coefficient level is needed for this motivic statement. -/
@[colib_tag "COL-1224",
  colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/MilnorEquivalence.lean:84-99" "ingredient"
  "Historical characteristic-zero integral comparison; reuse its migrated arbitrary-field COL-1026",
  colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/SuslinVoevodsky/FieldTopDegree.lean:85-95,128-139" "ingredient"
  "Original integral coefficient reduction and its literal quotient comparison"]
def motivicFiniteEquiv (q n : ℕ) : milnorModulo k q n ≃+
    motivicFiniteCohomology k (q : ℤ) q n (SmoothSite.base (Spec (.of k))) :=
  (QuotientAddGroup.quotientAddEquivOfEq (symbolReduction_ker k q n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (symbolReduction k q n) (symbolReduction_surjective k q n))

/-- The finite comparison retains the original integral symbol and reduction on cosets. -/
@[colib_tag "COL-1224"]
theorem motivicFiniteEquiv_mk (q n : ℕ) (x : MilnorKTheory k q) :
    motivicFiniteEquiv k q n (QuotientAddGroup.mk x) =
      motivicBaseIntegralReduction k (q : ℤ) q n
        (DiagonalMilnorSymbol.motivicSymbol k q x) := rfl

/-- In degree one the comparison consumes the existing weight-one Milnor equivalence. -/
@[colib_tag "COL-1224"]
theorem motivicFiniteEquiv_one_mk (n : ℕ) (x : MilnorKTheory k 1) :
    motivicFiniteEquiv k 1 n (QuotientAddGroup.mk x) =
      motivicBaseIntegralReduction k 1 1 n (WeightOne.milnorEquiv k x) := by
  change motivicBaseIntegralReduction k 1 1 n
      (DiagonalMilnorSymbol.motivicSymbol k 1 x) = _
  exact congrArg (motivicBaseIntegralReduction k 1 1 n)
    (DiagonalMilnorSymbol.motivicSymbol_one_comparison k x)

end AlgebraicGeometry.MotivicCohomology.FiniteMilnorDiagonal
