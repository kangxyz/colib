/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Dedekind.ResidueTotalNorm
public import Colib.RingTheory.KTheory.MilnorK.Dedekind.PolynomialResidue
public import Colib.RingTheory.Localization.FiniteTypeResidue
public import Colib.RingTheory.KTheory.MilnorK.RationalFunctionInfinity
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenFiniteReciprocity

/-!
# Rational reciprocity on the actual Dedekind prime points

Adapted from Aglib `Dedekind/PolynomialTotalNorm.lean`, revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 22–68. Native rational
reciprocity is reused on its actual support. The original chosen norm on each
actual local residue field is identified through the native quotient equivalence.
-/

@[expose] public noncomputable section

namespace Stacks.Chow.PolynomialDedekindResidue

open Polynomial IsLocalRing IsDedekindDomain MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

universe u
variable (k : Type u) [Field k] [CharZero k]

/-- The actual local residue field is finite over the coefficients at every maximal ideal. -/
instance polynomialIdealLocalResidueFinite (q : Ideal k[X]) [q.IsMaximal] :
    FiniteDimensional k (ResidueField (Localization.AtPrime q)) :=
  Localization.finiteType_localResidue_finite k k[X] q

instance polynomialLocalResidueFinite (q : HeightOneSpectrum k[X]) :
    FiniteDimensional k (ResidueField (Localization.AtPrime q.asIdeal)) :=
  Localization.finiteType_localResidue_finite k k[X] q.asIdeal

/-- The native quotient equivalence is an equivalence for the actual coefficient action. -/
def quotientResidueAlgEquiv (p : MonicIrreduciblePoint k) :
    (k[X] ⧸ Ideal.span {poly p.2}) ≃ₐ[k]
      ResidueField (Localization.AtPrime (point p).asIdeal) :=
  { quotientRingEquivResidueField (Ideal.span {poly p.2}) with
    commutes' := fun a => by
      change algebraMap (k[X] ⧸ Ideal.span {poly p.2})
        (Ideal.span {poly p.2}).ResidueField
        (algebraMap k (k[X] ⧸ Ideal.span {poly p.2}) a) = _
      exact (IsScalarTower.algebraMap_apply k (k[X] ⧸ Ideal.span {poly p.2})
        (Ideal.span {poly p.2}).ResidueField a).symm }

/-- The original prime residue norm is precisely the native simple-norm residue term. -/
theorem norm_totalResidue_point (p : MonicIrreduciblePoint k) (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    (milnorKNorm k (ResidueField (Localization.AtPrime (point p).asIdeal)) n
      (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) : MilnorKRing k) =
      simpleMilnorNorm p.2 (milnorKTotalResidue k n x p) := by
  let φ : ResidueField (Localization.AtPrime (point p).asIdeal) →+*
      (k[X] ⧸ Ideal.span {poly p.2}) :=
    (quotientResidueAlgEquiv k p).symm.toRingEquiv.toRingHom
  let ψ : ResidueField (Localization.AtPrime (point p).asIdeal) →+*
      (k[X] ⧸ Ideal.span {poly p.2}) :=
    (quotientRingEquivResidueField (Ideal.span {poly p.2})).symm.toRingHom
  let Φ : (ResidueField (Localization.AtPrime (point p).asIdeal) →+*
      (k[X] ⧸ Ideal.span {poly p.2})) → MilnorKRing k := fun f =>
    simpleMilnorNorm p.2
      (@milnorKRingMap (ResidueField (Localization.AtPrime (point p).asIdeal))
        (k[X] ⧸ Ideal.span {poly p.2}) inferInstance
        (Ideal.Quotient.field (Ideal.span {poly p.2})) f
        (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)))
  have hchosen : (milnorKNorm k
      (ResidueField (Localization.AtPrime (point p).asIdeal)) n
      (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) : MilnorKRing k) =
      Φ φ :=
    milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv p.2
      (quotientResidueAlgEquiv k p).symm
      (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p))
  have hmap : φ = ψ := by
    apply RingHom.ext
    intro y
    rfl
  have hres : @milnorKRingMap (ResidueField (Localization.AtPrime (point p).asIdeal))
      (k[X] ⧸ Ideal.span {poly p.2}) inferInstance
      (Ideal.Quotient.field (Ideal.span {poly p.2})) ψ
      (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) =
      (milnorKTotalResidue k n x p : MilnorKRing (k[X] ⧸ Ideal.span {poly p.2})) :=
    congrArg (fun z : @MilnorKTheory (k[X] ⧸ Ideal.span {poly p.2})
      (Ideal.Quotient.field (Ideal.span {poly p.2})) n => z.1) (totalResidue_point p n x)
  exact hchosen.trans ((congrArg Φ hmap).trans (congrArg (simpleMilnorNorm p.2) hres))

/-- Rational reciprocity on the original height-one prime residue groups, in every degree. -/
theorem normedTotalResidue_add_infinity (n : ℕ)
    (x : MilnorKTheory (RatFunc k) (n + 1)) :
    DedekindResidue.normedTotalResidue k k[X] (RatFunc k) n x +
      infinityResidue (k := k) n x = 0 := by
  classical
  change DedekindResidue.totalNorm k k[X] n
    (DedekindResidue.totalResidue k[X] (RatFunc k) n x) + _ = _
  rw [DedekindResidue.totalNorm_eq_finsum, ← finsum_comp_equiv (pointEquiv (k := k))]
  change (∑ᶠ p : MonicIrreduciblePoint k,
    milnorKNorm k (ResidueField (Localization.AtPrime (point p).asIdeal)) n
      (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p))) +
    infinityResidue (k := k) n x = 0
  have hsum : (∑ᶠ p : MonicIrreduciblePoint k,
      milnorKNorm k (ResidueField (Localization.AtPrime (point p).asIdeal)) n
        (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p))) =
      ∑ p ∈ (milnorKTotalResidue k n x).support,
        milnorKNorm k (ResidueField (Localization.AtPrime (point p).asIdeal)) n
          (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    apply DFinsupp.mem_support_iff.mpr
    intro hz
    apply hp
    apply Subtype.ext
    change (milnorKNorm k (ResidueField (Localization.AtPrime (point p).asIdeal)) n
      (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) : MilnorKRing k) = 0
    have hzRing : (milnorKTotalResidue k n x p :
        MilnorKRing (k[X] ⧸ Ideal.span {poly p.2})) = 0 := by
      exact congrArg (fun z : MilnorKTheory (k[X] ⧸ Ideal.span {poly p.2}) n =>
        z.1) hz
    exact (norm_totalResidue_point k p n x).trans
      ((congrArg (simpleMilnorNorm p.2) hzRing).trans (map_zero _))
  rw [hsum]
  apply Subtype.ext
  change ((∑ p ∈ (milnorKTotalResidue k n x).support,
      milnorKNorm k (ResidueField (Localization.AtPrime (point p).asIdeal)) n
        (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) :
      MilnorKTheory k n) : MilnorKRing k) + infinityResidueRing k x = 0
  have hnormsum : ((∑ p ∈ (milnorKTotalResidue k n x).support,
      milnorKNorm k (ResidueField (Localization.AtPrime (point p).asIdeal)) n
        (DedekindResidue.totalResidue k[X] (RatFunc k) n x (point p)) :
      MilnorKTheory k n) : MilnorKRing k) =
      ∑ p ∈ (milnorKTotalResidue k n x).support,
        simpleMilnorNorm p.2 (milnorKTotalResidue k n x p) := by
    rw [AddSubmonoidClass.coe_finsetSum]
    apply Finset.sum_congr rfl
    intro p _
    exact norm_totalResidue_point k p n x
  exact (congrArg (fun z : MilnorKRing k => z + infinityResidueRing k x) hnormsum).trans
    (sum_simpleMilnorNorm_totalResidue_add_infinity_eq_zero k n x)

end Stacks.Chow.PolynomialDedekindResidue
