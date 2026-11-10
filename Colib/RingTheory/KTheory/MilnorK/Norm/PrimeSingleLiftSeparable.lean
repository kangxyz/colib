/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeScalarBaseChangeSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalOriginResidueSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeChosenComparisonSeparable

/-!
# The iterated simple norm from the original upper single-residue lift

For a separable normal prime-degree constant extension, an actual homogeneous
single-residue lift computes the iterated simple norm as minus infinity of its
original chosen rational norm. The upper polynomial is arbitrary. The proof
uses the actual Laurent-origin-infinity square and the existing simple-norm
characterization, with its original minus sign.

This supplies the first side of the prime diamond, not the finite-place
contraction of the rational norm. No arbitrary-point residue square is assumed.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

local instance primeDiamond_nativeIrreducibleSeparable {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance primeDiamond_rootFiniteSeparable {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Module.Finite F (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance primeDiamond_rationalFiniteSeparable {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) :
    Module.Finite (RatFunc F) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable {k : Type u} [Field k] {d e : ℕ}

section SingleLift

variable (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable)
  (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))]

include hsep hp

/-- An actual upper single-residue lift computes the iterated native simple norm
as minus infinity of its original chosen rational norm. -/
theorem simpleMilnorNorm_simpleMilnorNorm_eq_neg_infinityResidueRing_of_lift_of_separable
    {f : ℕ} (q : MonicIrreducibleOfDegree (AdjoinRoot (poly p)) f)
    (z : MilnorKRing (AdjoinRoot (poly q))) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1))
    (hx : IsSingleResidueLift q z (x : MilnorKRing _)) :
    simpleMilnorNorm p (simpleMilnorNorm q z) =
      -infinityResidueRing k
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x :
          MilnorKRing (RatFunc k)) := by
  have hinf := congrArg (fun y : MilnorKTheory k n => (y : MilnorKRing k))
    (infinityResidue_milnorKNorm_ratFunc_of_separable p hsep hp n x)
  simp only [coe_infinityResidue, coe_milnorKNorm] at hinf
  calc
    simpleMilnorNorm p (simpleMilnorNorm q z) =
        -simpleMilnorNorm p (infinityResidueRing (AdjoinRoot (poly p)) x) := by
      let y : MilnorKRing (k[X] ⧸ Ideal.span {poly p}) :=
        infinityResidueRing (AdjoinRoot (poly p)) x
      have hq : (simpleMilnorNorm q z : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) = -y :=
        simpleMilnorNorm_eq hx
      exact (congrArg (simpleMilnorNorm p) hq).trans (map_neg (simpleMilnorNorm p) y)
    _ = -milnorKNormRing k (AdjoinRoot (poly p))
        (infinityResidueRing (AdjoinRoot (poly p)) x) := by
      let ep : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] AdjoinRoot (poly p) :=
        { toRingEquiv := RingEquiv.refl _
          commutes' := fun _ => rfl }
      let y : MilnorKRing (AdjoinRoot (poly p)) :=
        infinityResidueRing (AdjoinRoot (poly p)) x
      let : Algebra.IsSeparable k (AdjoinRoot (poly p)) :=
        AdjoinRoot.isSeparable_of_polynomial_separable _ hsep
      have hcomparison :=
        milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_one_or_normal_prime_of_separable
          p (Or.inr hp) ep.symm y
      change milnorKNormRing k (AdjoinRoot (poly p)) y =
        simpleMilnorNorm p (milnorKRingMap (RingHom.id (AdjoinRoot (poly p))) y)
          at hcomparison
      have hnorm : milnorKNormRing k (AdjoinRoot (poly p)) y = simpleMilnorNorm p y := by
        simpa only [milnorKRingMap_id_apply] using hcomparison
      exact congrArg Neg.neg hnorm.symm
    _ = _ := congrArg Neg.neg hinf.symm

/-- Every native homogeneous class admits a genuine homogeneous single-residue
lift, and the iterated simple norm is already computed on that same lift. -/
theorem exists_isSingleResidueLift_simpleMilnorNorm_simpleMilnorNorm_of_separable
    {f : ℕ} (q : MonicIrreducibleOfDegree (AdjoinRoot (poly p)) f)
    (n : ℕ) (z : MilnorKTheory (AdjoinRoot (poly q)) n) :
    ∃ x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1),
      IsSingleResidueLift q (z : MilnorKRing (AdjoinRoot (poly q))) (x : MilnorKRing _) ∧
      simpleMilnorNorm p (simpleMilnorNorm q (z : MilnorKRing (AdjoinRoot (poly q)))) =
        -infinityResidueRing k
          (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x :
            MilnorKRing (RatFunc k)) := by
  let zq : MilnorKRing ((AdjoinRoot (poly p))[X] ⧸ Ideal.span {poly q}) :=
    (z : MilnorKRing (AdjoinRoot (poly q)))
  have hzq : zq ∈ milnorKGrading ((AdjoinRoot (poly p))[X] ⧸ Ideal.span {poly q}) n :=
    z.property
  obtain ⟨x, hxn, hx⟩ := exists_isSingleResidueLift' q hzq
  exact ⟨⟨x, hxn⟩, hx,
    simpleMilnorNorm_simpleMilnorNorm_eq_neg_infinityResidueRing_of_lift_of_separable
      p hsep hp q (z : MilnorKRing (AdjoinRoot (poly q))) n ⟨x, hxn⟩ hx⟩

end SingleLift

end Stacks.Chow

end
