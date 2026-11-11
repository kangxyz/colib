/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimePresentationSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.SimpleInseparableTrace
public import Colib.RingTheory.KTheory.MilnorK.RestrictionKernel

/-!
# Purely inseparable prime presentation independence

Restriction of each actual simple norm is the same degree multiple. The original
restriction-kernel degree law kills their difference by the prime degree. The
already proved arbitrary-characteristic finite mixed expansion supplies a coprime
annihilator of that same difference. The original Bezout argument then proves
actual equality; no characteristic-power cancellation or injectivity is assumed.

The proof reuses the accepted normal-separable prime proof's coprime and Bezout
steps and changes only its first trace comparison. The native fields, quotient
presentations, scalar maps, simple norms and homogeneous grading are unchanged.
-/

@[expose] public noncomputable section

open Polynomial
open scoped BigOperators

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k]

/-- Presentation independence for every positive homogeneous class. The finite
coprime extension is chosen for this class, not once for the whole Milnor ring. -/
theorem simpleMilnorNorm_eq_map_algEquiv_of_prime_homogeneous_of_isPurelyInseparable
    {ell : ℕ}
    (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    [IsPurelyInseparable k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (m : ℕ) (x : MilnorKTheory (k[X] ⧸ Ideal.span {poly p}) (m + 1)) :
    simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) =
      simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))) := by
  classical
  let δ : MilnorKRing k :=
    simpleMilnorNorm p (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) -
      simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))
  let : FiniteDimensional k (k[X] ⧸ Ideal.span {poly p}) :=
    (AdjoinRoot.powerBasis' (monic p)).finite
  have hdim : Module.finrank k (k[X] ⧸ Ideal.span {poly p}) = ell := by
    rw [finrank_quotient_span_eq_natDegree, natDegree_eq p]
  have hE : milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p})) δ = 0 := by
    have hp := milnorKRingMap_simpleMilnorNorm_of_isPurelyInseparable
      p (AlgEquiv.refl : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k]
        (k[X] ⧸ Ideal.span {poly p}))
      (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    change milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p}))
      (simpleMilnorNorm p (milnorKRingMap (RingHom.id _)
        (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})))) = _ at hp
    rw [milnorKRingMap_id_apply] at hp
    have hq := milnorKRingMap_simpleMilnorNorm_of_isPurelyInseparable
      q f (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p}))
    dsimp only [δ]
    rw [map_sub, hp, hq, sub_self]
  have hell : (ell : ℤ) • δ = 0 := by
    have h := finrank_zsmul_eq_zero_of_milnorKRingMap_eq_zero
      k (k[X] ⧸ Ideal.span {poly p}) δ hE
    rw [hdim] at h
    exact h
  obtain ⟨d, hcop, hd⟩ :=
    simpleMilnorNorm_difference_exists_coprime_smul_arbitrary p q hprime f m x
  change (d : ℤ) • δ = 0 at hd
  have hbez : (1 : ℤ) = (ell : ℤ) * Nat.gcdA ell d +
      (d : ℤ) * Nat.gcdB ell d := by
    simpa only [hcop.gcd_eq_one, Nat.cast_one] using
      Nat.gcd_eq_gcd_ab ell d
  have hδ : δ = 0 := by
    calc
      δ = (1 : ℤ) • δ := (one_smul ℤ δ).symm
      _ = ((ell : ℤ) * Nat.gcdA ell d +
            (d : ℤ) * Nat.gcdB ell d) • δ :=
        congrArg (fun a : ℤ => a • δ) hbez
      _ = Nat.gcdA ell d • ((ell : ℤ) • δ) +
            Nat.gcdB ell d • ((d : ℤ) • δ) := by
        rw [add_smul, mul_comm (ell : ℤ) (Nat.gcdA ell d),
          mul_comm (d : ℤ) (Nat.gcdB ell d),
          mul_smul, mul_smul]
      _ = 0 := by rw [hell, hd, smul_zero, smul_zero, add_zero]
  exact sub_eq_zero.mp hδ

/-- Whole-ring presentation independence for a purely inseparable prime-degree
root extension over its original base field. -/
theorem simpleMilnorNorm_eq_map_algEquiv_of_prime_of_isPurelyInseparable
    {ell : ℕ}
    (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    [IsPurelyInseparable k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q}))
    (x : MilnorKRing (k[X] ⧸ Ideal.span {poly p})) :
    simpleMilnorNorm p x =
      simpleMilnorNorm q (milnorKRingMap f.toRingHom x) := by
  let lhs : MilnorKRing (k[X] ⧸ Ideal.span {poly p}) →+ MilnorKRing k := simpleMilnorNorm p
  let rhs : MilnorKRing (k[X] ⧸ Ideal.span {poly p}) →+ MilnorKRing k :=
    (simpleMilnorNorm q).comp (milnorKRingMap f.toRingHom).toAddMonoidHom
  have hgen (l : List (k[X] ⧸ Ideal.span {poly p})ˣ) :
      milnorKSymbolProd (k[X] ⧸ Ideal.span {poly p}) l ∈ AddMonoidHom.eqLocus lhs rhs := by
    change simpleMilnorNorm p (milnorKSymbolProd (k[X] ⧸ Ideal.span {poly p}) l) =
      simpleMilnorNorm q (milnorKRingMap f.toRingHom
        (milnorKSymbolProd (k[X] ⧸ Ideal.span {poly p}) l))
    cases l with
    | nil => simp only [milnorKSymbolProd_nil, map_one, simpleMilnorNorm_one]
    | cons a l =>
        exact simpleMilnorNorm_eq_map_algEquiv_of_prime_homogeneous_of_isPurelyInseparable
          p q hprime f l.length
          ⟨milnorKSymbolProd (k[X] ⧸ Ideal.span {poly p}) (a :: l), by
            simpa only [List.length_cons] using
              milnorKSymbolProd_mem_milnorKGrading (a :: l)⟩
  exact mem_of_forall_milnorKSymbolProd_mem (H := AddMonoidHom.eqLocus lhs rhs) hgen x

/-- Purely inseparable prime presentation independence for the existing additive maps. -/
theorem simpleMilnorNorm_eq_comp_of_prime_of_isPurelyInseparable
    {ell : ℕ}
    (p q : MonicIrreducibleOfDegree k ell) (hprime : ell.Prime)
    [IsPurelyInseparable k (k[X] ⧸ Ideal.span {poly p})]
    (f : (k[X] ⧸ Ideal.span {poly p}) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly q})) :
    simpleMilnorNorm p =
      (simpleMilnorNorm q).comp (milnorKRingMap f.toRingHom).toAddMonoidHom := by
  ext x
  exact simpleMilnorNorm_eq_map_algEquiv_of_prime_of_isPurelyInseparable p q hprime f x

end Stacks.Chow

end
