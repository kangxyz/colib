/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenScalarBaseChange
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTower
public import Colib.RingTheory.KTheory.MilnorK.RestrictionKernel

/-!
# Weighted refinement of the actual native scalar factors

Adapted from `Aglib/KTheory/MilnorK/Norm/FiniteExtension/WeightedBranches.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 30–110.
The native chosen norm and literal native coefficient-factor subtype replace the
old Milnor presentation. The degree-weight identity is explicit; the later DVR
consumer proves it from characteristic polynomials and uniformizer equations.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- Positive horizontal ramification and the actual squares convert the fiber count. -/
theorem ramification_fiber_weight_conversion
    {ι : Type*} [Fintype ι] (e a : ℕ) (he : 0 < e) (b c d : ι → ℕ)
    (hsquare : ∀ i, e * b i = a * c i)
    (hcount : ∑ i, c i * d i = e) : ∑ i, b i * d i = a := by
  apply Nat.eq_of_mul_eq_mul_left he
  calc
    e * ∑ i, b i * d i = ∑ i, (e * b i) * d i := by
      rw [Finset.mul_sum]
      simp only [Nat.mul_assoc]
    _ = ∑ i, (a * c i) * d i := by simp_rw [hsquare]
    _ = a * ∑ i, c i * d i := by
      rw [Finset.mul_sum]
      simp only [Nat.mul_assoc]
    _ = e * a := by rw [hcount, Nat.mul_comm]

/-- The complete chosen-norm scalar formula is independent of its finite enumeration. -/
theorem milnorKNorm_map_eq_sum_scalarFactors_of_algEquiv_of_fintype
    {k L E : Type u} [Field k] [CharZero k] [Field L] [Field E]
    [Algebra k L] [Algebra k E] [FiniteDimensional k E]
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (ε : E ≃ₐ[k] AdjoinRoot (poly p))
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap k L)}]
    (n : ℕ) (x : MilnorKTheory E n) :
    let _ : ∀ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
        poly r.2 ∣ (poly p).map (algebraMap k L)},
        FiniteDimensional L (AdjoinRoot (poly r.1.2)) :=
      fun r => (AdjoinRoot.powerBasis' (monic r.1.2)).finite
    milnorKTransport (algebraMap k L) n (milnorKNorm k E n x) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
          poly r.2 ∣ (poly p).map (algebraMap k L)},
        milnorKNorm L (AdjoinRoot (poly r.1.2)) n
          (milnorKTransport
            ((AdjoinRoot.map (algebraMap k L) (poly p) (poly r.1.2) r.2).comp
              ε.toRingHom) n x) := by
  intro hFinite
  have h := milnorKNorm_map_eq_sum_scalarFactors_of_algEquiv (algebraMap k L) p ε n x
  have hEnumeration : coefficientFactorFintype (algebraMap k L) (poly p) (ne_zero p) =
      (inferInstance : Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
        poly r.2 ∣ (poly p).map (algebraMap k L)}) := Subsingleton.elim _ _
  rw [hEnumeration] at h
  exact h

/-- Refining the literal scalar factors by finite fields preserves the chosen norm
with the exact degree-weighted multiplicity and original quotient maps. -/
theorem milnorKNorm_map_eq_weighted_sum_scalarFactors_of_algEquiv
    {k L E : Type u} [Field k] [CharZero k] [Field L] [CharZero L] [Field E]
    [Algebra k L] [Algebra k E] [FiniteDimensional k E]
    {d : ℕ} (p : MonicIrreducibleOfDegree k d) (ε : E ≃ₐ[k] AdjoinRoot (poly p))
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap k L)}]
    (I : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap k L)} → Type v) [∀ r, Fintype (I r)]
    (D : (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap k L)}) → I r → Type u)
    [∀ r i, Field (D r i)] [∀ r i, Algebra L (D r i)]
    [∀ r i, Algebra (AdjoinRoot (poly r.1.2)) (D r i)]
    [∀ r i, IsScalarTower L (AdjoinRoot (poly r.1.2)) (D r i)]
    [∀ r i, FiniteDimensional L (D r i)]
    [∀ r i, FiniteDimensional (AdjoinRoot (poly r.1.2)) (D r i)]
    (b : ∀ r, I r → ℕ) (a : ℕ)
    (hcount : ∀ r, ∑ i, b r i * Module.finrank (AdjoinRoot (poly r.1.2)) (D r i) = a)
    (n : ℕ) (x : MilnorKTheory E n) :
    a • milnorKTransport (algebraMap k L) n (milnorKNorm k E n x) =
      ∑ r, ∑ i, b r i • milnorKNorm L (D r i) n
        (milnorKTransport ((algebraMap (AdjoinRoot (poly r.1.2)) (D r i)).comp
          ((AdjoinRoot.map (algebraMap k L) (poly p) (poly r.1.2) r.2).comp
            ε.toRingHom)) n x) := by
  classical
  have branchFinite : ∀ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap k L)},
      FiniteDimensional L (AdjoinRoot (poly r.1.2)) :=
    fun r => (AdjoinRoot.powerBasis' (monic r.1.2)).finite
  rw [milnorKNorm_map_eq_sum_scalarFactors_of_algEquiv_of_fintype p ε, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  symm
  calc
    _ = ∑ i, (b r i * Module.finrank (AdjoinRoot (poly r.1.2)) (D r i)) •
        milnorKNorm L (AdjoinRoot (poly r.1.2)) n
          (milnorKTransport
            ((AdjoinRoot.map (algebraMap k L) (poly p) (poly r.1.2) r.2).comp
              ε.toRingHom) n x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← milnorKTransport_comp_apply,
        ← milnorKNorm_tower (k := L) (M := AdjoinRoot (poly r.1.2)) (L := D r i),
        milnorKNorm_milnorKTransport (AdjoinRoot (poly r.1.2)) (D r i),
        map_zsmul, natCast_zsmul, smul_smul]
    _ = _ := by rw [← Finset.sum_smul, hcount]

end Stacks.Chow

end
