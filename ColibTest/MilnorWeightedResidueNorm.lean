/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.ResidueMinpoly

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot IsLocalRing

universe u v

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

example
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
            ε.toRingHom)) n x) :=
  milnorKNorm_map_eq_weighted_sum_scalarFactors_of_algEquiv p ε I D b a hcount n x

open scoped Classical in
example
    {k A M : Type u} [Field k] [CharZero k] [Field A] [Field M] [CharZero M]
    [Algebra k A] [FiniteDimensional k A] [Algebra k M]
    {ι : Type u} [Fintype ι] (V : ι → Type u)
    [∀ i, Field (V i)] [∀ i, Algebra M (V i)] [∀ i, Algebra k (V i)]
    [∀ i, IsScalarTower k M (V i)] [∀ i, FiniteDimensional M (V i)]
    (B : PowerBasis k A) (φ : ∀ i, A →ₐ[k] V i) (b : ι → ℕ) (a : ℕ)
    (hcount : ∀ q : {r : Σ d : ℕ, MonicIrreducibleOfDegree M d //
        poly r.2 ∣ (minpoly k B.gen).map (algebraMap k M)},
      (∑ i, if minpoly M (φ i B.gen) = poly q.1.2 then
        b i * Module.finrank (IntermediateField.adjoin M {φ i B.gen}) (V i) else 0) = a)
    (n : ℕ) (x : MilnorKTheory A n) :
    a • milnorKTransport (algebraMap k M) n (milnorKNorm k A n x) =
      ∑ i, b i • milnorKNorm M (V i) n (milnorKTransport (φ i).toRingHom n x) :=
  milnorKNorm_map_eq_weighted_residue_sum V B φ b a hcount n x

end
