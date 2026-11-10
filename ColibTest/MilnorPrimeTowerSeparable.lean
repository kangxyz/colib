/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeTowerSeparable

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

universe u

local instance consumer_nativeIrreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

variable {k : Type u} [Field k] {d e : ℕ}

/-- The degree-one reduction needs no normality or characteristic assumption. -/
example (q : MonicIrreducibleOfDegree k d) (hq : (poly q).natDegree = 1)
    (ε : AdjoinRoot (poly q) ≃ₐ[k] k) (z : MilnorKRing (AdjoinRoot (poly q))) :
    simpleMilnorNorm q z = milnorKRingMap ε.toRingHom z := by
  have hd : d = 1 := (natDegree_eq q).symm.trans hq
  subst d
  exact simpleMilnorNorm_eq_map_of_degree_one q ε z

section LinearFactor

variable (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable)
  (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))] (h : MonicIrreducibleOfDegree k e)

include hsep hp

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)

/-- An arbitrary actual factor can be used once its actual matched degree is one. -/
example (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
      poly q.2 ∣ (poly h).map (algebraMap k E)})
    (hr : (poly (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2).natDegree =
      1)
    (ε : AdjoinRoot
      (poly (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2) ≃ₐ[H] H)
    (z : MilnorKRing (AdjoinRoot (poly q.1.2))) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 z) =
      simpleMilnorNorm h
        (milnorKRingMap
          ((AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).trans
            ε.toRingEquiv).toRingHom z) :=
  simpleMilnorNorm_prime_tower_of_linear_factor_of_separable p hsep hp h q hr ε z

end LinearFactor

section Tower

variable (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable)
  (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))] (h : MonicIrreducibleOfDegree k e)
  (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))

include hsep hp

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)
local notation "q" => AdjoinRoot.towerFactor (poly p) (poly h) f
local notation "Q" => AdjoinRoot (poly q.1.2)

/-- The quotient-side statement is a whole-ring identity. -/
example (z : MilnorKRing Q) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 z) =
      simpleMilnorNorm h
        (milnorKRingMap (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom z) :=
  simpleMilnorNorm_prime_tower_of_separable p hsep hp h f z

/-- The original-H statement uses the literal original coefficient-factor map. -/
example (x : MilnorKRing H) :
    simpleMilnorNorm h x =
      simpleMilnorNorm p
        (simpleMilnorNorm q.1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2) x)) :=
  simpleMilnorNorm_eq_prime_tower_of_separable p hsep hp h f x

example :
    (simpleMilnorNorm p).comp (simpleMilnorNorm q.1.2) =
      (simpleMilnorNorm h).comp
        (milnorKRingMap
          (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom).toAddMonoidHom :=
  simpleMilnorNorm_comp_simpleMilnorNorm_prime_tower_of_separable p hsep hp h f

example :
    simpleMilnorNorm h =
      (simpleMilnorNorm p).comp
        ((simpleMilnorNorm q.1.2).comp
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2)).toAddMonoidHom) :=
  simpleMilnorNorm_eq_comp_prime_tower_of_separable p hsep hp h f

/-- Every Milnor degree is retained, not only the unit-symbol degree. -/
example (n : ℕ) (z : MilnorKTheory Q n) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 (z : MilnorKRing Q)) =
      simpleMilnorNorm h
        (milnorKRingMap (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom
          (z : MilnorKRing Q)) :=
  simpleMilnorNorm_prime_tower_of_separable p hsep hp h f (z : MilnorKRing Q)

example (n : ℕ) (x : MilnorKTheory H n) :
    simpleMilnorNorm h (x : MilnorKRing H) =
      simpleMilnorNorm p
        (simpleMilnorNorm q.1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2)
            (x : MilnorKRing H))) :=
  simpleMilnorNorm_eq_prime_tower_of_separable p hsep hp h f (x : MilnorKRing H)

/-- In particular the theorem includes degree zero. -/
example (z : MilnorKTheory Q 0) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 (z : MilnorKRing Q)) =
      simpleMilnorNorm h
        (milnorKRingMap (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom
          (z : MilnorKRing Q)) :=
  simpleMilnorNorm_prime_tower_of_separable p hsep hp h f (z : MilnorKRing Q)

example (x : MilnorKTheory H 0) :
    simpleMilnorNorm h (x : MilnorKRing H) =
      simpleMilnorNorm p
        (simpleMilnorNorm q.1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2)
            (x : MilnorKRing H))) :=
  simpleMilnorNorm_eq_prime_tower_of_separable p hsep hp h f (x : MilnorKRing H)

/-- The norm tower uses the factor with the actual multiplicative degree formula. -/
example : (poly q.1.2).natDegree * d = e := by
  simpa only [natDegree_eq] using
    AdjoinRoot.towerFactor_natDegree_mul_natDegree (poly p) (poly h) f

/-- Its degree drops because the original lower degree is prime. -/
example : (poly q.1.2).natDegree < e := by
  have hdeg : 1 < (poly p).natDegree := by
    rw [natDegree_eq]
    exact hp.one_lt
  simpa only [natDegree_eq h] using
    AdjoinRoot.towerFactor_natDegree_lt (poly p) (poly h) f hdeg

end Tower

end
