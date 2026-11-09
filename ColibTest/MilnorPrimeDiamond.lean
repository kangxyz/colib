module

import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeDiamond

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
open scoped RatFunc
attribute [local instance] Polynomial.algebra Ideal.Quotient.field

universe u

local instance consumer_nativeIrreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance consumer_rootFinite {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Module.Finite F (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance consumer_rationalFinite {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) :
    Module.Finite (RatFunc F) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable {k : Type u} [Field k] [CharZero k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))] (h : MonicIrreducibleOfDegree k e)
  (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree (AdjoinRoot (poly p)) f //
    poly q.2 ∣ (poly h).map (algebraMap k (AdjoinRoot (poly p)))})

/-- The lift is supplied by the native surjectivity theorem, not as a hypothesis. -/
example (n : ℕ) (z : MilnorKTheory (AdjoinRoot (poly q.1.2)) n) :
    ∃ x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1),
      IsSingleResidueLift q.1.2 (z : MilnorKRing (AdjoinRoot (poly q.1.2))) (x : MilnorKRing _) ∧
      simpleMilnorNorm p (simpleMilnorNorm q.1.2 (z : MilnorKRing (AdjoinRoot (poly q.1.2)))) =
        -infinityResidueRing k
          (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x :
            MilnorKRing (RatFunc k)) :=
  exists_isSingleResidueLift_simpleMilnorNorm_simpleMilnorNorm p hp q.1.2 n z

/-- Every homogeneous degree is retained for arbitrary lower polynomial and factor. -/
example (n : ℕ) (z : MilnorKTheory (AdjoinRoot (poly q.1.2)) n) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 (z : MilnorKRing (AdjoinRoot (poly q.1.2)))) =
      simpleMilnorNorm h
        (simpleMilnorNorm
          (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2
          (milnorKRingMap
            (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom
            (z : MilnorKRing (AdjoinRoot (poly q.1.2))))) :=
  simpleMilnorNorm_prime_diamond_homogeneous p hp h q n z

/-- Degree zero is included, with no positivity hypothesis on the Milnor degree. -/
example (z : MilnorKTheory (AdjoinRoot (poly q.1.2)) 0) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 (z : MilnorKRing (AdjoinRoot (poly q.1.2)))) =
      simpleMilnorNorm h
        (simpleMilnorNorm
          (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2
          (milnorKRingMap
            (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom
            (z : MilnorKRing (AdjoinRoot (poly q.1.2))))) :=
  simpleMilnorNorm_prime_diamond_homogeneous p hp h q 0 z

/-- The full-ring statement requires neither a degree nor any supplied lift. -/
example (z : MilnorKRing (AdjoinRoot (poly q.1.2))) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 z) =
      simpleMilnorNorm h
        (simpleMilnorNorm
          (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2
          (milnorKRingMap
            (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom z)) :=
  simpleMilnorNorm_prime_diamond p hp h q z

/-- An arbitrary homogeneous lift contracts under the original chosen rational norm. -/
example (n : ℕ) (z : MilnorKRing (AdjoinRoot (poly q.1.2)))
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1))
    (hx : IsSingleResidueLift q.1.2 z (x : MilnorKRing _)) :
    IsSingleResidueLift h
      (simpleMilnorNorm
        (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2
        (milnorKRingMap
          (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom z))
      (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) (n + 1) x :
        MilnorKRing (RatFunc k)) :=
  IsSingleResidueLift.milnorKNorm_ratFunc_tensorSwap p hp h q z n x hx

/-- Both paths are the same original additive map on the actual upper quotient. -/
example :
    (simpleMilnorNorm p).comp (simpleMilnorNorm q.1.2) =
      (simpleMilnorNorm h).comp
        ((simpleMilnorNorm
          (AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q).1.2).comp
          (milnorKRingMap
            (AdjoinRoot.tensorSwapFactorQuotientEquiv
              (poly p) (poly h) q).toRingHom).toAddMonoidHom) :=
  simpleMilnorNorm_comp_simpleMilnorNorm_prime_diamond p hp h q

end
