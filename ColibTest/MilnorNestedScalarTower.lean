module

import Colib.RingTheory.KTheory.MilnorK.Norm.NestedScalarTower

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

universe u v

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

section Restriction

variable {k K : Type u} [Field k] [Field K] [CharZero k] [Algebra k K]
  {d e : ℕ} (p : MonicIrreducibleOfDegree k d)
  (h : MonicIrreducibleOfDegree k e)
  (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
  {Ω : Type v} [Field Ω] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
  [FiniteDimensional K Ω] [IsGalois K Ω]
  (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[K] Ω))
  (hsplit : ((poly h).map (algebraMap k Ω)).Splits)

include hG hsplit

local notation "q" => AdjoinRoot.towerFactor (poly p) (poly h) f
local notation "Q" => AdjoinRoot (poly (Sigma.snd (Subtype.val q)))
local notation "θ" => AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f

/-- No lower splitting or branch norm-compatibility assumptions are needed. -/
example (x : MilnorKRing Q) :
    milnorKRingMap (algebraMap k K) (simpleMilnorNorm p (simpleMilnorNorm q.1.2 x)) =
      milnorKRingMap (algebraMap k K)
        (simpleMilnorNorm h (milnorKRingMap (θ).toRingHom x)) :=
  simpleMilnorNorm_tower_map_of_pGroup_splitting p h f ℓ hG hsplit x

/-- The ambient universe is independent, including in each homogeneous degree. -/
example (n : ℕ) (x : MilnorKTheory Q n) :
    milnorKRingMap (algebraMap k K)
        (simpleMilnorNorm p (simpleMilnorNorm q.1.2 (x : MilnorKRing Q))) =
      milnorKRingMap (algebraMap k K)
        (simpleMilnorNorm h (milnorKRingMap (θ).toRingHom (x : MilnorKRing Q))) :=
  simpleMilnorNorm_tower_map_of_pGroup_splitting p h f ℓ hG hsplit (x : MilnorKRing Q)

end Restriction

end
