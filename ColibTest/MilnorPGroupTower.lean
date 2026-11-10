module

import Colib.RingTheory.KTheory.MilnorK.Norm.PGroupTower

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

universe u v

attribute [local instance] Stacks.Chow.towerTransport_nativeIrreducible

variable {k : Type u} [Field k] [CharZero k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
  (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
  {Ω : Type v} [Field Ω] [Algebra k Ω] [FiniteDimensional k Ω] [IsGalois k Ω]
  (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[k] Ω))
  (j : AdjoinRoot (poly h) →ₐ[k] Ω)

include hG j

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)
local notation "q" => AdjoinRoot.towerFactor (poly p) (poly h) f
local notation "Q" => AdjoinRoot (poly q.1.2)

/-- Arbitrary lower degree and the literal original coefficient-factor map. -/
example (x : MilnorKRing H) :
    simpleMilnorNorm h x =
      simpleMilnorNorm p
        (simpleMilnorNorm q.1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2) x)) :=
  simpleMilnorNorm_eq_pGroup_tower p h f ℓ hG j x

/-- The actual upper quotient version retains the actual top-field equivalence. -/
example (z : MilnorKRing Q) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 z) =
      simpleMilnorNorm h
        (milnorKRingMap (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom z) :=
  simpleMilnorNorm_pGroup_tower p h f ℓ hG j z

example :
    simpleMilnorNorm h =
      (simpleMilnorNorm p).comp
        ((simpleMilnorNorm q.1.2).comp
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2)).toAddMonoidHom) :=
  simpleMilnorNorm_eq_comp_pGroup_tower p h f ℓ hG j

example :
    (simpleMilnorNorm p).comp (simpleMilnorNorm q.1.2) =
      (simpleMilnorNorm h).comp
        (milnorKRingMap
          (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom).toAddMonoidHom :=
  simpleMilnorNorm_comp_simpleMilnorNorm_pGroup_tower p h f ℓ hG j

/-- Every homogeneous degree is covered, with no symbol-generation assumption. -/
example (n : ℕ) (x : MilnorKTheory H n) :
    simpleMilnorNorm h (x : MilnorKRing H) =
      simpleMilnorNorm p
        (simpleMilnorNorm q.1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2)
            (x : MilnorKRing H))) :=
  simpleMilnorNorm_eq_pGroup_tower p h f ℓ hG j (x : MilnorKRing H)

/-- Degree zero is retained. -/
example (z : MilnorKTheory Q 0) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 (z : MilnorKRing Q)) =
      simpleMilnorNorm h
        (milnorKRingMap (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom
          (z : MilnorKRing Q)) :=
  simpleMilnorNorm_pGroup_tower p h f ℓ hG j (z : MilnorKRing Q)

end
