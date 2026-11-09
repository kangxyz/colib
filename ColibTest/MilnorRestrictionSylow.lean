module

import Colib.RingTheory.KTheory.MilnorK.RestrictionSylow

open Stacks.Chow

universe u

variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω]
  [FiniteDimensional k Ω] [IsGalois k Ω]

-- The restrictions are the actual native maps to literal fixed fields.
example (x : MilnorKRing k)
    (hx : ∀ (p : ℕ) (_hp : p.Prime), ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
      milnorKRingMap (algebraMap k
        (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) x = 0) : x = 0 :=
  eq_zero_of_milnorKRingMap_sylow_restrictions k Ω x hx

example (x y : MilnorKRing k)
    (hxy : ∀ (p : ℕ) (_hp : p.Prime), ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
      milnorKRingMap (algebraMap k
        (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) x =
      milnorKRingMap (algebraMap k
        (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) y) : x = y :=
  eq_of_milnorKRingMap_sylow_restrictions k Ω x y hxy

example (n : ℕ) (x : MilnorKTheory k n)
    (hx : ∀ (p : ℕ) (_hp : p.Prime), ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
      milnorKTransport (algebraMap k
        (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) n x = 0) : x = 0 :=
  eq_zero_of_milnorKTransport_sylow_restrictions k Ω n x hx

-- Degree zero and arbitrary characteristic are still part of equality detection.
example (x y : MilnorKTheory k 0)
    (hxy : ∀ (p : ℕ) (_hp : p.Prime), ∃ S : Sylow p (Ω ≃ₐ[k] Ω),
      milnorKTransport (algebraMap k
        (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) 0 x =
      milnorKTransport (algebraMap k
        (IntermediateField.fixedField (S : Subgroup (Ω ≃ₐ[k] Ω)))) 0 y) : x = y :=
  eq_of_milnorKTransport_sylow_restrictions k Ω 0 x y hxy
