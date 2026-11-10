/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TowerFactor
public import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport
public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeDiamond

/-!
# The native normal-prime base step for simple-norm towers

The complete native prime diamond specializes at the actual factor selected by a
field embedding. Its opposite factor has degree one by construction. The existing
degree-one simple norm is its actual algebra equivalence, so the two original
quotient maps compose to the constructed top-field equivalence.

Both whole-ring identities and equalities of additive maps retain the original
`simpleMilnorNorm`, `milnorKRingMap` and literal `AdjoinRoot.map`. No tower law,
norm-compatibility square or general presentation-independence premise is assumed.
The lower degree is prime and its quotient extension is normal in characteristic
zero; the top polynomial and its given embedding are otherwise arbitrary.

The proof route is adapted from `Aglib/KTheory/MilnorK/Norm/Polynomial/PrimeTower.lean`
at revision `52e09db47998f139064acf48a2d3a64494d0dd9a`. Its alternate branch, norm and
Milnor K models are neither imported nor copied. All carriers and maps are native.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

local instance primeTower_nativeIrreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

variable {k : Type u} [Field k] {d e : ℕ}

/-- An actual degree-one polynomial has the existing simple norm induced by any
of its base-field algebra equivalences, even when its native degree index is arbitrary. -/
theorem simpleMilnorNorm_eq_map_of_natDegree_eq_one
    (q : MonicIrreducibleOfDegree k d) (hq : (poly q).natDegree = 1)
    (ε : AdjoinRoot (poly q) ≃ₐ[k] k) (z : MilnorKRing (AdjoinRoot (poly q))) :
    simpleMilnorNorm q z = milnorKRingMap ε.toRingHom z := by
  have hd : d = 1 := (natDegree_eq q).symm.trans hq
  subst d
  exact simpleMilnorNorm_eq_map_of_degree_one q ε z

section LinearFactor

variable [CharZero k] (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))] (h : MonicIrreducibleOfDegree k e)

include hp

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)

/-- A linear actual matched factor collapses the whole native prime diamond.
The resulting top-field map is the composite of the two literal equivalences. -/
theorem simpleMilnorNorm_prime_tower_of_linear_factor
    (q : {q : Σ f : ℕ, MonicIrreducibleOfDegree E f //
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
            ε.toRingEquiv).toRingHom z) := by
  rw [simpleMilnorNorm_prime_diamond p hp h q z,
    simpleMilnorNorm_eq_map_of_natDegree_eq_one _ hr ε]
  exact congrArg (simpleMilnorNorm h)
    (milnorKRingMap_comp_apply
      (AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q).toRingHom
      ε.toRingHom z)

end LinearFactor

section Tower

variable [CharZero k] (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
  [Normal k (AdjoinRoot (poly p))] (h : MonicIrreducibleOfDegree k e)
  (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))

include hp

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)
local notation "q" => AdjoinRoot.towerFactor (poly p) (poly h) f
local notation "Q" => AdjoinRoot (poly q.1.2)

/-- The actual normal-prime base tower on the whole native Milnor K-ring.
The upper factor and its top-field equivalence are constructed from the given embedding. -/
theorem simpleMilnorNorm_prime_tower (z : MilnorKRing Q) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 z) =
      simpleMilnorNorm h
        (milnorKRingMap (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom z) :=
  simpleMilnorNorm_prime_tower_of_linear_factor p hp h q
    (AdjoinRoot.towerFactor_matched_natDegree (poly p) (poly h) f)
    (AdjoinRoot.towerFactorTargetEquiv (poly p) (poly h) f) z

/-- On the original top field, the native simple norm factors through the actual
normal-prime subfield using the literal inverse coefficient-factor map. -/
theorem simpleMilnorNorm_eq_prime_tower (x : MilnorKRing H) :
    simpleMilnorNorm h x =
      simpleMilnorNorm p
        (simpleMilnorNorm q.1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2) x)) := by
  rw [simpleMilnorNorm_prime_tower p hp h f]
  apply congrArg (simpleMilnorNorm h)
  rw [← AdjoinRoot.towerFactorRingEquiv_symm_toRingHom, milnorKRingMap_comp_apply]
  have hcomp :
      (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom.comp
          (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).symm.toRingHom =
        RingHom.id H := by
    apply RingHom.ext
    intro a
    exact (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).apply_symm_apply a
  exact ((congrArg (fun φ : H →+* H => milnorKRingMap φ x) hcomp).trans
    (milnorKRingMap_id_apply x)).symm

/-- Equality of the original additive maps on the constructed upper quotient. -/
theorem simpleMilnorNorm_comp_simpleMilnorNorm_prime_tower :
    (simpleMilnorNorm p).comp (simpleMilnorNorm q.1.2) =
      (simpleMilnorNorm h).comp
        (milnorKRingMap
          (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom).toAddMonoidHom := by
  ext z
  exact simpleMilnorNorm_prime_tower p hp h f z

/-- Equality of the original additive maps on the original top field. -/
theorem simpleMilnorNorm_eq_comp_prime_tower :
    simpleMilnorNorm h =
      (simpleMilnorNorm p).comp
        ((simpleMilnorNorm q.1.2).comp
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2)).toAddMonoidHom) := by
  ext x
  exact simpleMilnorNorm_eq_prime_tower p hp h f x

end Tower

end Stacks.Chow

end
