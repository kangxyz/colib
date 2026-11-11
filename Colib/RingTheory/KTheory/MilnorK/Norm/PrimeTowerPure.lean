/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TowerFactor
public import Colib.RingTheory.KTheory.MilnorK.Norm.PrimeDiamondPure
import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport

/-!
# The native simple-norm tower step in purely inseparable prime degree

The actual lower-field embedding selects a tensor factor whose matched factor is
linear. The degree-one norm acts by the original linear quotient equivalence.
Its composite with the tensor-swap map is the original tower factor equivalence.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

local instance primeTowerPure_irreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

variable {k : Type u} [Field k] {d e : ℕ}

private theorem primeTowerPure_simpleMilnorNorm_eq_map_of_natDegree_eq_one
    (q : MonicIrreducibleOfDegree k d) (hq : (poly q).natDegree = 1)
    (ε : AdjoinRoot (poly q) ≃ₐ[k] k) (z : MilnorKRing (AdjoinRoot (poly q))) :
    simpleMilnorNorm q z = milnorKRingMap ε.toRingHom z := by
  have hd : d = 1 := (natDegree_eq q).symm.trans hq
  subst d
  exact simpleMilnorNorm_eq_map_of_degree_one q ε z

variable (p : MonicIrreducibleOfDegree k d) (hp : d.Prime)
  [hPure : IsPurelyInseparable k (AdjoinRoot (poly p))] (h : MonicIrreducibleOfDegree k e)
  (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))

include hp hPure

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)
local notation "q" => AdjoinRoot.towerFactor (poly p) (poly h) f
local notation "Q" => AdjoinRoot (poly q.1.2)

/-- The prime-pure lower step on the original upper polynomial quotient. -/
theorem simpleMilnorNorm_prime_tower_of_isPurelyInseparable (z : MilnorKRing Q) :
    simpleMilnorNorm p (simpleMilnorNorm q.1.2 z) =
      simpleMilnorNorm h
        (milnorKRingMap (AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom z) := by
  let r := AdjoinRoot.tensorSwapFactorIndexEquiv (poly p) (poly h) q
  let η := AdjoinRoot.tensorSwapFactorQuotientEquiv (poly p) (poly h) q
  let ε := AdjoinRoot.towerFactorTargetEquiv (poly p) (poly h) f
  have hdiamond := simpleMilnorNorm_prime_diamond_of_isPurelyInseparable p hp h q z
  have hlinear := primeTowerPure_simpleMilnorNorm_eq_map_of_natDegree_eq_one r.1.2
    (AdjoinRoot.towerFactor_matched_natDegree (poly p) (poly h) f) ε
    (milnorKRingMap η.toRingHom z)
  have hcomp := milnorKRingMap_comp_apply η.toRingHom ε.toRingHom z
  exact hdiamond.trans (congrArg (simpleMilnorNorm h) (hlinear.trans hcomp))

/-- The simple norm on the original top field factors through the literal
coefficient-factor map for a purely inseparable prime lower extension. -/
theorem simpleMilnorNorm_eq_prime_tower_of_isPurelyInseparable (x : MilnorKRing H) :
    simpleMilnorNorm h x =
      simpleMilnorNorm p
        (simpleMilnorNorm q.1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2) x)) := by
  let φ := AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2
  let η := AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f
  have hcomp : η.toRingHom.comp φ = RingHom.id H :=
    RingHom.ext (AdjoinRoot.towerFactorRingEquiv_map (poly p) (poly h) f)
  have hmap : milnorKRingMap η.toRingHom (milnorKRingMap φ x) = x :=
    (milnorKRingMap_comp_apply φ η.toRingHom x).trans
      ((congrArg (fun ψ : H →+* H => milnorKRingMap ψ x) hcomp).trans
        (milnorKRingMap_id_apply x))
  exact ((simpleMilnorNorm_prime_tower_of_isPurelyInseparable p hp h f
    (milnorKRingMap φ x)).trans (congrArg (simpleMilnorNorm h) hmap)).symm

/-- Equality of the actual additive norm maps on the original top field. -/
theorem simpleMilnorNorm_eq_comp_prime_tower_of_isPurelyInseparable :
    @Eq (MilnorKRing H →+ MilnorKRing k) (simpleMilnorNorm h)
      ((simpleMilnorNorm p).comp
        ((simpleMilnorNorm q.1.2).comp
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly q.1.2) q.2)).toAddMonoidHom)) := by
  refine AddMonoidHom.ext (M := MilnorKRing H) (N := MilnorKRing k) ?_
  intro x
  exact simpleMilnorNorm_eq_prime_tower_of_isPurelyInseparable p hp h f x

end Stacks.Chow

end
