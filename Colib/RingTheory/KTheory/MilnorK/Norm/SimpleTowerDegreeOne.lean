/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TowerFactor
public import Colib.RingTheory.KTheory.MilnorK.Norm.PresentationSupport

/-!
# Native simple-norm towers with degree-one lower field

Degree multiplication and monic divisibility identify the actual selected factor
with the literal coefficient image of the top polynomial. The native coefficient
norm formula and projection formula then give the whole-ring tower identity.
No characteristic, normality, prime-degree or ambient-field assumption is used.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

local instance simpleTowerDegreeOne_nativeIrreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

variable {k : Type u} [Field k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
  (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)
section DegreeOne

attribute [local instance] Ideal.Quotient.field

local notation "qD" => AdjoinRoot.towerFactor (poly p) (poly h) f

/-- A degree-one lower field makes the selected factor the literal coefficient image. -/
theorem towerFactor_poly_eq_map_of_lower_natDegree_eq_one
    (hp : (poly p).natDegree = 1) :
    poly qD.1.2 = (poly h).map (algebraMap k E) := by
  have hdegree := AdjoinRoot.towerFactor_natDegree_mul_natDegree (poly p) (poly h) f
  rw [hp, mul_one] at hdegree
  apply (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (monic qD.1.2)
    ((monic h).map (algebraMap k E)) qD.2 ?_).symm
  simpa only [Polynomial.natDegree_map, hdegree] using
    (le_rfl : (poly h).natDegree ≤ (poly h).natDegree)

/-- The whole-ring native tower when the actual lower polynomial has degree one. -/
theorem simpleMilnorNorm_eq_tower_of_lower_natDegree_eq_one
    (hp : (poly p).natDegree = 1) (x : MilnorKRing H) :
    simpleMilnorNorm h x =
      simpleMilnorNorm p
        (simpleMilnorNorm qD.1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k E) (poly h) (poly qD.1.2) qD.2) x)) := by
  have hd : d = 1 := (natDegree_eq p).symm.trans hp
  have hone : simpleMilnorNorm p 1 = (1 : MilnorKRing k) := by
    simpa only [hd, Nat.cast_one, one_zsmul] using simpleMilnorNorm_one p
  have hprojection (y : MilnorKRing k) :
      simpleMilnorNorm p
        (milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p})) y) = y :=
    (congrArg (simpleMilnorNorm p)
      (mul_one (milnorKRingMap (algebraMap k (k[X] ⧸ Ideal.span {poly p})) y)).symm).trans
      ((simpleMilnorNorm_map_mul p y 1).trans
        ((congrArg (fun z : MilnorKRing k => y * z) hone).trans (mul_one y)))
  have hmap := simpleMilnorNorm_map_of_poly_eq_map (algebraMap k E) h qD.1.2
    (towerFactor_poly_eq_map_of_lower_natDegree_eq_one p h f hp) x
  exact (hprojection (simpleMilnorNorm h x)).symm.trans
    (congrArg (simpleMilnorNorm p) hmap)

end DegreeOne

end Stacks.Chow

end
