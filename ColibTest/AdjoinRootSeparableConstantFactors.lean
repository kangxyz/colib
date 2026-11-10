/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.AdjoinRoot.SeparableConstantFactors
import Colib.RingTheory.KTheory.MilnorK.Norm.PolynomialResidueMap

noncomputable section

open Polynomial Stacks.Chow MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k]

-- The lower theorem permits an explicitly inseparable closed point.
example (p h : k[X]) [Fact (Irreducible p)] [Fact (Irreducible h)]
    (hp : p.Separable) (_hinseparable : ¬h.Separable) :
    Squarefree (h.map (algebraMap k (AdjoinRoot p))) :=
  AdjoinRoot.squarefree_map_of_separable_constant p h hp

variable {d e a : ℕ} (p : MonicIrreducibleOfDegree k d)
  (h : MonicIrreducibleOfDegree k e)

local instance : Fact (Irreducible (poly p)) := ⟨irreducible p⟩
local instance : Fact (Irreducible (poly h)) := ⟨irreducible h⟩

-- Consume the geometric multiplicity statement in the original whole-ring
-- polynomial residue map. No separability of h occurs in the statement.
set_option backward.isDefEq.respectTransparency false in
example (hp : (poly p).Separable)
    (q : MonicIrreducibleOfDegree (AdjoinRoot (poly p)) a)
    (hq : poly q ∣ (poly h).map (algebraMap k (AdjoinRoot (poly p))))
    (x : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue q
        (milnorKRingMap
          (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k (AdjoinRoot (poly p))))
            (Polynomial.nonZeroDivisors_le_comap_mapRingHom
              (algebraMap k (AdjoinRoot (poly p))))) x) =
      milnorKRingMap
        (AdjoinRoot.map (algebraMap k (AdjoinRoot (poly p))) (poly h) (poly q) hq)
        (monicIrreducibleResidue h x) := by
  have hm := AdjoinRoot.multiplicity_eq_one_of_dvd_map_separable_constant
    (poly p) (poly h) hp (poly q) (irreducible q) hq
  rw [monicIrreducibleResidue_mapRingHom
    (algebraMap k (AdjoinRoot (poly p))) h q hq x,
    hm, Nat.cast_one, one_zsmul]
  rfl
