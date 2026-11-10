module

import Colib.RingTheory.AdjoinRoot.TowerFactor

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

variable {k : Type*} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "q" => towerFactor p h f
local notation "r" => tensorSwapFactorIndexEquiv p h q
local notation "Q" => AdjoinRoot (poly q.1.2)

example : X - C (f (root p)) ∣ p.map (algebraMap k H) :=
  towerFactor_linear_dvd p h f

example : poly q.1.2 ∣ h.map (algebraMap k E) := q.2

example : poly r.1.2 = X - C (f (root p)) :=
  towerFactor_matched_poly p h f

example : (poly r.1.2).natDegree = 1 := towerFactor_matched_natDegree p h f

example (b : H) :
    towerFactorTargetEquiv p h f (algebraMap H (AdjoinRoot (poly r.1.2)) b) = b :=
  (towerFactorTargetEquiv p h f).commutes b

example (b : H) :
    towerFactorRingEquiv p h f
      (AdjoinRoot.map (algebraMap k E) h (poly q.1.2) q.2 b) = b :=
  towerFactorRingEquiv_map p h f b

example :
    (towerFactorRingEquiv p h f).symm.toRingHom =
      AdjoinRoot.map (algebraMap k E) h (poly q.1.2) q.2 :=
  towerFactorRingEquiv_symm_toRingHom p h f

example : towerFactorRingEquiv p h f (root (poly q.1.2)) = root h :=
  towerFactorRingEquiv_root p h f

example (a : E) : towerFactorRingEquiv p h f (algebraMap E Q a) = f a :=
  towerFactorRingEquiv_algebraMap p h f a

example : (towerFactorAlgEquiv p h f).toRingEquiv = towerFactorRingEquiv p h f := rfl

example (c : k) : towerFactorAlgEquiv p h f (algebraMap k Q c) = algebraMap k H c :=
  (towerFactorAlgEquiv p h f).commutes c

example : (poly q.1.2).natDegree * p.natDegree = h.natDegree :=
  towerFactor_natDegree_mul_natDegree p h f

example (hp : 1 < p.natDegree) : (poly q.1.2).natDegree < h.natDegree :=
  towerFactor_natDegree_lt p h f hp

example (x : Q) :
    AdjoinRoot.map (algebraMap k E) h (poly q.1.2) q.2 (towerFactorRingEquiv p h f x) = x := by
  rw [← towerFactorRingEquiv_symm_toRingHom]
  exact (towerFactorRingEquiv p h f).symm_apply_apply x
