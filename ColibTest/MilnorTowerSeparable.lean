/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.TowerSeparable

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

universe u

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- There is no ambient, prime-degree, normality or norm-comparison hypothesis. -/
example
    {k : Type u} [Field k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (hhsep : (poly h).Separable)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h)) (x : MilnorKRing (AdjoinRoot (poly
      (Sigma.snd (Subtype.val (AdjoinRoot.towerFactor (poly p) (poly h) f)))))) :
    simpleMilnorNorm p (simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2 x) =
      simpleMilnorNorm h (milnorKRingMap ((AdjoinRoot.towerFactorRingEquiv (poly p) (poly h)
      f)).toRingHom x) :=
  simpleMilnorNorm_tower_of_separable p h hhsep f x

/-- The original top quotient uses exactly the native inverse coefficient-factor map. -/
example
    {k : Type u} [Field k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (hhsep : (poly h).Separable)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h)) (x : MilnorKRing (AdjoinRoot (poly h))) :
    simpleMilnorNorm h x =
      simpleMilnorNorm p
        (simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k (AdjoinRoot (poly p))) (poly h) (poly
      (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2) (AdjoinRoot.towerFactor (poly p) (poly h)
      f).2) x)) :=
  simpleMilnorNorm_eq_tower_of_separable p h hhsep f x

example
    {k : Type u} [Field k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (hhsep : (poly h).Separable)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h)) :
    (simpleMilnorNorm p).comp (simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2) =
      (simpleMilnorNorm h).comp (milnorKRingMap ((AdjoinRoot.towerFactorRingEquiv (poly p) (poly h)
      f)).toRingHom).toAddMonoidHom :=
  simpleMilnorNorm_comp_simpleMilnorNorm_tower_of_separable p h hhsep f

example
    {k : Type u} [Field k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (hhsep : (poly h).Separable)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h)) :
    simpleMilnorNorm h =
      (simpleMilnorNorm p).comp
        ((simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2).comp
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k (AdjoinRoot (poly p))) (poly h) (poly
      (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2) (AdjoinRoot.towerFactor (poly p) (poly h)
      f).2)).toAddMonoidHom) :=
  simpleMilnorNorm_eq_comp_tower_of_separable p h hhsep f

/-- The quotient-side tower holds on every native homogeneous degree. -/
example
    {k : Type u} [Field k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (hhsep : (poly h).Separable)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h)) (n : ℕ) (x : MilnorKTheory (AdjoinRoot (poly
      (Sigma.snd (Subtype.val (AdjoinRoot.towerFactor (poly p) (poly h) f))))) n) :
    simpleMilnorNorm p (simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2 (x :
      MilnorKRing (AdjoinRoot (poly (Sigma.snd (Subtype.val (AdjoinRoot.towerFactor (poly p) (poly
      h) f))))))) =
      simpleMilnorNorm h (milnorKRingMap ((AdjoinRoot.towerFactorRingEquiv (poly p) (poly h)
      f)).toRingHom (x : MilnorKRing (AdjoinRoot (poly (Sigma.snd (Subtype.val
      (AdjoinRoot.towerFactor (poly p) (poly h) f))))))) :=
  simpleMilnorNorm_tower_of_separable p h hhsep f (x : MilnorKRing (AdjoinRoot (poly
    (Sigma.snd (Subtype.val
      (AdjoinRoot.towerFactor (poly p) (poly h) f))))))

/-- The original top-field statement also retains every native homogeneous degree. -/
example
    {k : Type u} [Field k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (hhsep : (poly h).Separable)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h)) (n : ℕ) (x : MilnorKTheory (AdjoinRoot (poly
      h)) n) :
    simpleMilnorNorm h (x : MilnorKRing (AdjoinRoot (poly h))) =
      simpleMilnorNorm p
        (simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k (AdjoinRoot (poly p))) (poly h) (poly
      (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2) (AdjoinRoot.towerFactor (poly p) (poly h)
      f).2)
            (x : MilnorKRing (AdjoinRoot (poly h))))) :=
  simpleMilnorNorm_eq_tower_of_separable p h hhsep f (x : MilnorKRing (AdjoinRoot (poly h)))

/-- Degree zero is part of the original whole-ring theorem. -/
example
    {k : Type u} [Field k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (hhsep : (poly h).Separable)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h)) (x : MilnorKTheory (AdjoinRoot (poly
      (Sigma.snd (Subtype.val (AdjoinRoot.towerFactor (poly p) (poly h) f))))) 0) :
    simpleMilnorNorm p (simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2 (x :
      MilnorKRing (AdjoinRoot (poly (Sigma.snd (Subtype.val (AdjoinRoot.towerFactor (poly p) (poly
      h) f))))))) =
      simpleMilnorNorm h (milnorKRingMap ((AdjoinRoot.towerFactorRingEquiv (poly p) (poly h)
      f)).toRingHom (x : MilnorKRing (AdjoinRoot (poly (Sigma.snd (Subtype.val
      (AdjoinRoot.towerFactor (poly p) (poly h) f))))))) :=
  simpleMilnorNorm_tower_of_separable p h hhsep f (x : MilnorKRing (AdjoinRoot (poly
    (Sigma.snd (Subtype.val
      (AdjoinRoot.towerFactor (poly p) (poly h) f))))))

example
    {k : Type u} [Field k] {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (hhsep : (poly h).Separable)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h)) (x : MilnorKTheory (AdjoinRoot (poly h)) 0)
      :
    simpleMilnorNorm h (x : MilnorKRing (AdjoinRoot (poly h))) =
      simpleMilnorNorm p
        (simpleMilnorNorm (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2
          (milnorKRingMap
            (AdjoinRoot.map (algebraMap k (AdjoinRoot (poly p))) (poly h) (poly
      (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2) (AdjoinRoot.towerFactor (poly p) (poly h)
      f).2)
            (x : MilnorKRing (AdjoinRoot (poly h))))) :=
  simpleMilnorNorm_eq_tower_of_separable p h hhsep f (x : MilnorKRing (AdjoinRoot (poly h)))

end
