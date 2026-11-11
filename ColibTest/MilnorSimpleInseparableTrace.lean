/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.SimpleInseparableTrace

/-! Exact consumers of the native simple and adjoining norm trace formulas. -/

noncomputable section

open Polynomial Module IntermediateField Stacks.Chow
open MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L]

example {d : ℕ} (p : MonicIrreducibleOfDegree K d)
    (e : L ≃ₐ[K] (K[X] ⧸ Ideal.span {poly p})) (x : MilnorKRing L) :
    milnorKRingMap (algebraMap K L)
      (simpleMilnorNorm p (milnorKRingMap e.toRingHom x)) = (d : ℤ) • x :=
  milnorKRingMap_simpleMilnorNorm_of_isPurelyInseparable p e x

example {a : L} (ha : IsIntegral K a) (x : MilnorKRing K⟮a⟯) :
    milnorKRingMap (algebraMap K K⟮a⟯) (milnorKNormAdjoinSimple K ha x) =
      (finrank K K⟮a⟯ : ℤ) • x :=
  milnorKRingMap_milnorKNormAdjoinSimple_of_isPurelyInseparable ha x

example {a : L} (ha : IsIntegral K a) :
    (milnorKRingMap (algebraMap K K⟮a⟯)).toAddMonoidHom.comp
        (milnorKNormAdjoinSimple K ha) =
      (finrank K K⟮a⟯ : ℤ) • AddMonoidHom.id (MilnorKRing K⟮a⟯) := by
  ext x
  exact milnorKRingMap_milnorKNormAdjoinSimple_of_isPurelyInseparable ha x

example {a : L} (ha : IsIntegral K a) (n : ℕ) (x : MilnorKTheory K⟮a⟯ n) :
    milnorKRingMap (algebraMap K K⟮a⟯)
      (milnorKNormAdjoinSimple K ha (x : MilnorKRing K⟮a⟯)) =
        (finrank K K⟮a⟯ : ℤ) • (x : MilnorKRing K⟮a⟯) :=
  milnorKRingMap_milnorKNormAdjoinSimple_of_isPurelyInseparable ha _

end
