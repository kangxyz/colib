/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Norm.AcrossUniversesFinite

noncomputable section

open IntermediateField Stacks.Chow

universe u v w

example {k M L : Type u} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L]
    (n : ℕ) :
    (milnorKNorm k M n).comp (milnorKNorm M L n) = milnorKNorm k L n :=
  milnorKNorm_comp_milnorKNorm_of_finite n

example (k L : Type u) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    (a : L) (x : MilnorKRing L) :
    milnorKNormRing k L x =
      milnorKNormAdjoinSimple k (Algebra.IsIntegral.isIntegral a)
        (milnorKNormRing k⟮a⟯ L x) :=
  milnorKNormRing_eq_adjoinSimple_step_of_finite k L a x

example {k : Type u} {M : Type v} {L : Type w} [Field k] [Field M] [Field L]
    [Algebra k M] [Algebra M L] [Algebra k L] [IsScalarTower k M L]
    [FiniteDimensional k M] [FiniteDimensional M L] [FiniteDimensional k L]
    (x : MilnorKTheory L 0) :
    milnorKNormAcross k M 0 (milnorKNormAcross M L 0 x) = milnorKNormAcross k L 0 x :=
  milnorKNormAcross_tower_of_finite 0 x

end
