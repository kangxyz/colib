/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.Topology.Prespectrum.SequentialColimitStable
import Colib.Topology.Prespectrum.HomotopyPushoutEmbedding
open CategoryTheory CategoryTheory.Limits Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.LoopPrespectrum.SequentialColimitBridgeTest
open SequentialColimit
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

example (i : ℕ) : f i ≫ inclusion E f (i + 1) = inclusion E f i :=
  successor_inclusion E f i

example (i : ℕ) : Telescope.inclusion E f i ≫ collapse E f = inclusion E f i :=
  inclusion_collapse E f i

example : IsColimit (cocone E f) := isColimit E f

variable (hc : ∀ i k, IsClosedEmbedding ((f i).map k))
variable [∀ i k, T1Space ((E i).space k)]
example : IsStableEquivalence (collapse E f) := collapse_isStableEquivalence E f hc

example {A B C : LoopPrespectrum.{u}} (a : A ⟶ B) (b : A ⟶ C) (k : ℕ)
    [T1Space (A.space k)] [T1Space (B.space k)] [T1Space (C.space k)] :
    IsClosedEmbedding ((HomotopyPushout.inl a b).map k) :=
  HomotopyPushout.isClosedEmbedding_inl a b k

end Topology.LoopPrespectrum.SequentialColimitBridgeTest
