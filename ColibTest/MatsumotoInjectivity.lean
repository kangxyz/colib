/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.KTheory.MilnorK.Steinberg.Equivalence
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.RatFunc.Basic

/-! Checks on the concrete Bruhat detector and canonical kernel equivalence. -/

noncomputable section

universe u v

open StableSteinberg

variable {F : Type u} [Field F]

example : Function.Injective (milnorToKernel F) := milnorToKernel_injective F

example : Function.Bijective (milnorToKernel F) := milnorToKernel_bijective F

example : (milnorKernelEquiv F).toAddMonoidHom = milnorToKernel F := rfl

example (a b : Fˣ) :
    milnorKernelEquiv F (milnorKTupleSymbol ![a, b]) =
      Additive.ofMul (torusDefectKernel a b) := milnorKernelEquiv_pair F a b

example (a b : Fˣ) :
    (milnorKernelEquiv F).symm (Additive.ofMul (torusDefectKernel a b)) =
      milnorKTupleSymbol ![a, b] := milnorKernelEquiv_symm_torusDefectKernel F a b

example {L : Type v} [Field L] (f : F →+* L) :
    ((toElementaryKernelMap f).toAdditive).comp (milnorKernelEquiv F).toAddMonoidHom =
      (milnorKernelEquiv L).toAddMonoidHom.comp (milnorKTheoryMap f 2).toAddMonoidHom :=
  milnorKernelEquiv_naturality f

example (n : ℕ) (hn : 3 ≤ n) (a b : Fˣ) :
    CommutatorDetectorTransfer.finiteCommutator (RootCoordinate.finiteRootOperator F) n hn a b =
      RootCoordinate.finiteCoefficientOperator F n
        (Multiplicative.ofAdd (milnorKTupleSymbol ![a, b])) :=
  RootCoordinate.finiteRootOperator_commutator_mark F n hn a b

section CharacteristicTwo

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

example : Function.Injective (milnorToKernel (RatFunc (ZMod 2))) := by
  let _ : Infinite (RatFunc (ZMod 2)) :=
    Infinite.of_injective _ (RatFunc.algebraMap_injective (ZMod 2))
  exact milnorToKernel_injective_of_infinite _

end CharacteristicTwo
