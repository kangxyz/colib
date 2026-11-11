/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# Purely inseparable scalar images of root fields

When a purely inseparable root presentation stays irreducible after a
change of coefficients, the actual new root field is purely inseparable.
The root-power relation is transported by the literal quotient map.
-/

@[expose] public noncomputable section

open Polynomial IntermediateField

namespace AdjoinRoot

/-- A purely inseparable root field stays purely inseparable under any
coefficient change that preserves irreducibility. -/
theorem isPurelyInseparable_map_of_isPurelyInseparable
    {k K : Type*} [Field k] [Field K] [Algebra k K] {f : k[X]}
    [Fact (Irreducible f)] [Fact (Irreducible (f.map (algebraMap k K)))]
    [IsPurelyInseparable k (AdjoinRoot f)] :
    IsPurelyInseparable K (AdjoinRoot (f.map (algebraMap k K))) := by
  obtain ⟨p, _⟩ := ExpChar.exists k
  let : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k K).injective p
  let q := f.map (algebraMap k K)
  let j : AdjoinRoot f →+* AdjoinRoot q := AdjoinRoot.map (algebraMap k K) f q dvd_rfl
  obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem k p (AdjoinRoot.root f)
  have hj := congrArg j hc
  change j (AdjoinRoot.of f c) = j (AdjoinRoot.root f ^ (p ^ n)) at hj
  dsimp only [j] at hj
  rw [AdjoinRoot.map_of, map_pow, AdjoinRoot.map_root] at hj
  have hroot : AdjoinRoot.root q ∈ perfectClosure K (AdjoinRoot q) :=
    (mem_perfectClosure_iff_pow_mem p).2 ⟨n, algebraMap k K c, hj⟩
  apply isPurelyInseparable_iff_perfectClosure_eq_top.mpr
  apply top_unique
  rw [← IntermediateField.adjoin_root_eq_top q]
  exact IntermediateField.adjoin_simple_le_iff.mpr hroot

end AdjoinRoot

end
