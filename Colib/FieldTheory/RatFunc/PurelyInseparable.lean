/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.IntermediateField.CompositumImage
public import Colib.FieldTheory.RatFunc.AlgebraMap
public import Colib.FieldTheory.RatFunc.CoefficientMap
public import Mathlib.FieldTheory.RatFunc.IntermediateField

/-!
# Purely inseparable rational coefficient extension

The native rational function field over the upper coefficients is generated
by the image of the original rational function field and the upper constants.
Pure inseparability of that compositum uses the actual rational coefficient map.
-/

@[expose] public noncomputable section

open IntermediateField
open scoped RatFunc nonZeroDivisors
attribute [local instance] Polynomial.algebra

namespace RatFunc

variable {k E : Type*} [Field k] [Field E] [Algebra k E]

/-- A purely inseparable extension of constants induces a purely inseparable
extension on the original rational function fields. -/
theorem isPurelyInseparable_ratFunc [IsPurelyInseparable k E] :
    IsPurelyInseparable (RatFunc k) (RatFunc E) := by
  let A := RatFunc k
  let D := RatFunc E
  let C := IntermediateField.adjoin E (Set.range (algebraMap A D))
  let : Algebra A C := (adjoinRangeFactor A E D).toAlgebra
  let : IsPurelyInseparable A C := isPurelyInseparable_adjoin_range k A E D
  have hX : algebraMap A D (RatFunc.X : RatFunc k) = (RatFunc.X : RatFunc E) := by
    change algebraMap (RatFunc k) (RatFunc E) (RatFunc.X : RatFunc k) = _
    rw [RatFunc.algebraMap_eq_mapRingHom, ← RatFunc.algebraMap_X,
      RatFunc.mapRingHom_algebraMap]
    change algebraMap (Polynomial E) (RatFunc E)
      ((Polynomial.X : Polynomial k).map (algebraMap k E)) = RatFunc.X
    rw [Polynomial.map_X, RatFunc.algebraMap_X]
  have htop : C = ⊤ := by
    apply top_unique
    rw [← RatFunc.adjoin_X]
    exact IntermediateField.adjoin_simple_le_iff.mpr
      (IntermediateField.subset_adjoin E (Set.range (algebraMap A D)) ⟨_, hX⟩)
  obtain ⟨p, _⟩ := ExpChar.exists A
  apply (isPurelyInseparable_iff_pow_mem A p).2
  intro x
  have hx : x ∈ C := by
    rw [htop]
    exact IntermediateField.mem_top
  let y : C := ⟨x, hx⟩
  obtain ⟨n, z, hz⟩ := IsPurelyInseparable.pow_mem A p y
  refine ⟨n, z, ?_⟩
  change algebraMap C D (algebraMap A C z) = (algebraMap C D y) ^ (p ^ n)
  rw [hz, map_pow]

end RatFunc

end
