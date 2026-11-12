/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.StalkwiseRegular
public import StacksFrontier.AlgebraicGeometry.F6Rank89.StalkDimension
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk

/-! # Cartier regularity on an open containing the whole support -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- An ideal is Cartier when it is Cartier on an open containing its whole
closed support. The generator of each stalk is transported through that
point's actual local-ring isomorphism. -/
theorem isEffectiveCartierDivisor_of_whole_support {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (j : Y ⟶ X) [IsOpenImmersion j] (I : X.IdealSheafData)
    (hs : Set.range I.subschemeι ⊆ Set.range j) (hI : IsEffectiveCartierDivisor (I.comap j)) :
    IsEffectiveCartierDivisor I := by
  apply isEffectiveCartierDivisor_of_stalk_regular_principal I
  intro x hx
  obtain ⟨y, rfl⟩ := hs (by rwa [I.range_subschemeι])
  let e := (asIso (j.stalkMap y)).commRingCatIsoToRingEquiv
  obtain ⟨a, ha, hspan⟩ := exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor
    (I.comap j) hI y
  refine ⟨e.symm a, isRegular_ringEquiv e.symm ha, ?_⟩
  apply e.idealComapOrderIso.symm.injective
  simp only [RingEquiv.idealComapOrderIso_symm_apply]
  rw [Ideal.map_span, Set.image_singleton, e.apply_symm_apply]
  exact (IdealSheafData.stalk_comap I j y).symm.trans hspan

end AlgebraicGeometry
