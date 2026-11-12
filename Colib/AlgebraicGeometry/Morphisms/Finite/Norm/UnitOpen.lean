/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The open where both pairs of norm sections generate

A finite morphism maps the full source zero support to a closed set. Removing
this set and the target zero support gives the original common domain of the
coefficients. The criterion uses the entire inverse image of any boundary
scheme.

Adapted from `SectionPairNormParameterNeighborhood.lean` under
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Pencils/Norm` at
a6805c4a87cdfd7717dd7a94039246a167f15380.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Unit ideals on a covering family of whole inverse images detect the
unit ideal on the original scheme. -/
theorem IdealSheafData.eq_top_of_range_cover {ι : Type*} {T : Scheme.{u}}
    (I : T.IdealSheafData) {C : ι → Scheme.{u}} (f : ∀ i, C i ⟶ T)
    (hcover : ∀ x : T, ∃ i, x ∈ Set.range (f i)) (hI : ∀ i, I.comap (f i) = ⊤) :
    I = ⊤ := by
  apply (IdealSheafData.support_eq_bot_iff _).mp
  apply Closeds.ext
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hx
  obtain ⟨i, y, rfl⟩ := hcover x
  have hy : y ∈ ((I.comap (f i)).support : Set (C i)) := by
    rw [IdealSheafData.support_comap]
    exact hx
  rw [hI i, IdealSheafData.support_top, Closeds.coe_bot] at hy
  exact Set.notMem_empty y hy

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  (I : X.IdealSheafData) (J : Y.IdealSheafData)

/-- The entire target open where the target ideal and the whole inverse
source ideal are the unit ideals. -/
def normUnitOpen : Y.Opens :=
  ⟨((J.support : Set Y) ∪ f '' (I.support : Set X))ᶜ,
    (J.support.isClosed.union (f.isClosedMap _ I.support.isClosed)).isOpen_compl⟩

/-- Any map into the common open has both pulled-back unit ideals. Conversely,
those two unit ideals force the map to factor through the same original open. -/
theorem range_subset_normUnitOpen_iff {W : Scheme.{u}} (w : W ⟶ Y) :
    Set.range w ⊆ (normUnitOpen f I J : Set Y) ↔
      J.comap w = ⊤ ∧ I.comap (pullback.fst f w) = ⊤ := by
  constructor
  · intro h
    constructor
    · apply (IdealSheafData.support_eq_bot_iff _).mp
      apply Closeds.ext
      rw [IdealSheafData.support_comap]
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      exact h ⟨x, rfl⟩ (Or.inl hx)
    · apply (IdealSheafData.support_eq_bot_iff _).mp
      apply Closeds.ext
      rw [IdealSheafData.support_comap]
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      apply h ⟨pullback.snd f w x, rfl⟩
      right
      refine ⟨pullback.fst f w x, hx, ?_⟩
      exact congrArg (fun a ↦ a x) (pullback.condition (f := f) (g := w))
  · rintro ⟨hJ, hI⟩ _ ⟨x, rfl⟩ hx
    rcases hx with hx | ⟨y, hy, h⟩
    · have hx' : x ∈ (J.comap w).support := by
        rwa [IdealSheafData.support_comap]
      change x ∈ ((J.comap w).support : Set W) at hx'
      exact Set.notMem_empty x
        (by simpa only [hJ, IdealSheafData.support_top, Closeds.coe_bot] using hx')
    · obtain ⟨a, ha, -⟩ := Scheme.exists_preimage_of_isPullback
        (IsPullback.of_hasPullback f w) y x h
      have ha' : a ∈ (I.comap (pullback.fst f w)).support := by
        rw [IdealSheafData.support_comap]
        change pullback.fst f w a ∈ (I.support : Set X)
        rwa [ha]
      change a ∈ ((I.comap (pullback.fst f w)).support : Set (pullback f w : Scheme)) at ha'
      exact Set.notMem_empty a
        (by simpa only [hI, IdealSheafData.support_top, Closeds.coe_bot] using ha')

end AlgebraicGeometry.Scheme
