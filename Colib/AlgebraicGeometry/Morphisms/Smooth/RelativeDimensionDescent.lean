/-
Copyright (c) 2026 Colib contributors and AxiomMath/Stacks contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.Smooth.RelativeDimensionNeighborhood
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Basic

/-!
# Relative dimension descends along a surjective base change

For an actual smooth morphism, a constant local fiber dimension determines its relative
smooth dimension. The proof extracts the lower smooth-chart argument of
`Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq` without importing the
Hilbert-scheme application that owns that native theorem. Fiber dimension is preserved by
base change, so a surjective base map detects the relative dimension of the original smooth
morphism. Smoothness itself is a separate hypothesis, to be supplied by flat descent.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A smooth morphism with constant local fiber dimension has that smooth relative dimension. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Picard/HilbertSchemeSmoothness.lean:143-175"
  "adaptation" "lower smooth-chart proof of the constant relative-dimension criterion"]
theorem Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    (n : ℕ) (h : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      (n : WithBot ℕ∞)) : SmoothOfRelativeDimension n f := by
  have hlocal (x : X) : ∃ V : X.Opens, x ∈ V ∧ SmoothOfRelativeDimension n (V.ι ≫ f) := by
    obtain ⟨V, hx, m, hm⟩ := Smooth.exists_relativeDimension_neighborhood f x
    have := hm
    have he := fiberDimensionAt_eq_of_smoothOfRelativeDimension (V.ι ≫ f) m ⟨x, hx⟩
    have hopen := fiberDimensionAt_eq_of_open_square V.ι f (V.ι ≫ f) (𝟙 Y)
      (by simp) ⟨x, hx⟩
    have hnm : n = m := by exact_mod_cast ((h x).symm.trans (hopen.symm.trans he))
    subst m
    exact ⟨V, hx, hm⟩
  choose V hx hV using hlocal
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{u} n)
      (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))
  apply IsZariskiLocalAtSource.of_iSup_eq_top V _ hV
  ext x
  exact ⟨fun _ => Set.mem_univ x, fun _ => Opens.mem_iSup.mpr ⟨x, hx x⟩⟩

/-- In the literal pullback square, a surjective base map detects the relative dimension of
an already smooth original morphism. -/
theorem SmoothOfRelativeDimension.of_surjective_isPullback
    {X' X Y' Y : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (f : X ⟶ Y) (g : Y' ⟶ Y) (h : IsPullback g' f' f g)
    [Smooth f] [Surjective g] (n : ℕ) [SmoothOfRelativeDimension n f'] :
    SmoothOfRelativeDimension n f := by
  have : Surjective g' := MorphismProperty.of_isPullback h.flip inferInstance
  apply Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq f n
  intro x
  obtain ⟨x', rfl⟩ := g'.surjective x
  rw [← topologicalKrullDimAt_fiber_eq_of_isPullback h x']
  exact fiberDimensionAt_eq_of_smoothOfRelativeDimension f' n x'

end AlgebraicGeometry
