/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.ProjectiveLineCompactification
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineIntegral
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Nonempty infinity in the actual finite projective-line compactification

A nonempty étale chart has dense image in the polynomial line over a domain. If the same
coordinate map extends to a finite projective-line map, that extension is surjective.
Consequently its actual infinity pullback is surjective over the original base, so infinity
cannot disappear after a nonempty base restriction. Finiteness alone would not suffice.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite projective-line map extending a nonempty étale affine chart is surjective. -/
theorem surjective_projectiveLine_cover_of_etale_chart
    (R : Type u) [CommRing R] [IsDomain R]
    {V N : Scheme.{u}} [Nonempty V]
    (g : V ⟶ Spec (.of (Polynomial R))) [Etale g]
    (j : V ⟶ N) (π : N ⟶ projectiveLine R) [IsFinite π]
    (h : j ≫ π = g ≫ projectiveLineXChart R) : Surjective π := by
  have : IsDominant g := ⟨g.isOpenMap.isOpen_range.dense (Set.range_nonempty g)⟩
  have : IsDominant (projectiveLineXChart R) := ⟨denseRange_projectiveLineXChart R⟩
  have : IsDominant (j ≫ π) := by rw [h]; infer_instance
  have : IsDominant π := IsDominant.of_comp j π
  infer_instance

/-- The actual principal localization of the original polynomial coordinate map suffices.
The original affine source, compactification and coordinate map are unchanged. -/
theorem surjective_projectiveLine_cover_of_etale_away
    (R B : Type u) [CommRing R] [IsDomain R] [CommRing B] [IsDomain B]
    (f : Polynomial R →+* B) (r : B) (hr : r ≠ 0)
    (he : ((algebraMap B (Localization.Away r)).comp f).Etale)
    {N : Scheme.{u}} (i : Spec (.of B) ⟶ N) (π : N ⟶ projectiveLine R) [IsFinite π]
    (h : i ≫ π = Spec.map (CommRingCat.ofHom f) ≫ projectiveLineXChart R) : Surjective π := by
  let j := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away r)))
  let g := Spec.map (CommRingCat.ofHom ((algebraMap B (Localization.Away r)).comp f))
  have : IsDomain (Localization.Away r) := Localization.Away.isDomain hr
  have : Etale g := HasRingHomProperty.Spec_iff.mpr he
  apply surjective_projectiveLine_cover_of_etale_chart R g (j ≫ i) π
  rw [Category.assoc, h, ← Category.assoc]
  congr 1
  exact (Spec.map_comp _ _).symm

/-- The original scheme-theoretic infinity pullback meets every fiber of a surjective cover. -/
theorem surjective_infinity_pullback
    (R : Type u) [CommRing R]
    {N D : Scheme.{u}} (π : N ⟶ projectiveLine R) [Surjective π]
    (b : D ⟶ N) (e : D ⟶ Spec (.of R))
    (h : IsPullback b e π (projectiveLineInfinitySection R)) : Surjective e :=
  MorphismProperty.of_isPullback h inferInstance

end AlgebraicGeometry.Scheme
