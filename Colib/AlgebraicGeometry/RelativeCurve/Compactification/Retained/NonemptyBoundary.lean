/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.BoundaryNeighborhood

/-!
# The full retained boundary survives nonempty base restrictions

When an old boundary meets every base fiber and lies outside the retained open, the literal
full retained boundary also meets every base fiber. Its actual preimage over a marked base
open is therefore nonempty. No nonempty-boundary certificate is assumed at the restricted stage.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- The full original closed complement dominates every base point already met by infinity. -/
theorem surjective_retainedBoundary
    {C S D : Scheme.{u}} (q : C ⟶ S) (b : D ⟶ C) [Surjective (b ≫ q)]
    (V : C.Opens) (h : Set.range b ⊆ (V : Set C)ᶜ) :
    Surjective (retainedBoundaryInclusion V ≫ q) := by
  constructor
  intro s
  obtain ⟨d, hd⟩ := (b ≫ q).surjective s
  have hb : b d ∈ Set.range (retainedBoundaryInclusion V) := by
    rw [range_retainedBoundaryInclusion]
    exact h (Set.mem_range_self d)
  obtain ⟨x, hx⟩ := hb
  exact ⟨x, by change q ((retainedBoundaryInclusion V) x) = s; rw [hx]; exact hd⟩

/-- The actual boundary preimage over any base neighborhood of a marked point is nonempty. -/
theorem nonempty_retainedBoundary_preimage
    {C S : Scheme.{u}} (q : C ⟶ S) (V : C.Opens)
    [Surjective (retainedBoundaryInclusion V ≫ q)]
    (T : S.Opens) (s : S) (hs : s ∈ T) :
    Nonempty (((retainedBoundaryInclusion V ≫ q) ⁻¹ᵁ T).toScheme) := by
  obtain ⟨c, hc⟩ := (retainedBoundaryInclusion V ≫ q).surjective s
  exact ⟨⟨c, by change (retainedBoundaryInclusion V ≫ q) c ∈ T; rwa [hc]⟩⟩

end AlgebraicGeometry.Scheme.RelativeCurve

namespace AlgebraicGeometry.Scheme

/-- An actual point in a base preimage supplies the nonemptiness needed for integrality.
This applies to the retained curve and to later section-unit opens without assuming either
open is integral in advance. -/
theorem isIntegral_preimage_of_mem
    {C S : Scheme.{u}} [IsIntegral C] (q : C ⟶ S) (T : S.Opens)
    (x : C) (hx : q x ∈ T) : IsIntegral ((q ⁻¹ᵁ T).toScheme) := by
  have : Nonempty ((q ⁻¹ᵁ T).toScheme) := ⟨⟨x, hx⟩⟩
  exact isIntegral_of_isOpenImmersion (q ⁻¹ᵁ T).ι

end AlgebraicGeometry.Scheme
