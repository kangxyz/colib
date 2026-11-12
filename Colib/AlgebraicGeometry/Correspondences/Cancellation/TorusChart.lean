/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.NativeChart
public import Colib.AlgebraicGeometry.Sites.Smooth.GroupSchemes

/-!
# The Laurent chart of the native torus over a field

The actual torus chart retains both the forward coordinate and the structure
map. Its base change identifies the original torus product over any scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {k : Type u} [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => SmoothSite.multiplicativeGroupObject Sₖ
set_option quotPrecheck false in
local notation "gₖ" => (multiplicativeGroupBaseChange Sₖ ↘ Sₖ)

/-- The canonical Laurent chart for the existing torus over a field. -/
def torusFieldChart : Spec (.of (LaurentPolynomial k)) ≅ (Gₖ).left :=
  nativeChartIso (𝟙 Sₖ) ≪≫ asIso (pullback.snd (𝟙 Sₖ) gₖ)

/-- The chart lies over the original field. -/
theorem torusFieldChart_hom_base :
    (torusFieldChart (k := k)).hom ≫ gₖ = chartProjection := by
  change chartMap (𝟙 Sₖ) ≫ pullback.snd _ _ ≫ gₖ = _
  rw [← pullback.condition, Category.comp_id, chartMap_fst]

/-- Pulling the original torus coordinate back to the chart gives the forward Laurent generator. -/
theorem torusFieldChart_appTop :
    (torusFieldChart (k := k)).hom.appTop (multiplicativeGroupBaseChangeCoordinate Sₖ).val =
      (ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1) :=
  chartMap_appTop_coordinate (𝟙 Sₖ)

/-- The torus product over an original support is the pullback of the chart over the field. -/
theorem torusFieldChart_isPullback {P : Scheme.{u}} (q : P ⟶ Sₖ) :
    IsPullback (pullback.snd q gₖ ≫ (torusFieldChart (k := k)).inv)
      (pullback.fst q gₖ) (chartProjection (R := k)) q := by
  let H : IsPullback (pullback.snd q gₖ) (pullback.fst q gₖ) gₖ q :=
    (IsPullback.of_hasPullback q gₖ).flip
  refine H.of_iso' (Iso.refl _) (torusFieldChart (k := k)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.comp_id] using torusFieldChart_hom_base (k := k)
  · simp

end AlgebraicGeometry.NativeTorusPolynomial
