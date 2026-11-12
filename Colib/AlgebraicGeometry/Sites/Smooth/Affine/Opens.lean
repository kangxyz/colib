/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affine opens and overlaps on the actual smooth site

The open subscheme keeps the original structure map and inclusion.
Two affine sources over an affine target have an affine overlap.

Adapted from Motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
Aglib/AlgebraicGeometry/Sites/Smooth/Affine / Opens.lean.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {k : Type u} [Field k]

/-- The original affine open, with its unchanged structure map. -/
def affineOpenSite (V : SmoothSite (Spec (.of k))) (W : V.left.Opens)
    [IsAffine W.toScheme] : SmoothSite (Spec (.of k)) :=
  mk (W.ι ≫ V.hom)

/-- Literal inclusion of the original affine open. -/
def affineOpenInclusion (V : SmoothSite (Spec (.of k))) (W : V.left.Opens)
    [IsAffine W.toScheme] : affineOpenSite V W ⟶ V := homMk W.ι rfl

instance affineOpenInclusion_open (V : SmoothSite (Spec (.of k))) (W : V.left.Opens)
    [IsAffine W.toScheme] : IsOpenImmersion (affineOpenInclusion V W).left :=
  inferInstanceAs (IsOpenImmersion W.ι)

/-- The overlap of the two affine source objects is affine. -/
theorem affineOpenOverlap_affine
    {X A V : SmoothSite (Spec (.of k))} [IsAffine X.left] [IsAffine A.left]
    (i : A ⟶ X) [Etale i.left] (v : V ⟶ X)
    (W : V.left.Opens) [IsAffine W.toScheme] :
    IsAffine (etalePullback i (affineOpenInclusion V W ≫ v)).left := by
  let : IsAffine (affineOpenSite V W).left := ‹IsAffine W.toScheme›
  change IsAffine (pullback i.left ((affineOpenInclusion V W ≫ v).left))
  infer_instance

end AlgebraicGeometry.Scheme.SmoothSite
