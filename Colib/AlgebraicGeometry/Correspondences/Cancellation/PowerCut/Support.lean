/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Basic
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut

/-!
# Prime supports with two torus coordinates

The two projections of a prime support are those of its integral closed
subscheme in the original product. The torus coordinates are retained.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject Sₖ

variable (X Y : SmoothSite (Spec (CommRingCat.of k)))

/-- The native product in which the original correspondence is a cycle. -/
abbrev torusPowerCutAmbient : Scheme.{u} :=
  (SmoothSite.product (SmoothSite.product X Gₘ) (SmoothSite.product Y Gₘ)).left

/-- The projection of the integral support onto the source with its torus factor. -/
abbrev torusPowerCutSource (z : torusPowerCutAmbient k X Y) :
    (integralComponentAt (X := torusPowerCutAmbient k X Y) z).subscheme ⟶
      (SmoothSite.product X Gₘ).left :=
  (integralComponentAt (X := torusPowerCutAmbient k X Y) z).subschemeι ≫
    (SmoothSite.productFst (SmoothSite.product X Gₘ) (SmoothSite.product Y Gₘ)).left

/-- The projection of the integral support onto the target with its torus factor. -/
abbrev torusPowerCutTarget (z : torusPowerCutAmbient k X Y) :
    (integralComponentAt (X := torusPowerCutAmbient k X Y) z).subscheme ⟶
      (SmoothSite.product Y Gₘ).left :=
  (integralComponentAt (X := torusPowerCutAmbient k X Y) z).subschemeι ≫
    (SmoothSite.productSnd (SmoothSite.product X Gₘ) (SmoothSite.product Y Gₘ)).left

end AlgebraicGeometry.Cor
