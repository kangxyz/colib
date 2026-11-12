/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.ForgetBaseProduct
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapComponent

/-!
# Native integral supports after forgetting a separated base

The existing Stacks comparison for a closed immersion identifies each original
native integral component with the native component at its image point. Both
projections are retained. This is the support comparison required before
transporting the actual incidence scheme and its Tor coefficients.

Adapted from `Motivic/AlgebraicGeometry/Correspondences/BaseChange/Forget/Support.lean`
at `a6805c4a87cdfd7717dd7a94039246a167f15380` on native integral components.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

namespace Stacks.Chow

variable {S T X Y : Scheme.{u}} (r : T ⟶ S) (f : X ⟶ T) (g : Y ⟶ T)
  [IsSeparated r] (z : pullback (C := Scheme) f g)

/-- The actual integral component is unchanged by the closed product immersion. -/
def forgetBaseSupportIso :
    (integralComponentAt z).subscheme ≅
      (integralComponentAt (forgetBaseProductMap r f g z)).subscheme :=
  (exists_iso_integralComponentAt_comp (forgetBaseProductMap r f g) z).choose

/-- The component comparison preserves the actual closed inclusions. -/
@[reassoc (attr := simp)]
theorem forgetBaseSupportIso_hom_inclusion :
    (forgetBaseSupportIso r f g z).hom ≫
        (integralComponentAt (forgetBaseProductMap r f g z)).subschemeι =
      (integralComponentAt z).subschemeι ≫ forgetBaseProductMap r f g :=
  (exists_iso_integralComponentAt_comp (forgetBaseProductMap r f g) z).choose_spec

/-- The original source projection is unchanged. -/
@[reassoc]
theorem forgetBaseSupportIso_hom_fst :
    (forgetBaseSupportIso r f g z).hom ≫
        (integralComponentAt (forgetBaseProductMap r f g z)).subschemeι ≫
          pullback.fst (f ≫ r) (g ≫ r) =
      (integralComponentAt z).subschemeι ≫ pullback.fst f g := by
  rw [forgetBaseSupportIso_hom_inclusion_assoc, forgetBaseProductMap_fst]

/-- The original target projection is unchanged. -/
@[reassoc]
theorem forgetBaseSupportIso_hom_snd :
    (forgetBaseSupportIso r f g z).hom ≫
        (integralComponentAt (forgetBaseProductMap r f g z)).subschemeι ≫
          pullback.snd (f ≫ r) (g ≫ r) =
      (integralComponentAt z).subschemeι ≫ pullback.snd f g := by
  rw [forgetBaseSupportIso_hom_inclusion_assoc, forgetBaseProductMap_snd]

end Stacks.Chow
