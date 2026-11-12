/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Frobenius

/-!
# The native Frobenius twist functor on the original smooth site

The native pullback functor on schemes over the base preserves smooth, separated,
finite-type objects. Its restriction uses exactly the previously constructed twist objects,
and the original relative Frobenius gives its natural transformation from the identity.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Frobenius

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] (hS : IsInCharacteristic S p)

/-- Restrict the native base Frobenius pullback functor to original smooth objects. -/
def frobeniusTwistFunctor : SmoothSite S ⥤ SmoothSite S where
  obj X := frobeniusTwist p hS X
  map f := homMk
    (((_root_.AlgebraicGeometry.frobeniusTwist S p hS).map ((forget S).map f)).left)
    (((_root_.AlgebraicGeometry.frobeniusTwist S p hS).map ((forget S).map f)).w)
  map_id X := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f => f.left)
      ((_root_.AlgebraicGeometry.frobeniusTwist S p hS).map_id ((forget S).obj X))
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact congrArg (fun f => f.left)
      ((_root_.AlgebraicGeometry.frobeniusTwist S p hS).map_comp
        ((forget S).map f) ((forget S).map g))

@[simp]
theorem frobeniusTwistFunctor_obj (X : SmoothSite S) :
    (frobeniusTwistFunctor p hS).obj X = frobeniusTwist p hS X := rfl

/-- Naturality retains the original scheme maps and the native base-change functor. -/
theorem relativeFrobenius_naturality {X Y : SmoothSite S} (f : X ⟶ Y) :
    relativeFrobenius p hS X ≫ (frobeniusTwistFunctor p hS).map f =
      f ≫ relativeFrobenius p hS Y := by
  apply MorphismProperty.Over.Hom.ext
  exact congrArg (fun f => f.left)
    (_root_.AlgebraicGeometry.relativeFrobenius_naturality S p hS ((forget S).map f))

/-- The original relative Frobenius, naturally on the whole smooth site. -/
def relativeFrobeniusNatTrans : 𝟭 (SmoothSite S) ⟶ frobeniusTwistFunctor p hS where
  app X := relativeFrobenius p hS X
  naturality _ _ f := (relativeFrobenius_naturality p hS f).symm

end AlgebraicGeometry.Scheme.SmoothSite
