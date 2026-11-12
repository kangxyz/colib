/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.AffineLineFiber
public import Colib.AlgebraicGeometry.Sites.Smooth.Products

/-!
# Polynomial faces on literal relative products

A map on the original base and the identity on the retained smooth factor
form the actual Cartesian product square. Pasting this square with a
polynomial face retains the same evaluation and flat parameter.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} {X Y : SmoothSite S} (f : X ⟶ Y) (T : SmoothSite S)

/-- The actual product map is Cartesian along the original factor. -/
theorem productMap_left_isPullback :
    IsPullback (productMap f (𝟙 T)).left (productFst X T).left
      (productFst Y T).left f.left := by
  change IsPullback (productMap f (𝟙 T)).left (pullback.fst X.hom T.hom)
    (pullback.fst Y.hom T.hom) f.left
  have hf : (productMap f (𝟙 T)).left ≫ pullback.fst Y.hom T.hom =
      pullback.fst X.hom T.hom ≫ f.left :=
    congrArg (fun g => g.left) (productMap_fst f (𝟙 T))
  have hs : (productMap f (𝟙 T)).left ≫ pullback.snd Y.hom T.hom =
      pullback.snd X.hom T.hom := by
    exact congrArg (fun g => g.left) ((productMap_snd f (𝟙 T)).trans (Category.comp_id _))
  apply IsPullback.flip
  refine IsPullback.of_bot (t := IsPullback.of_hasPullback Y.hom T.hom) ?_ hf.symm
  rw [MorphismProperty.Over.w f, hs]
  exact IsPullback.of_hasPullback X.hom T.hom

variable {k : Type u} [Field k]
  {U W : SmoothSite (Spec (CommRingCat.of k))}

/-- A Cartesian polynomial face remains the same evaluation face after taking the product. -/
theorem productMap_cartesian_polynomial_face (g : U ⟶ W)
    (T : SmoothSite (Spec (CommRingCat.of k)))
    (q : W.left ⟶ Spec (.of (Polynomial k))) (a : k)
    (H : IsPullback g.left U.hom q (AffineLineFiber.point a)) :
    IsPullback (productMap g (𝟙 T)).left (product U T).hom
      ((productFst W T).left ≫ q) (AffineLineFiber.point a) :=
  (productMap_left_isPullback g T).paste_vert H

end AlgebraicGeometry.Scheme.SmoothSite
