/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.EnoughPoints
public import Colib.CategoryTheory.Sites.Simplicial.StalkwiseFibrantReplacement

/-!
# Nisnevich injective fibrant replacement on the smooth site

Use the original smooth schemes and their actual Nisnevich points. The
coefficient universe is the one used by the motivic homotopy category.
-/

@[expose] public section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

/-- Every pointed simplicial presheaf on the smooth Nisnevich site of an
affine scheme has an actual stalkwise trivial fibrant replacement. -/
theorem exists_nisnevichInjectiveFibrantReplacement (R : CommRingCat.{u})
    (X : PointedSimplicialPresheaf.{u + 1} (SmoothSite (Spec R))) :
    ∃ (Y : PointedSimplicialPresheaf.{u + 1} (SmoothSite (Spec R))) (i : X ⟶ Y),
      stalkwiseTrivialMonomorphisms (SmoothSite (Spec R))
        (SmoothSite.nisnevichTopology (Spec R)) i ∧
      IsStalkwiseInjectiveFibrant (SmoothSite (Spec R))
        (SmoothSite.nisnevichTopology (Spec R)) Y :=
  exists_stalkwiseInjectiveFibrantReplacement (SmoothSite (Spec R))
    (SmoothSite.nisnevichTopology (Spec R)) X

end AlgebraicGeometry.MotivicHomotopy
