/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# Scheme-open pairs with their actual commuting squares

A pair is an open immersion, and a morphism is any commuting square of schemes.
No flatness, cartesianness or compactness is part of this category.

Adapted from Quillen
`Quillen/Aglib/AlgebraicGeometry/Morphisms/OpenImmersion/Pair/Basic.lean:26-37`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native Mathlib objects.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- Open immersions with arbitrary commuting squares in the native morphism-property category. -/
abbrev OpenPairs := MorphismProperty.Arrow (@IsOpenImmersion : MorphismProperty Scheme.{u}) ⊤ ⊤

instance openPairs_openImmersion (X : OpenPairs.{u}) : IsOpenImmersion X.hom :=
  X.prop

end AlgebraicGeometry.Scheme
