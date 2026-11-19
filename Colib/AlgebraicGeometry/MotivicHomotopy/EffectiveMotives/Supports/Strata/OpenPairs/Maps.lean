/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cohomology.GenericOpen
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Original maps of literal smooth open pairs -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))

variable (X : Sm(k))

/-- The literal inclusion between two opens, on the given smooth scheme. -/
abbrev relativeOpenInclusion {U V : X.left.Opens} (h : U ≤ V) :=
  (SmoothSite.opensFunctor X).map (homOfLE h)

/-- The arrow of an inclusion of actual opens. -/
abbrev relativeOpenPair {U V : X.left.Opens} (h : U ≤ V) : Arrow Sm(k) :=
  Arrow.mk (relativeOpenInclusion k X h)

/-- A map of two relative pairs given by inclusions of literal opens. -/
def relativeOpenPairMap {U V U' V' : X.left.Opens} (h : U ≤ V) (h' : U' ≤ V')
    (a : U ≤ U') (b : V ≤ V') : relativeOpenPair k X h ⟶ relativeOpenPair k X h' :=
  Arrow.homMk' (relativeOpenInclusion k X a) (relativeOpenInclusion k X b) (by
    change ((SmoothSite.opensFunctor X).map (homOfLE a)) ≫
      (SmoothSite.opensFunctor X).map (homOfLE h') =
      (SmoothSite.opensFunctor X).map (homOfLE h) ≫
      (SmoothSite.opensFunctor X).map (homOfLE b)
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1)

/-- The actual maps of relative pairs compose by inclusion of opens. -/
theorem relativeOpenPairMap_comp {U V U' V' U'' V'' : X.left.Opens}
    (h : U ≤ V) (h' : U' ≤ V') (h'' : U'' ≤ V'')
    (a : U ≤ U') (b : V ≤ V') (a' : U' ≤ U'') (b' : V' ≤ V'') :
    relativeOpenPairMap k X h h' a b ≫ relativeOpenPairMap k X h' h'' a' b' =
      relativeOpenPairMap k X h h'' (a.trans a') (b.trans b') := by
  apply Arrow.hom_ext
  · exact ((SmoothSite.opensFunctor X).map_comp (homOfLE a) (homOfLE a')).symm
  · exact ((SmoothSite.opensFunctor X).map_comp (homOfLE b) (homOfLE b')).symm

/-- Excision to an open covering the support in a literal pair. -/
abbrev relativeOpenPairRestriction {B U V : X.left.Opens} (h : B ≤ U) (hV : V ≤ U) :
    relativeOpenPair k X (inf_le_left : V ⊓ B ≤ V) ⟶ relativeOpenPair k X h :=
  relativeOpenPairMap k X inf_le_left h inf_le_right hV

end AlgebraicGeometry.MotivicHomotopy
