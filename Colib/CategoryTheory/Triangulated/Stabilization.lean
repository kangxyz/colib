/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.ExactInverse
public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Exactness
public import Colib.CategoryTheory.Triangulated.Stabilization.Triangulated
import Colib.Util.References

/-! # Triangulated stabilization and symmetric object inversion

The stage model inverts a fully faithful exact endofunctor. When it is right
tensoring by an object with identity self-braiding, the same stages carry
the symmetric tensor and its shift comparisons.
-/

attribute [colib_tag "COL-1235",
  colib_ref "Voevodsky2000TriangulatedMotives" "Section 2.1, after Proposition 2.1.3"
    "generalization" "Finite-stage inversion of a fully faithful exact endofunctor"]
  CategoryTheory.Stabilization

attribute [colib_tag "COL-1235"]
  CategoryTheory.Stabilization.homEquiv
  CategoryTheory.Stabilization.distinguished_iff
  CategoryTheory.Stabilization.atLevel_isTriangulated
  CategoryTheory.Stabilization.twistEquivalence
  CategoryTheory.Stabilization.inverseTwistEquivalence_isTriangulated

attribute [colib_tag "COL-1304",
  colib_ref "Voevodsky2000TriangulatedMotives" "Section 2.1 and Corollary 2.1.5"
    "generalization" "Exact tensor after inversion with the identity self-braiding"]
  CategoryTheory.Stabilization.stableTensorLeft_isTriangulated

attribute [colib_tag "COL-1304"]
  CategoryTheory.Stabilization.monoidalCategory
  CategoryTheory.Stabilization.symmetricCategory
  CategoryTheory.Stabilization.stableTensorRight_isTriangulated
