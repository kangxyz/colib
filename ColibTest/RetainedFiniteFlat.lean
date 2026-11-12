/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Divisors.RetainedFiniteFlat

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

example {C U V : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]
    (I : C.IdealSheafData) (hI : Set.range I.subschemeι ⊆ Set.range j)
    (q : C ⟶ V) [Stacks.Morphisms.IsFiniteLocallyFree (I.subschemeι ≫ q)] :
    Stacks.Morphisms.IsFiniteLocallyFree ((I.comap j).subschemeι ≫ j ≫ q) :=
  Scheme.IdealSheafData.isFiniteLocallyFree_comap_of_range_subset j I hI q

example {C U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j]
    (I : C.IdealSheafData) (hI : Set.range I.subschemeι ⊆ Set.range j) :
    (Scheme.IdealSheafData.retainedSubschemeIso j I hI).hom ≫ I.subschemeι =
      (I.comap j).subschemeι ≫ j :=
  Scheme.IdealSheafData.retainedSubschemeIso_hom_subschemeι j I hI

#print axioms AlgebraicGeometry.Scheme.IdealSheafData.isFiniteLocallyFree_comap_of_range_subset
#print axioms Stacks.Chow.retainedFiniteFlatDivisorCorrespondence
#print axioms Stacks.Chow.retainedFiniteFlatDivisorCorrespondence_val
