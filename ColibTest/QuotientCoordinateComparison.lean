/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.TensorProduct.QuotientCoordinateComparison

open scoped TensorProduct
open Algebra.TensorProduct

/-- The comparison records the quotient map itself, without any field hypothesis. -/
example (K E B : Type*) [CommRing K] [CommRing E] [CommRing B]
    [Algebra K E] [Algebra K B] (I : Ideal B) :
    (tensorQuotientEquiv (R := K) E B E I).toRingHom.comp
      (map (AlgHom.id E E) (Ideal.Quotient.mkₐ K I)).toRingHom =
    Ideal.Quotient.mk (I.map (includeRight (R := K) (A := E))) :=
  tensorQuotientEquiv_comp_map_quotient K E B I

/-- Nilpotents in the original quotient are not removed. -/
example (K E B : Type*) [CommRing K] [CommRing E] [CommRing B]
    [Algebra K E] [Algebra K B] (I : Ideal B) :
    Function.Surjective (map (AlgHom.id E E) (Ideal.Quotient.mkₐ K I)) :=
  map_quotient_surjective K E B I
