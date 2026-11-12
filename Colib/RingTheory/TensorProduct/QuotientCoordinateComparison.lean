/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The actual tensor quotient map and the native quotient comparison

The native tensor-quotient equivalence identifies the actual map induced by a quotient
with the quotient by the extended ideal. This records the map, rather than only an
isomorphism between the two rings.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct

variable (K E B : Type*) [CommRing K] [CommRing E] [CommRing B]
  [Algebra K E] [Algebra K B] (I : Ideal B)

/-- The native tensor-quotient comparison preserves the original quotient morphism. -/
theorem tensorQuotientEquiv_comp_map_quotient :
    (tensorQuotientEquiv (R := K) E B E I).toRingHom.comp
      (map (AlgHom.id E E) (Ideal.Quotient.mkₐ K I)).toRingHom =
    Ideal.Quotient.mk (I.map (includeRight (R := K) (A := E))) := by
  ext x <;> rfl

/-- The actual scalar extension of a quotient map is surjective. -/
theorem map_quotient_surjective :
    Function.Surjective (map (AlgHom.id E E) (Ideal.Quotient.mkₐ K I)) :=
  map_surjective (AlgHom.id E E) (Ideal.Quotient.mkₐ K I)
    Function.surjective_id Ideal.Quotient.mk_surjective

end Algebra.TensorProduct
