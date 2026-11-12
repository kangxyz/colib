/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Pushouts for the actual scalar-extension tensor map

Native tensor pushouts and their horizontal cancellation give the actual map square.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits

universe u

namespace CommRingCat
/-- The actual tensor map of an algebra homomorphism is its scalar-extension pushout. -/
theorem isPushout_scalarExtension_map
    (E L A B : Type u) [CommRing E] [CommRing L] [CommRing A] [CommRing B]
    [Algebra E L] [Algebra E A] [Algebra E B] (f : A →ₐ[E] B) :
    IsPushout (ofHom f.toRingHom)
      (ofHom (Algebra.TensorProduct.includeRight : A →ₐ[E] L ⊗[E] A).toRingHom)
      (ofHom (Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B).toRingHom)
      (ofHom (Algebra.TensorProduct.map (AlgHom.id E L) f).toRingHom) := by
  apply IsPushout.of_left (h₁₁ := ofHom (algebraMap E A))
    (h₂₁ := ofHom (algebraMap L (L ⊗[E] A))) (v₁₁ := ofHom (algebraMap E L))
  · convert (isPushout_tensorProduct E L B).flip using 1
    · ext e
      exact f.commutes e
    · ext l
      simp
  · ext a
    simp
  · exact (isPushout_tensorProduct E L A).flip
end CommRingCat
