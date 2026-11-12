/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.RingTheory.TensorProduct.ScalarExtensionDescent

universe u

/-- All three native properties descend on the same original map and tensor square. -/
example (E L A B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing A] [CommRing B] [Algebra E A] [Algebra E B] (f : A →ₐ[E] B)
    (he : (Algebra.TensorProduct.map f (AlgHom.id E L)).toRingHom.Etale)
    (hs : (Algebra.TensorProduct.map f (AlgHom.id E L)).toRingHom.Smooth)
    (hf : (Algebra.TensorProduct.map f (AlgHom.id E L)).toRingHom.Finite) :
    f.toRingHom.Etale ∧ f.toRingHom.Smooth ∧ f.toRingHom.Finite :=
  ⟨f.etale_of_tensorProductMap E L A B he, f.smooth_of_tensorProductMap E L A B hs,
    f.finite_of_tensorProductMap E L A B hf⟩
