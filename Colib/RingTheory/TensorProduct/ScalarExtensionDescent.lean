/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.LinearAlgebra.Basis.VectorSpace
/-!
# Descent through the actual scalar-extension tensor map

For a map of algebras over a field, its tensor product with the identity of a field extension
is the original faithfully-flat base-change map. The literal tensor square is a native
algebra pushout. Native descent therefore detects etaleness, smoothness and finiteness on
that map, without assuming a replacement comparison square or changing the original map.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace AlgHom

/-- Any native ring-hom property that descends under faithfully flat base change can be
checked on the original tensor product with the identity of a field extension. -/
theorem of_tensorProductMap_of_codescendsAlong
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.CodescendsAlong P RingHom.FaithfullyFlat)
    (E L A B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing A] [CommRing B] [Algebra E A] [Algebra E B] (f : A →ₐ[E] B)
    (hf : P (Algebra.TensorProduct.map f (AlgHom.id E L)).toRingHom) :
    P f.toRingHom := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower E A B := IsScalarTower.of_algebraMap_eq fun a => (f.commutes a).symm
  let : Algebra (A ⊗[E] L) (B ⊗[E] L) :=
    (Algebra.TensorProduct.map f (AlgHom.id E L)).toRingHom.toAlgebra
  have : IsScalarTower A B (B ⊗[E] L) := inferInstance
  have : IsScalarTower A (A ⊗[E] L) (B ⊗[E] L) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      simp only [Algebra.TensorProduct.algebraMap_apply]
      rfl
  have : Algebra.IsPushout A B (A ⊗[E] L) (B ⊗[E] L) :=
    Algebra.IsPushout.tensorProduct_tensorProduct E L A B (by
      ext x
      change Algebra.TensorProduct.map f (AlgHom.id E L) ((1 : A) ⊗ₜ[E] x) = 1 ⊗ₜ[E] x
      simp)
  exact hP
    ((RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance) hf

/-- Smoothness descends from the actual tensor-product map. -/
theorem smooth_of_tensorProductMap (E L A B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing A] [CommRing B] [Algebra E A] [Algebra E B] (f : A →ₐ[E] B)
    (hf : (Algebra.TensorProduct.map f (AlgHom.id E L)).toRingHom.Smooth) :
    f.toRingHom.Smooth :=
  of_tensorProductMap_of_codescendsAlong _ RingHom.Smooth.codescendsAlong_faithfullyFlat
    E L A B f hf

/-- Finiteness descends from the actual tensor-product map. -/
theorem finite_of_tensorProductMap (E L A B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing A] [CommRing B] [Algebra E A] [Algebra E B] (f : A →ₐ[E] B)
    (hf : (Algebra.TensorProduct.map f (AlgHom.id E L)).toRingHom.Finite) :
    f.toRingHom.Finite :=
  of_tensorProductMap_of_codescendsAlong _ RingHom.Finite.codescendsAlong_faithfullyFlat
    E L A B f hf

/-- Etaleness descends from the actual tensor-product map. -/
theorem etale_of_tensorProductMap (E L A B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing A] [CommRing B] [Algebra E A] [Algebra E B] (f : A →ₐ[E] B)
    (hf : (Algebra.TensorProduct.map f (AlgHom.id E L)).toRingHom.Etale) :
    f.toRingHom.Etale :=
  of_tensorProductMap_of_codescendsAlong _ RingHom.Etale.codescendsAlong_faithfullyFlat
    E L A B f hf

/-- The same descent statement for the original left-oriented scalar extension, using only
the native tensor commutation maps. -/
theorem of_leftTensorProductMap_of_codescendsAlong
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.CodescendsAlong P RingHom.FaithfullyFlat) (hi : RingHom.RespectsIso P)
    (E L A B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing A] [CommRing B] [Algebra E A] [Algebra E B] (f : A →ₐ[E] B)
    (hf : P (Algebra.TensorProduct.map (AlgHom.id E L) f).toRingHom) :
    P f.toRingHom := by
  apply of_tensorProductMap_of_codescendsAlong P hP E L A B f
  have h := hi.1 _ (Algebra.TensorProduct.comm E L B).toRingEquiv
    (hi.2 _ (Algebra.TensorProduct.comm E A L).toRingEquiv hf)
  have he : (Algebra.TensorProduct.comm E L B).toRingHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id E L) f).toRingHom.comp
        (Algebra.TensorProduct.comm E A L).toRingHom) =
      (Algebra.TensorProduct.map f (AlgHom.id E L)).toRingHom := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a l => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rwa [he] at h

end AlgHom
