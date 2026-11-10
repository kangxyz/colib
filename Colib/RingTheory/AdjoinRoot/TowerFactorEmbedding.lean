/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TowerFactor

/-!
# The actual embedding between relative tower-factor presentations

For original embeddings `A → E → H`, the native selected factors over `A`
have their existing quotient algebras identified with `E` and `H`. Conjugating
the original embedding `E → H` by those identifications gives an actual
`A`-algebra homomorphism. Its injectivity, coefficient square, original field-map
square, literal `AdjoinRoot.map` square and root formula are proved below.

All original fields and relative quotient algebras keep their existing scalar
structures. In particular, no `A`-algebra structure is introduced on `E` or `H`.
This is independent lower algebra for the general simple-norm tower argument;
no norm law or new norm definition is used or asserted.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

variable {k : Type*} [Field k] (a p h : k[X])
  [Fact (Irreducible a)] [Fact (Irreducible p)] [Fact (Irreducible h)]
  (g : AdjoinRoot a →ₐ[k] AdjoinRoot p)
  (f : AdjoinRoot p →ₐ[k] AdjoinRoot h)

local notation "A" => AdjoinRoot a
local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h
local notation "qP" => towerFactor a p g
local notation "qH" => towerFactor a h (f.comp g)
local notation "pA" => poly qP.1.2
local notation "hA" => poly qH.1.2
local notation "PA" => AdjoinRoot pA
local notation "HA" => AdjoinRoot hA

/-- Conjugate the original field embedding by the two actual quotient equivalences. -/
def towerFactorEmbeddingRingHom : PA →+* HA :=
  (towerFactorRingEquiv a h (f.comp g)).symm.toRingHom.comp
    (f.toRingHom.comp (towerFactorRingEquiv a p g).toRingHom)

/-- The given lower embedding makes the coefficient square commute. -/
theorem towerFactorEmbeddingRingHom_algebraMap (x : A) :
    towerFactorEmbeddingRingHom a p h g f (algebraMap A PA x) =
      algebraMap A HA x := by
  apply (towerFactorRingEquiv a h (f.comp g)).injective
  change towerFactorRingEquiv a h (f.comp g)
      ((towerFactorRingEquiv a h (f.comp g)).symm
        (f (towerFactorRingEquiv a p g (algebraMap A PA x)))) =
    towerFactorRingEquiv a h (f.comp g) (algebraMap A HA x)
  rw [RingEquiv.apply_symm_apply, towerFactorRingEquiv_algebraMap,
    towerFactorRingEquiv_algebraMap]
  rfl

/-- The actual relative embedding, using the quotients' existing lower scalar structures. -/
def towerFactorEmbeddingAlgHom : PA →ₐ[A] HA :=
  { towerFactorEmbeddingRingHom a p h g f with
    commutes' := towerFactorEmbeddingRingHom_algebraMap a p h g f }

/-- The algebra homomorphism retains the original conjugated ring homomorphism. -/
theorem towerFactorEmbeddingAlgHom_toRingHom :
    (towerFactorEmbeddingAlgHom a p h g f).toRingHom =
      towerFactorEmbeddingRingHom a p h g f := rfl

/-- Cancellation gives the pointwise square with the original top-field maps. -/
theorem towerFactorEmbeddingAlgHom_apply (x : PA) :
    towerFactorRingEquiv a h (f.comp g) (towerFactorEmbeddingAlgHom a p h g f x) =
      f (towerFactorRingEquiv a p g x) := by
  change towerFactorRingEquiv a h (f.comp g)
      ((towerFactorRingEquiv a h (f.comp g)).symm
        (f (towerFactorRingEquiv a p g x))) = f (towerFactorRingEquiv a p g x)
  exact RingEquiv.apply_symm_apply _ _

/-- The actual relative homomorphism is injective because the original embedding is. -/
theorem towerFactorEmbeddingAlgHom_injective :
    Function.Injective (towerFactorEmbeddingAlgHom a p h g f) := by
  intro x y hxy
  apply (towerFactorRingEquiv a p g).injective
  apply f.injective
  change f (towerFactorRingEquiv a p g x) = f (towerFactorRingEquiv a p g y)
  rw [← towerFactorEmbeddingAlgHom_apply, ← towerFactorEmbeddingAlgHom_apply, hxy]

/-- The original top-field square is equality of actual ring homomorphisms. -/
theorem towerFactorEmbeddingAlgHom_comp_towerFactorRingEquiv :
    (towerFactorRingEquiv a h (f.comp g)).toRingHom.comp
        (towerFactorEmbeddingAlgHom a p h g f).toRingHom =
      f.toRingHom.comp (towerFactorRingEquiv a p g).toRingHom := by
  apply RingHom.ext
  intro x
  exact towerFactorEmbeddingAlgHom_apply a p h g f x

/-- The relative embedding preserves the original coefficient-factor maps on every element. -/
theorem towerFactorEmbeddingAlgHom_map (b : E) :
    towerFactorEmbeddingAlgHom a p h g f
      (AdjoinRoot.map (algebraMap k A) p pA qP.2 b) =
    AdjoinRoot.map (algebraMap k A) h hA qH.2 (f b) := by
  apply (towerFactorRingEquiv a h (f.comp g)).injective
  rw [towerFactorEmbeddingAlgHom_apply, towerFactorRingEquiv_map,
    towerFactorRingEquiv_map]

/-- The coefficient-factor map square uses the literal native homomorphisms. -/
theorem towerFactorEmbeddingAlgHom_comp_adjoinRootMap :
    (towerFactorEmbeddingAlgHom a p h g f).toRingHom.comp
        (AdjoinRoot.map (algebraMap k A) p pA qP.2) =
      (AdjoinRoot.map (algebraMap k A) h hA qH.2).comp f.toRingHom := by
  apply RingHom.ext
  intro b
  exact towerFactorEmbeddingAlgHom_map a p h g f b

/-- The relative root is the image of the original intermediate-field root. -/
theorem towerFactorEmbeddingAlgHom_root :
    towerFactorEmbeddingAlgHom a p h g f (root pA) =
      AdjoinRoot.map (algebraMap k A) h hA qH.2 (f (root p)) := by
  simpa only [AdjoinRoot.map_root] using
    towerFactorEmbeddingAlgHom_map a p h g f (root p)

/-- Reading the relative-root image in the original top field recovers the given embedding. -/
theorem towerFactorEmbeddingAlgHom_root_apply :
    towerFactorRingEquiv a h (f.comp g)
      (towerFactorEmbeddingAlgHom a p h g f (root pA)) = f (root p) := by
  rw [towerFactorEmbeddingAlgHom_apply, towerFactorRingEquiv_root]

end AdjoinRoot

end
