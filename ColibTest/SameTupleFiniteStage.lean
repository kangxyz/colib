/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.FiniteStageDescent

open scoped TensorProduct
open IntermediateField QuadraticIncidence QuadraticIncidence.InfinityChart

universe u

/-- The same tuple and distinct opens descend without an infinitude assumption on K. -/
example
    (K L B : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing B] [Algebra K B] {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ)
    (s : Finset L) (a : Exponent σ → L) (c : Fin d × Exponent σ → L)
    (rₑ r : L ⊗[K] B)
    (hf : (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j)
      (d + 1) (prependParameters L d a c)).Finite)
    (he : ((algebraMap (L ⊗[K] B) (Localization.Away rₑ)).comp
      (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j)
        (d + 1) (prependParameters L d a c))).Etale)
    (hs : ((algebraMap (L ⊗[K] B) (Localization.Away r)).comp
      (quadraticCoordinateHom L (L ⊗[K] B) (fun j => (1 : L) ⊗ₜ[K] g j) d c)).Smooth) :
    ∃ t : Finset L, s ⊆ t ∧ Module.Finite K (adjoin K (t : Set L)) ∧
      Algebra.IsSeparable K (adjoin K (t : Set L)) ∧
      ∃ (a' : Exponent σ → adjoin K (t : Set L))
        (c' : Fin d × Exponent σ → adjoin K (t : Set L))
        (rₑ' r' : (adjoin K (t : Set L)) ⊗[K] B),
        (∀ e, (a' e : L) = a e) ∧ (∀ q, (c' q : L) = c q) ∧
        finsetTensorInclusion K L B t rₑ' = rₑ ∧ finsetTensorInclusion K L B t r' = r ∧
        (quadraticCoordinateHom (adjoin K (t : Set L)) ((adjoin K (t : Set L)) ⊗[K] B)
          (fun j => 1 ⊗ₜ[K] g j) (d + 1)
          (prependParameters (adjoin K (t : Set L)) d a' c')).Finite ∧
        ((algebraMap ((adjoin K (t : Set L)) ⊗[K] B) (Localization.Away rₑ')).comp
          (quadraticCoordinateHom (adjoin K (t : Set L)) ((adjoin K (t : Set L)) ⊗[K] B)
            (fun j => 1 ⊗ₜ[K] g j) (d + 1)
            (prependParameters (adjoin K (t : Set L)) d a' c'))).Etale ∧
        ((algebraMap ((adjoin K (t : Set L)) ⊗[K] B) (Localization.Away r')).comp
          (quadraticCoordinateHom (adjoin K (t : Set L)) ((adjoin K (t : Set L)) ⊗[K] B)
            (fun j => 1 ⊗ₜ[K] g j) d c')).Smooth :=
  exists_finsetSubfield_sameTuple_coordinates K L B g d s a c rₑ r hf he hs
