/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Limits.FiniteSubfieldClopen
import Colib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.ScalarExtension
import Colib.RingTheory.Bertini.FiniteSubfieldParameters

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry IntermediateField QuadraticIncidence.InfinityChart

universe u

/-- The original mark is preserved by the exact affine clopen localization comparison. -/
example (K L B : Type u) [Field K] [Field L] [Algebra K L] [Algebra.IsSeparable K L]
    [CommRing B] [Algebra K B] (s : Finset L)
    (U : (Spec (.of (L ⊗[K] B))).Opens)
    (hU : IsClopen (U : Set (Spec (.of (L ⊗[K] B))))) [IsIntegral U.toScheme]
    (T : Scheme.{u}) (ξ : T ⟶ U.toScheme) :
    ∃ t : Finset L, s ⊆ t ∧ Module.Finite K (adjoin K (t : Set L)) ∧
      ∃ e : (adjoin K (t : Set L)) ⊗[K] B, IsIdempotentElem e ∧
        IsDomain (Localization.Away e) ∧
        ∃ i : U.toScheme ≅ Spec (.of (Localization.Away (finsetTensorInclusion K L B t e))),
          (ξ ≫ i.hom) ≫ Spec.map (CommRingCat.ofHom
            (algebraMap (L ⊗[K] B) (Localization.Away (finsetTensorInclusion K L B t e)))) =
              ξ ≫ U.ι := by
  obtain ⟨t, ht, hf, e, he, hd, i, hi⟩ :=
    Scheme.exists_integral_clopen_finsetSubfieldModel K L B s U hU
  exact ⟨t, ht, hf, e, he, hd, i, by rw [Category.assoc, hi]⟩

/-- The actual tensor inclusion, not an arbitrary equivalence, extends every full coordinate. -/
example (E L B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing B] [Algebra E B] {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ)
    (a : QuadraticIncidence.Exponent σ → E)
    (c : Fin d × QuadraticIncidence.Exponent σ → E) :
    (Algebra.TensorProduct.includeRight : B →ₐ[E] L ⊗[E] B).toRingHom.comp
        (quadraticRelativeCoordinateHom E B g d a c) =
      (quadraticRelativeCoordinateHom L (L ⊗[E] B) (fun j => 1 ⊗ₜ[E] g j) d
        (fun e => algebraMap E L (a e)) (fun q => algebraMap E L (c q))).comp
        (Polynomial.mapRingHom (MvPolynomial.map (algebraMap E L))) :=
  quadraticRelativeCoordinateHom_scalarExtension E L B (L ⊗[E] B)
    Algebra.TensorProduct.includeRight g d a c
