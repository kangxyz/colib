/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStageRetainedNativeChart
public import Colib.AlgebraicGeometry.ResidueField.FieldPoint
/-! # Inputs for selecting actual finite-stage quadratic data

The same finite original generators generate the tensor algebra. The canonical
coordinate equivalence recovers full-tuple finiteness, and the actual rational
tensor mark has maximal image. No geometric tuple or whole-fiber certificate is
assumed in these preparation lemmas.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.Scheme
universe u
namespace QuadraticIncidence.InfinityChart

theorem tensor_generators_adjoin (F L B : Type u) [Field F] [Field L] [Algebra F L]
    [CommRing B] [Algebra F B] {σ : Type u} (g : σ → B)
    (hg : Algebra.adjoin F (Set.range g) = ⊤) :
    Algebra.adjoin L (Set.range (fun j => (1 : L) ⊗ₜ[F] g j)) = ⊤ := by
  have hr : ((fun b => (1 : L) ⊗ₜ[F] b) '' Set.range g) =
      Set.range (fun j => (1 : L) ⊗ₜ[F] g j) := by
    ext x
    simp
  rw [← hr]
  exact Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
    (R := F) (A := L) (Set.range g) hg

theorem exists_finite_tensor_generators (F L B : Type u) [Field F] [Field L] [Algebra F L]
    [CommRing B] [Algebra F B] [Algebra.FiniteType F B] :
    ∃ (s : Finset B), Algebra.adjoin F (s : Set B) = ⊤ ∧
      Algebra.adjoin L (Set.range (fun j : s => (1 : L) ⊗ₜ[F] (j : B))) = ⊤ := by
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F B).out
  refine ⟨s, hs, ?_⟩
  apply tensor_generators_adjoin F L B
  have hr : Set.range (fun j : s => (j : B)) = (s : Set B) := by
    ext x
    simp
  rwa [hr]

theorem fullCoordinateHom_finite_of_relative
    (L R : Type u) [Field L] [CommRing R] [Algebra L R]
    {σ : Type u} [Fintype σ] (g : σ → R) (d : ℕ)
    (a : Exponent σ → L) (c : Fin d × Exponent σ → L)
    (h : (quadraticRelativeCoordinateHom L R g d a c).Finite) :
    (quadraticCoordinateHom L R g (d + 1) (prependParameters L d a c)).Finite := by
  have hcomp := h.comp (RingHom.Finite.of_surjective
    (finSuccEquiv L d).toRingHom (finSuccEquiv L d).surjective)
  convert hcomp using 1
  apply RingHom.ext
  intro p
  exact congrArg (aeval (fun i => aeval g
    (parameterTuple L σ (d + 1) (prependParameters L d a c) i).val))
    ((finSuccEquiv L d).symm_apply_apply p).symm

theorem rationalTensorPoint_isMaximal (F L B : Type u) [Field F] [Field L] [Algebra F L]
    [CommRing B] [Algebra F B] (x : Spec (.of L) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap F B)) =
      Spec.map (CommRingCat.ofHom (algebraMap F L))) :
    (rationalTensorPoint F L B x hx default).asIdeal.IsMaximal := by
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
  have h := isClosed_image_of_finite_fieldPoint
    (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[F] B))))
    (rationalTensorPoint F L B x hx) (by
      simp)
  have hp : (default : Spec (.of L)) = IsLocalRing.closedPoint L := Subsingleton.elim _ _
  rw [hp]
  exact h

end QuadraticIncidence.InfinityChart
