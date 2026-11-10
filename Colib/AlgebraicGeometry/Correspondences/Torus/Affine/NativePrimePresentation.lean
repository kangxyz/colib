/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialProducts
public import Colib.RingTheory.AdjoinRoot.NormalUnitPresentation
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Actual monic equations of native finite torus prime cycles

The input is an admissible point of the existing native correspondence ambient.
Its support is the native reduced closed subscheme of its closure. Finiteness,
dominance, scalar injectivity and Laurent generation are proved from that actual
support. Normality of the integral affine base gives its literal minimal
polynomial and an isomorphism from the whole polynomial quotient. The ambient
and both coordinate maps are retained; no presentation or desired inverse is
supplied as an assumption.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Correspondences/Torus/Affine/PolynomialPresentation.lean:40-156` and
`PolynomialCycles.lean:73-142`. The source's smooth integral affine range is
replaced by the exact normal-domain hypotheses it uses. This is source-only.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R : Type u} [CommRing R]

/-- Admissible points of the retained native torus ambient, not a new cycle group. -/
abbrev PrimePoint (f : Spec (.of R) ⟶ S) :=
  {z : ambient f // IsFiniteCorrespondencePoint f (multiplicativeGroupBaseChange S ↘ S) z}

namespace PrimePoint

variable {f : Spec (.of R) ⟶ S} (Z : PrimePoint f)

/-- The actual native integral closed support of the point. -/
abbrev support : Scheme.{u} := (integralComponentAt Z.val).subscheme

instance supportIntegral : IsIntegral Z.support := isIntegral_integralComponentAt Z.val

/-- The original closed inclusion, with its full ideal sheaf. -/
abbrev inclusion : Z.support ⟶ ambient f := (integralComponentAt Z.val).subschemeι

/-- Projection of the actual support to the affine source. -/
def projection : Z.support ⟶ Spec (.of R) := Z.inclusion ≫ pullback.fst _ _

instance projectionFinite : IsFinite Z.projection := Z.property.1

instance supportAffine : IsAffine Z.support := isAffine_of_isAffineHom Z.projection

/-- The whole coordinate ring of the actual native integral support. -/
abbrev coordinateRing : CommRingCat.{u} := Γ(Z.support, ⊤)

instance coordinateDomain : IsDomain Z.coordinateRing := inferInstance

/-- The scalar map is the pullback along the actual finite support projection. -/
def scalarMap : R →+* Z.coordinateRing :=
  Z.projection.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom

instance coordinateAlgebra : Algebra R Z.coordinateRing := Z.scalarMap.toAlgebra

instance coordinateFinite : Module.Finite R Z.coordinateRing := by
  change Z.scalarMap.Finite
  exact Z.projection.finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.surjective)

/-- The same closed support in the explicit chart of the native ambient. -/
def laurentEmbedding : Z.support ⟶ Spec (.of (LaurentPolynomial R)) :=
  Z.inclusion ≫ (nativeChartIso f).inv

instance laurentEmbeddingClosed : IsClosedImmersion Z.laurentEmbedding := by
  unfold laurentEmbedding
  infer_instance

@[reassoc] theorem laurentEmbedding_projection :
    Z.laurentEmbedding ≫ chartProjection = Z.projection := by
  change Z.inclusion ≫ chartInverse f ≫ chartProjection = _
  rw [chartInverse_projection]
  rfl

/-- Pullback of the actual Laurent coordinate ring to the whole support. -/
def laurentPullback : LaurentPolynomial R →+* Z.coordinateRing :=
  Z.laurentEmbedding.appTop.hom.comp
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom

/-- The forward coordinate together with its genuine inverse on the support. -/
def coordinateUnit : Z.coordinateRingˣ :=
  Units.map Z.laurentPullback.toMonoidHom chartUnit

theorem laurentPullback_C (r : R) :
    Z.laurentPullback (LaurentPolynomial.C r) = Z.scalarMap r := by
  have h := congrArg (fun k : Z.support ⟶ Spec (.of R) =>
    k.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) Z.laurentEmbedding_projection
  rw [Scheme.Hom.comp_appTop] at h
  have hc := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (LaurentPolynomial.C : R →+* LaurentPolynomial R))).symm r
  change chartProjection.appTop ((Scheme.ΓSpecIso (.of R)).inv r) =
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (LaurentPolynomial.C r) at hc
  simpa only [ConcreteCategory.comp_apply, hc, laurentPullback, scalarMap,
    RingHom.comp_apply] using h

/-- The actual closed immersion proves surjective Laurent evaluation. -/
theorem laurent_eval_surjective :
    Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R Z.coordinateRing)
      Z.coordinateUnit) := by
  have he : Z.laurentPullback =
      LaurentPolynomial.eval₂ (algebraMap R Z.coordinateRing) Z.coordinateUnit := by
    apply laurentRingHom_ext
    · intro r
      rw [Z.laurentPullback_C, LaurentPolynomial.eval₂_C]
      rfl
    · rw [LaurentPolynomial.eval₂_T, zpow_one]
      simp only [coordinateUnit, Units.coe_map, chartUnit_val]
      rfl
  rw [← he]
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine Z.laurentEmbedding).2.comp
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).symm.commRingCatIsoToRingEquiv.surjective

variable [IsDomain R]

/-- The component condition over an integral source is genuine surjectivity. -/
theorem projection_surjective : Function.Surjective Z.projection := by
  apply Set.range_eq_univ.mp
  exact Set.mem_singleton_iff.mp
    (irreducibleComponents_eq_singleton (X := Spec (.of R)) ▸ Z.property.2)

/-- Source dominance forces injectivity of the actual scalar map. -/
theorem scalarMap_injective : Function.Injective Z.scalarMap := by
  have : Surjective Z.projection := ⟨Z.projection_surjective⟩
  have : IsSchemeTheoreticallyDominant Z.projection :=
    IsSchemeTheoreticallyDominant.of_isDominant Z.projection
  exact (Z.projection.app_injective ⊤).comp
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.injective

instance coordinateTorsionFree : Module.IsTorsionFree R Z.coordinateRing :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr Z.scalarMap_injective

/-- The literal native minimal polynomial of the support's forward coordinate. -/
def coordinatePolynomial : R[X] := minpoly R (Z.coordinateUnit : Z.coordinateRing)

omit [IsDomain R] in
theorem coordinatePolynomial_monic : Z.coordinatePolynomial.Monic :=
  minpoly.monic (IsIntegral.of_finite R _)

omit [IsDomain R] in
theorem coordinatePolynomial_natDegree_pos : 1 ≤ Z.coordinatePolynomial.natDegree :=
  minpoly.natDegree_pos (IsIntegral.of_finite R _)

variable [IsIntegrallyClosed R]

theorem coordinatePolynomial_constant_isUnit : IsUnit (Z.coordinatePolynomial.coeff 0) :=
  AdjoinRoot.NormalUnitPresentation.minpoly_coeff_zero_isUnit R Z.coordinateUnit

/-- The actual evaluation kernel is the principal ideal of this literal monic equation. -/
theorem coordinatePolynomial_ker :
    RingHom.ker (Polynomial.aeval (Z.coordinateUnit : Z.coordinateRing)).toRingHom =
      Ideal.span {Z.coordinatePolynomial} :=
  AdjoinRoot.NormalUnitPresentation.ker_aeval R Z.coordinateUnit

/-- The whole actual quotient algebra, not merely its generic fibre or reduced quotient. -/
def polynomialEquiv : AdjoinRoot Z.coordinatePolynomial ≃ₐ[R] Z.coordinateRing :=
  AdjoinRoot.NormalUnitPresentation.equiv R Z.coordinateUnit Z.laurent_eval_surjective

@[simp] theorem polynomialEquiv_root :
    Z.polynomialEquiv (AdjoinRoot.root Z.coordinatePolynomial) =
      (Z.coordinateUnit : Z.coordinateRing) :=
  AdjoinRoot.NormalUnitPresentation.equiv_root R Z.coordinateUnit Z.laurent_eval_surjective

@[simp] theorem polynomialEquiv_symm_coordinate :
    Z.polynomialEquiv.symm (Z.coordinateUnit : Z.coordinateRing) =
      AdjoinRoot.root Z.coordinatePolynomial := by
  apply Z.polynomialEquiv.injective
  rw [AlgEquiv.apply_symm_apply, Z.polynomialEquiv_root]

/-- The full native quotient scheme is isomorphic to the original integral support. -/
def polynomialSupportIso : Spec (.of (AdjoinRoot Z.coordinatePolynomial)) ≅ Z.support :=
  Scheme.Spec.mapIso Z.polynomialEquiv.symm.toRingEquiv.toCommRingCatIso.op ≪≫
    Z.support.isoSpec.symm

omit [IsDomain R] [IsIntegrallyClosed R] in
theorem supportIsoSpec_inv_map {A : Type u} [CommRing A]
    (k : Z.support ⟶ Spec (.of A)) :
    Z.support.isoSpec.inv ≫ k = Spec.map (CommRingCat.ofHom
      (k.appTop.hom.comp (Scheme.ΓSpecIso (.of A)).inv.hom)) := by
  rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

@[reassoc] theorem polynomialSupportIso_projection :
    Z.polynomialSupportIso.hom ≫ Z.projection =
      NativeTorusPolynomial.projection Z.coordinatePolynomial := by
  change Spec.map (CommRingCat.ofHom Z.polynomialEquiv.symm.toRingHom) ≫
    Z.support.isoSpec.inv ≫ Z.projection = _
  rw [Z.supportIsoSpec_inv_map, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact Z.polynomialEquiv.symm.commutes r

@[reassoc] theorem polynomialSupportIso_laurentEmbedding :
    Z.polynomialSupportIso.hom ≫ Z.laurentEmbedding =
      chartQuotient Z.coordinatePolynomial Z.coordinatePolynomial_constant_isUnit := by
  change Spec.map (CommRingCat.ofHom Z.polynomialEquiv.symm.toRingHom) ≫
    Z.support.isoSpec.inv ≫ Z.laurentEmbedding = _
  rw [Z.supportIsoSpec_inv_map, ← Spec.map_comp]
  unfold chartQuotient
  congr 1
  apply CommRingCat.hom_ext
  apply laurentRingHom_ext
  · intro r
    change Z.polynomialEquiv.symm (Z.laurentPullback (LaurentPolynomial.C r)) = _
    rw [Z.laurentPullback_C]
    exact (Z.polynomialEquiv.symm.commutes r).trans
      (LaurentPolynomial.eval₂_C _ _ r).symm
  · change Z.polynomialEquiv.symm (Z.coordinateUnit : Z.coordinateRing) =
      LaurentPolynomial.eval₂ (AdjoinRoot.of Z.coordinatePolynomial)
        (AdjoinRoot.rootUnit _ Z.coordinatePolynomial_constant_isUnit) (LaurentPolynomial.T 1)
    simp only [LaurentPolynomial.eval₂_T, zpow_one, Z.polynomialEquiv_symm_coordinate,
      AdjoinRoot.rootUnit_val]

@[reassoc] theorem polynomialSupportIso_inclusion :
    Z.polynomialSupportIso.hom ≫ Z.inclusion =
      NativeTorusPolynomial.inclusion f Z.coordinatePolynomial
        Z.coordinatePolynomial_constant_isUnit := by
  rw [← chartQuotient_chartMap, ← Z.polynomialSupportIso_laurentEmbedding]
  simp only [laurentEmbedding, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end PrimePoint

end AlgebraicGeometry.NativeTorusPolynomial
