/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.CycleRationalFunction

/-!
# Actual native prime supports of monic prime polynomials

The prime point is the generic point of the actual closed quotient image.
Its native integral support is exactly that image ideal. Equal such points
give equal actual Laurent kernel sheaves, hence mutual polynomial divisibility.
Monicity removes the scalar ambiguity. These are geometric support arguments,
not assumed injectivity of divisors or an abstract inverse interface.

Adapted to native points and integer cycles from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Correspondences/Torus/Affine/PrimePolynomial.lean`, blob
`7b9e9854f028ad224c576bcf52cc0ef0a8977a20`. Source-only.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R : Type u} [CommRing R]

attribute [local instance] inclusion_isClosedImmersion

/-- A finite flat map from an integral scheme covers a whole source component. -/
theorem range_mem_irreducibleComponents_of_integral_finite_flat
    {A X : Scheme.{u}} [IsIntegral A] (q : A ⟶ X) [IsFinite q] [Flat q] :
    Set.range q ∈ irreducibleComponents X := by
  have h := finiteFlat_range_integralComponentAt q (genericPoint A)
    (genericPoint_mem_genericPoints A)
  rw [finiteCyclePushforward_range_integralComponentAt,
    coe_support_integralComponentAt, (genericPoint_spec A).def, Set.image_univ] at h
  exact h

/-- The actual closed quotient image has the same projection up to its canonical isomorphism. -/
theorem inclusion_image_projection (f : Spec (.of R) ⟶ S) (p : R[X])
    (hu : IsUnit (p.coeff 0)) :
    (inclusion f p hu).imageι ≫ pullback.fst _ _ =
      inv (inclusion f p hu).toImage ≫ projection p := by
  apply (cancel_epi (inclusion f p hu).toImage).mp
  simp only [← Category.assoc, Scheme.Hom.toImage_imageι, inclusion_fst,
    IsIso.hom_inv_id, Category.id_comp]

/-- The actual native prime point of a whole monic prime quotient. -/
def primePoint (f : Spec (.of R) ⟶ S) (p : R[X]) (hp : p.Monic)
    (hu : IsUnit (p.coeff 0)) (hprime : Prime p) : PrimePoint f := by
  letI : IsDomain (AdjoinRoot p) := AdjoinRoot.isDomain_of_prime hprime
  letI := projection_isFinite p hp
  letI := projection_flat p hp
  let i := inclusion f p hu
  have hI : IsIntegral i.image := IsIntegral.of_isIso i.toImage
  refine ⟨genericPointOf i.ker hI,
    (isFiniteCorrespondencePoint_genericPointOf_iff f
      (multiplicativeGroupBaseChange S ↘ S) i.ker hI).mpr ?_⟩
  constructor
  · change IsFinite (i.imageι ≫ pullback.fst _ _)
    rw [inclusion_image_projection]
    infer_instance
  · change Set.range (i.imageι ≫ pullback.fst _ _) ∈ _
    rw [inclusion_image_projection]
    change Set.range (projection p ∘ inv i.toImage) ∈ _
    rw [Set.range_comp, Set.range_eq_univ.mpr (inv i.toImage).surjective, Set.image_univ]
    exact range_mem_irreducibleComponents_of_integral_finite_flat (projection p)

/-- The native integral support retains the actual closed quotient ideal. -/
theorem primePoint_ideal (f : Spec (.of R) ⟶ S) (p : R[X]) (hp : p.Monic)
    (hu : IsUnit (p.coeff 0)) (hprime : Prime p) :
    integralComponentAt (primePoint f p hp hu hprime).val = (inclusion f p hu).ker := by
  have : IsDomain (AdjoinRoot p) := AdjoinRoot.isDomain_of_prime hprime
  have hI : IsIntegral (inclusion f p hu).image :=
    IsIntegral.of_isIso (inclusion f p hu).toImage
  exact integralComponentAt_genericPointOf (inclusion f p hu).ker hI

/-- Passing through the actual closed image does not change the Laurent kernel. -/
theorem chartQuotient_ker_eq_image_chart_ker (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    (chartQuotient p hu).ker =
      ((inclusion f p hu).imageι ≫ (nativeChartIso f).inv).ker := by
  calc
    (chartQuotient p hu).ker = (inclusion f p hu ≫ (nativeChartIso f).inv).ker := by
      rw [← chartQuotient_chartMap]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = ((inclusion f p hu).toImage ≫
        (inclusion f p hu).imageι ≫ (nativeChartIso f).inv).ker := by
      rw [← Category.assoc, Scheme.Hom.toImage_imageι]
    _ = _ := Scheme.Hom.ker_comp_of_isIso _ _

/-- Equality of native prime points gives equality of the actual Laurent kernel sheaves. -/
theorem primePoint_eq_kernel (f : Spec (.of R) ⟶ S) (p q : R[X])
    (hp : p.Monic) (hq : q.Monic) (hpu : IsUnit (p.coeff 0)) (hqu : IsUnit (q.coeff 0))
    (hpp : Prime p) (hqp : Prime q)
    (h : primePoint f p hp hpu hpp = primePoint f q hq hqu hqp) :
    (chartQuotient p hpu).ker = (chartQuotient q hqu).ker := by
  have hi : (inclusion f p hpu).ker = (inclusion f q hqu).ker := by
    rw [← primePoint_ideal f p hp hpu hpp, ← primePoint_ideal f q hq hqu hqp, h]
  rw [chartQuotient_ker_eq_image_chart_ker f, chartQuotient_ker_eq_image_chart_ker f]
  change ((inclusion f p hpu).ker.subschemeι ≫ (nativeChartIso f).inv).ker =
    ((inclusion f q hqu).ker.subschemeι ≫ (nativeChartIso f).inv).ker
  rw [hi]

/-- Actual Laurent kernel inclusion detects ordinary polynomial divisibility. -/
theorem dvd_of_chartQuotient_ker_le (p q : R[X])
    (hpu : IsUnit (p.coeff 0)) (hqu : IsUnit (q.coeff 0))
    (h : (chartQuotient q hqu).ker ≤ (chartQuotient p hpu).ker) : p ∣ q := by
  have hmem : (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent q) ∈
      (chartQuotient p hpu).ker.ideal
        ⟨⊤, isAffineOpen_top (Spec (.of (LaurentPolynomial R)))⟩ := by
    apply h ⟨⊤, isAffineOpen_top (Spec (.of (LaurentPolynomial R)))⟩
    rw [chartQuotient_ker_top]
    exact Ideal.subset_span (Set.mem_singleton _)
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker] at hmem
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (chartQuotientHom p hpu)))
    (toLaurent q)
  change (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv
      (chartQuotientHom p hpu (toLaurent q)) =
    (chartQuotient p hpu).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent q)) at hn
  change (chartQuotient p hpu).appTop
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent q)) = 0 at hmem
  rw [hmem, chartQuotientHom_toLaurent] at hn
  apply AdjoinRoot.mk_eq_zero.mp
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv).1
  simpa only [map_zero] using hn

/-- Distinct monic prime equations define distinct actual native prime supports. -/
theorem primePoint_injective (f : Spec (.of R) ⟶ S) (p q : R[X])
    (hp : p.Monic) (hq : q.Monic) (hpu : IsUnit (p.coeff 0)) (hqu : IsUnit (q.coeff 0))
    (hpp : Prime p) (hqp : Prime q)
    (h : primePoint f p hp hpu hpp = primePoint f q hq hqu hqp) : p = q := by
  have he := primePoint_eq_kernel f p q hp hq hpu hqu hpp hqp h
  have hpq := dvd_of_chartQuotient_ker_le p q hpu hqu he.ge
  have hqp' := dvd_of_chartQuotient_ker_le q p hqu hpu he.le
  exact (eq_of_monic_of_dvd_of_natDegree_le hp hq hpq
    (hq.natDegree_le_of_dvd hpp.ne_zero hqp')).symm

variable [IsNoetherianRing R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The whole prime quotient contributes one at its actual native prime point. -/
theorem polynomialCycle_eq_primePoint (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0)) (hprime : Prime p) :
    polynomialCycle f p hp hu = singleFiniteCorrespondence f
      (multiplicativeGroupBaseChange S ↘ S) (primePoint f p hp hu hprime).val
        (primePoint f p hp hu hprime).property 1 := by
  have : IsDomain (AdjoinRoot p) := AdjoinRoot.isDomain_of_prime hprime
  have := projection_isFinite p hp
  let i := inclusion f p hu
  have : IsIntegral i.image := IsIntegral.of_isIso i.toImage
  have : IsFinite (i.imageι ≫ pullback.fst _ _) := by
    rw [inclusion_image_projection]
    infer_instance
  have : IsAffine i.image := isAffine_of_isAffineHom (i.imageι ≫ pullback.fst _ _)
  have : IsNoetherian i.image :=
    { toIsLocallyNoetherian :=
        LocallyOfFiniteType.isLocallyNoetherian (i.imageι ≫ pullback.fst _ _)
      toCompactSpace := inferInstance }
  apply Subtype.ext
  rw [polynomialCycle_val]
  change finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle _) = _
  have h := finiteCyclePushforward_comp_apply i.toImage i.imageι
    (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot p))))
  have hi : finiteCyclePushforward i.toImage
      (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot p)))) =
        AlgebraicCycle.fundamentalCycle i.image := by
    have hIso := finiteCyclePushforward_fundamentalCycle_iso (asIso i.toImage)
    dsimp only [asIso] at hIso
    exact hIso
  rw [hi] at h
  have he : finiteCyclePushforward i
      (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot p)))) =
        finiteCyclePushforward i.imageι (AlgebraicCycle.fundamentalCycle i.image) := by
    simpa only [i.toImage_imageι] using h.symm
  rw [he, finiteCyclePushforward_fundamentalCycle_integral]
  rfl

variable [IsDomain R] [IsIntegrallyClosed R]

namespace PrimePoint

variable {f : Spec (.of R) ⟶ S} (Z : PrimePoint f)

omit [IsNoetherianRing R] in
/-- The literal coordinate polynomial is prime because its evaluation target is a domain. -/
theorem coordinatePolynomial_prime : Prime Z.coordinatePolynomial :=
  AdjoinRoot.NormalUnitPresentation.minpoly_prime R Z.coordinateUnit

/-- A native admissible point is recovered as its actual prime-polynomial support. -/
theorem eq_primePoint_coordinatePolynomial :
    Z = primePoint f Z.coordinatePolynomial Z.coordinatePolynomial_monic
      Z.coordinatePolynomial_constant_isUnit Z.coordinatePolynomial_prime := by
  classical
  apply Subtype.ext
  have hc := Z.polynomialCycle_eq_single.symm.trans
    (polynomialCycle_eq_primePoint f Z.coordinatePolynomial Z.coordinatePolynomial_monic
      Z.coordinatePolynomial_constant_isUnit Z.coordinatePolynomial_prime)
  have he := congrArg (fun c : finiteCorrespondences f
    (multiplicativeGroupBaseChange S ↘ S) => c.val Z.val) hc
  by_contra h
  simp [singleFiniteCorrespondence, single_apply, h] at he

end PrimePoint

/-- A monic prime equation is recovered literally, not just up to association. -/
@[simp] theorem coordinatePolynomial_primePoint (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0)) (hprime : Prime p) :
    (primePoint f p hp hu hprime).coordinatePolynomial = p := by
  let Z := primePoint f p hp hu hprime
  exact (primePoint_injective f p Z.coordinatePolynomial hp Z.coordinatePolynomial_monic
    hu Z.coordinatePolynomial_constant_isUnit hprime Z.coordinatePolynomial_prime
      Z.eq_primePoint_coordinatePolynomial).symm

end AlgebraicGeometry.NativeTorusPolynomial
