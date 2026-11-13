/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.PolynomialCycle
public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.NativeChart
public import Colib.AlgebraicGeometry.Chow.FiniteFlatProduct
public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Product additivity of whole native polynomial cycles

The auxiliary affine coordinate chart is the explicit isomorphism to the
retained native ambient. Its quotient kernel is the actual principal ideal,
not its radical. Product additivity follows from the concrete local quotient
exact sequence and finite-length proofs over generic source points, then is
transported through that actual isomorphism. All correspondence values remain
in the original native `finiteCorrespondences` group.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial TopologicalSpace
open Stacks.Chow

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {S : Scheme.{u}} {R : Type u} [CommRing R]

/-- The quotient homomorphism in the auxiliary coordinate chart. -/
def chartQuotientHom (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    LaurentPolynomial R →+* AdjoinRoot p :=
  LaurentPolynomial.eval₂ (AdjoinRoot.of p) (AdjoinRoot.rootUnit p hu)

theorem chartQuotientHom_toLaurent (p : R[X]) (hu : IsUnit (p.coeff 0)) (q : R[X]) :
    chartQuotientHom p hu (toLaurent q) = AdjoinRoot.mk p q := by
  rw [chartQuotientHom, LaurentPolynomial.eval₂_toLaurent,
    AdjoinRoot.rootUnit_val, ← AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.aeval_eq q

/-- The literal quotient is surjective, with no reducedness or monicity assumption. -/
theorem chartQuotientHom_surjective (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    Function.Surjective (chartQuotientHom p hu) := by
  intro a
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective (g := p) a
  exact ⟨toLaurent q, chartQuotientHom_toLaurent p hu q⟩

/-- The affine chart's actual closed quotient map. -/
def chartQuotient (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    Spec (.of (AdjoinRoot p)) ⟶ Spec (.of (LaurentPolynomial R)) :=
  Spec.map (CommRingCat.ofHom (chartQuotientHom p hu))

instance chartQuotient_isClosedImmersion (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    IsClosedImmersion (chartQuotient p hu) :=
  IsClosedImmersion.spec_of_surjective _ (chartQuotientHom_surjective p hu)

@[reassoc] theorem chartQuotient_projection (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    chartQuotient p hu ≫ chartProjection = projection p := by
  unfold chartQuotient chartProjection projection
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact LaurentPolynomial.eval₂_C _ _ r

theorem chartQuotientHom_unit (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    Units.map (chartQuotientHom p hu).toMonoidHom chartUnit = AdjoinRoot.rootUnit p hu := by
  apply Units.ext
  simp [chartQuotientHom, chartUnit_val]

/-- The chart quotient is exactly the original native span, not a substitute support. -/
@[reassoc] theorem chartQuotient_chartMap (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    chartQuotient p hu ≫ (nativeChartIso f).hom = inclusion f p hu := by
  apply pullback.hom_ext
  · simp only [Category.assoc, nativeChartIso, chartMap_fst, chartQuotient_projection,
      inclusion_fst]
  · simp only [Category.assoc, nativeChartIso, chartMap_snd, inclusion_snd]
    have h := nativeAffineTorusPoint_natural (chartProjection ≫ f)
      (chartQuotientHom p hu) chartUnit
    rw [chartQuotientHom_unit] at h
    change (nativeAffineTorusPoint (chartQuotient p hu ≫ (chartProjection ≫ f)) _).left = _ at h
    rw [← Category.assoc, chartQuotient_projection] at h
    exact h.symm

/-- The chart retains the whole defining ideal, including every repeated factor. -/
theorem chartQuotientHom_ker (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    RingHom.ker (chartQuotientHom p hu) = Ideal.span {toLaurent p} := by
  apply le_antisymm
  · intro a ha
    obtain ⟨n, q, hq⟩ := LaurentPolynomial.exists_T_pow a
    have hq0 : AdjoinRoot.mk p q = 0 := by
      rw [← chartQuotientHom_toLaurent p hu, hq, map_mul, RingHom.mem_ker.mp ha, zero_mul]
    obtain ⟨r, hr⟩ := AdjoinRoot.mk_eq_zero.mp hq0
    apply (Ideal.unit_mul_mem_iff_mem (Ideal.span {toLaurent p})
      (LaurentPolynomial.isUnit_T n)).mp
    rw [mul_comm, ← hq, hr, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _))
  · apply Ideal.span_le.mpr
    rintro a (rfl : a = toLaurent p)
    change chartQuotientHom p hu (toLaurent p) = 0
    rw [chartQuotientHom_toLaurent, AdjoinRoot.mk_self]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The kernel sheaf on the chart has precisely the principal global equation. -/
theorem chartQuotient_ker_top (p : R[X]) (hu : IsUnit (p.coeff 0)) :
    (chartQuotient p hu).ker.ideal
        ⟨⊤, isAffineOpen_top (Spec (.of (LaurentPolynomial R)))⟩ =
      Ideal.span {(Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent p)} := by
  rw [Scheme.Hom.ker_apply]
  change RingHom.ker (chartQuotient p hu).appTop.hom =
    Ideal.span {(Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent p)}
  apply Ideal.comap_injective_of_surjective
    (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv).2
  rw [RingHom.comap_ker]
  have hn := congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (chartQuotientHom p hu)))
  change (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv.hom.comp (chartQuotientHom p hu) =
    (chartQuotient p hu).appTop.hom.comp
      (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom at hn
  rw [← hn, RingHom.ker_comp_of_injective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (AdjoinRoot p))).inv).1,
    chartQuotientHom_ker]
  have hm : Ideal.span {(Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent p)} =
      (Ideal.span {toLaurent p}).map
        (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv.hom := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hm, Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv)]

/-- The actual polynomial section in the chart's native structure-sheaf stalk. -/
def chartPolynomialGerm (p : R[X]) (x : Spec (.of (LaurentPolynomial R))) :
    (Spec (.of (LaurentPolynomial R))).presheaf.stalk x :=
  (Spec (.of (LaurentPolynomial R))).presheaf.germ ⊤ x (by trivial)
    ((Scheme.ΓSpecIso (.of (LaurentPolynomial R))).inv (toLaurent p))

/-- The actual stalk kernel is the principal polynomial germ, without radicalization. -/
theorem chartQuotient_ker_stalk (p : R[X]) (hu : IsUnit (p.coeff 0))
    (x : Spec (.of (LaurentPolynomial R))) :
    IdealSheafData.stalk (chartQuotient p hu).ker x = Ideal.span {chartPolynomialGerm p x} := by
  rw [IdealSheafData.stalk_eq_map_germ _ x
    ⟨⊤, isAffineOpen_top (Spec (.of (LaurentPolynomial R)))⟩ (by trivial),
    chartQuotient_ker_top, Ideal.map_span, Set.image_singleton]
  rfl

@[simp] theorem chartPolynomialGerm_mul (p q : R[X])
    (x : Spec (.of (LaurentPolynomial R))) :
    chartPolynomialGerm (p * q) x = chartPolynomialGerm p x * chartPolynomialGerm q x := by
  simp only [chartPolynomialGerm, map_mul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Monicity remains regular through both actual localizations, even over nonreduced rings. -/
theorem chartPolynomialGerm_regular (p : R[X]) (hp : p.Monic)
    (x : Spec (.of (LaurentPolynomial R))) :
    chartPolynomialGerm p x ∈
      nonZeroDivisors ((Spec (.of (LaurentPolynomial R))).presheaf.stalk x) := by
  let : Algebra (LaurentPolynomial R)
      ((Spec (.of (LaurentPolynomial R))).presheaf.stalk x) :=
    StructureSheaf.stalkAlgebra (LaurentPolynomial R) x
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := LaurentPolynomial R) x
  have : IsLocalization.AtPrime
      ((Spec (.of (LaurentPolynomial R))).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (LaurentPolynomial R) x
  change algebraMap (LaurentPolynomial R)
    ((Spec (.of (LaurentPolynomial R))).presheaf.stalk x) (toLaurent p) ∈ _
  apply IsLocalization.nonZeroDivisors_le_comap x.asIdeal.primeCompl _
  exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers (Polynomial.X : R[X]))
    (LaurentPolynomial R) hp.mem_nonZeroDivisors

variable [IsNoetherianRing R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Exact chart quotient lengths calculate the actual native correspondence coefficient. -/
theorem polynomialCycle_apply_chart (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0))
    (x : Spec (.of (LaurentPolynomial R)))
    (hx : chartProjection x ∈ genericPoints (Spec (.of R))) :
    (polynomialCycle f p hp hu).val ((nativeChartIso f).hom x) =
      ((Module.length ((Spec (.of (LaurentPolynomial R))).presheaf.stalk x)
        ((Spec (.of (LaurentPolynomial R))).presheaf.stalk x ⧸
          Ideal.span {chartPolynomialGerm p x})).toNat : ℤ) := by
  have := quotient_isNoetherian p
  have := inclusion_isClosedImmersion f p hu
  have : IsFinite (chartQuotient p hu ≫ chartProjection) := by
    rw [chartQuotient_projection]
    exact projection_isFinite p hp
  rw [polynomialCycle_val]
  have h := finiteCyclePushforward_comp_apply (chartQuotient p hu) (nativeChartIso f).hom
    (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot p))))
  have he : finiteCyclePushforward (inclusion f p hu)
      (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot p)))) =
        finiteCyclePushforward (nativeChartIso f).hom
          (finiteCyclePushforward (chartQuotient p hu)
            (AlgebraicCycle.fundamentalCycle (Spec (.of (AdjoinRoot p))))) := by
    simpa only [chartQuotient_chartMap] using h.symm
  rw [he, finiteCyclePushforward_apply_of_isClosedImmersion,
    finiteCyclePushforward_fundamentalCycle_apply_eq_quotientStalkLength
      chartProjection (chartQuotient p hu) x hx]
  unfold closedImmersionQuotientStalkLength
  rw [chartQuotient_ker_stalk]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Product additivity of the actual native correspondence, with all generic local lengths. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Torus/Affine/PolynomialProducts.lean:122-180"
  "adaptation" "Whole-cycle additivity from exact local lengths and the native coordinate chart"]
theorem polynomialCycle_mul (f : Spec (.of R) ⟶ S)
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic)
    (hp0 : IsUnit (p.coeff 0)) (hq0 : IsUnit (q.coeff 0)) :
    polynomialCycle f (p * q) (hp.mul hq) (by simpa using hp0.mul hq0) =
      polynomialCycle f p hp hp0 + polynomialCycle f q hq hq0 := by
  let hpq0 : IsUnit ((p * q).coeff 0) := by simpa using hp0.mul hq0
  have := quotient_isNoetherian p
  have := quotient_isNoetherian q
  have := quotient_isNoetherian (p * q)
  have : IsFinite (chartQuotient p hp0 ≫ chartProjection) := by
    rw [chartQuotient_projection]; exact projection_isFinite p hp
  have : IsFinite (chartQuotient q hq0 ≫ chartProjection) := by
    rw [chartQuotient_projection]; exact projection_isFinite q hq
  have : IsFinite (chartQuotient (p * q) hpq0 ≫ chartProjection) := by
    rw [chartQuotient_projection]; exact projection_isFinite (p * q) (hp.mul hq)
  have : Flat (chartQuotient p hp0 ≫ chartProjection) := by
    rw [chartQuotient_projection]; exact projection_flat p hp
  have : Flat (chartQuotient q hq0 ≫ chartProjection) := by
    rw [chartQuotient_projection]; exact projection_flat q hq
  have : Flat (chartQuotient (p * q) hpq0 ≫ chartProjection) := by
    rw [chartQuotient_projection]; exact projection_flat (p * q) (hp.mul hq)
  have hc := finiteCyclePushforward_fundamentalCycle_mul_of_stalk_ker chartProjection
    (chartQuotient p hp0) (chartQuotient q hq0) (chartQuotient (p * q) hpq0)
    (fun x _ => ⟨chartPolynomialGerm p x, chartPolynomialGerm q x,
      chartQuotient_ker_stalk p hp0 x, chartQuotient_ker_stalk q hq0 x,
      by rw [chartQuotient_ker_stalk, chartPolynomialGerm_mul],
      chartPolynomialGerm_regular q hq x⟩)
  apply Subtype.ext
  simpa only [AddSubgroup.coe_add, map_add, finiteCyclePushforward_comp_apply,
    chartQuotient_chartMap,
    polynomialCycle_val] using congrArg (finiteCyclePushforward (nativeChartIso f).hom) hc

@[simp] theorem polynomialCycle_one (f : Spec (.of R) ⟶ S) :
    polynomialCycle f (1 : R[X]) monic_one (by simp) = 0 := by
  have h := polynomialCycle_mul f (1 : R[X]) 1 monic_one monic_one (by simp) (by simp)
  simp only [one_mul] at h
  exact (add_left_cancel (a := polynomialCycle f 1 monic_one (by simp)))
    (by simpa only [add_zero] using h.symm)

/-- Repeated factors carry their full multiplicities in the native correspondence group. -/
theorem polynomialCycle_pow (f : Spec (.of R) ⟶ S)
    (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0)) (n : ℕ) :
    polynomialCycle f (p ^ n) (hp.pow n)
      (by simpa only [coeff_zero_eq_eval_zero, eval_pow] using hu.pow n) =
      n • polynomialCycle f p hp hu := by
  induction n with
  | zero => simp only [pow_zero, polynomialCycle_one, zero_nsmul]
  | succ n ih =>
    calc
      polynomialCycle f (p ^ (n + 1)) _ _ =
          polynomialCycle f (p ^ n) (hp.pow n)
            (by simpa only [coeff_zero_eq_eval_zero, eval_pow] using hu.pow n) +
            polynomialCycle f p hp hu := by
        simpa only [pow_succ] using
          polynomialCycle_mul f (p ^ n) p (hp.pow n) hp
            (by simpa only [coeff_zero_eq_eval_zero, eval_pow] using hu.pow n) hu
      _ = (n + 1) • polynomialCycle f p hp hu := by rw [ih, succ_nsmul]

end AlgebraicGeometry.NativeTorusPolynomial
