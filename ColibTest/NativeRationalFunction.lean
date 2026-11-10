module

import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.InverseNaturality
import Colib.RingTheory.Smooth.IntegrallyClosed

/-! Source-only consumers of actual native supports, signed fractions, and determinant norms. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial Stacks.Chow TopologicalSpace
open AlgebraicGeometry.NativeTorusPolynomial Polynomial.BoundaryOneRationalFunctions

universe u v

section RingPresentation

variable {R : Type u} {A : Type v} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing A] [IsDomain A] [Algebra R A] [Module.IsTorsionFree R A] [Module.Finite R A]
  (t : Aˣ) (ht : Function.Surjective (LaurentPolynomial.eval₂ (algebraMap R A) t))

example : (minpoly R (t : A)).Monic := AdjoinRoot.NormalUnitPresentation.minpoly_monic R t

example : IsUnit ((minpoly R (t : A)).coeff 0) :=
  AdjoinRoot.NormalUnitPresentation.minpoly_coeff_zero_isUnit R t

example : Prime (minpoly R (t : A)) := AdjoinRoot.NormalUnitPresentation.minpoly_prime R t

example : AdjoinRoot (minpoly R (t : A)) ≃ₐ[R] A :=
  AdjoinRoot.NormalUnitPresentation.equiv R t ht

example : AdjoinRoot.NormalUnitPresentation.equiv R t ht
    (AdjoinRoot.root (minpoly R (t : A))) = (t : A) :=
  AdjoinRoot.NormalUnitPresentation.equiv_root R t ht

example : RingHom.ker (Polynomial.aeval (t : A)).toRingHom =
    Ideal.span {minpoly R (t : A)} := AdjoinRoot.NormalUnitPresentation.ker_aeval R t

example (p : R[X]) (hp : p.Monic) (hu : IsUnit (p.coeff 0)) :
    ∃ factors : List R[X], factors.prod = p ∧
      ∀ q ∈ factors, q.Monic ∧ Prime q ∧ IsUnit (q.coeff 0) :=
  Polynomial.NormalMonicFactorization.exists_list_monic_prime_factors_of_normal p hp hu

end RingPresentation

section NativeGeometry

variable {S T : Scheme.{u}} {R : Type u} [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R] [IsNoetherianRing R]
  (f : Spec (.of R) ⟶ S) (g : Spec (.of R) ⟶ T)
  (Z : PrimePoint f) (p q : denominators R)
  (c : finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S))
  (a : Additive (admissibleGroup R))

example : Function.Injective Z.scalarMap := Z.scalarMap_injective

example : Function.Surjective (LaurentPolynomial.eval₂
    (algebraMap R Z.coordinateRing) Z.coordinateUnit) := Z.laurent_eval_surjective

example : AdjoinRoot Z.coordinatePolynomial ≃ₐ[R] Z.coordinateRing := Z.polynomialEquiv

example : Spec (.of (AdjoinRoot Z.coordinatePolynomial)) ≅ Z.support := Z.polynomialSupportIso

example : Z.polynomialSupportIso.hom ≫ Z.inclusion =
    inclusion f Z.coordinatePolynomial Z.coordinatePolynomial_constant_isUnit :=
  Z.polynomialSupportIso_inclusion

example : polynomialCycle f Z.coordinatePolynomial Z.coordinatePolynomial_monic
    Z.coordinatePolynomial_constant_isUnit =
      singleFiniteCorrespondence f (multiplicativeGroupBaseChange S ↘ S) Z.val Z.property 1 :=
  Z.polynomialCycle_eq_single

example : cycleRationalFunction f
    (singleFiniteCorrespondence f (multiplicativeGroupBaseChange S ↘ S) Z.val Z.property (-3)) =
      (-3 : ℤ) • Additive.ofMul Z.rationalFunction := cycleRationalFunction_single f _ _ _

example : rationalDivisorHom f (cycleRationalFunction f c) = c :=
  rationalDivisorHom_cycleRationalFunction f c

example : cycleRationalFunction f (rationalDivisorHom f a) = a :=
  cycleRationalFunction_rationalDivisorHom f a

example : Additive (admissibleGroup R) ≃+
    finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) := rationalDivisorEquiv f

example : Function.Injective (boundaryDivisor f) := boundaryDivisor_injective f

example : cycleRationalFunction f (denominatorCycle f (p ^ 7)) =
    Additive.ofMul (admissibleFraction (p ^ 7) 1) := cycleRationalFunction_denominator f _

example : rationalDivisor f (admissibleFraction p q ^ (-3 : ℤ)) =
    (-3 : ℤ) • rationalDivisor f (admissibleFraction p q) := rationalDivisor_zpow f _ _

example (hp : Prime p.val) :
    (primePoint f p.val p.property.1 p.property.2 hp).coordinatePolynomial = p.val :=
  coordinatePolynomial_primePoint f p.val p.property.1 p.property.2 hp

example : Module.Free R Z.coordinateRing := Z.coordinateFree

example : Z.coordinateUnit =
    Units.map Z.inclusion.appTop.hom.toMonoidHom (ambientCoordinate f) :=
  Z.coordinateUnit_eq_native

example : (Z.coordinateNorm : R) = Algebra.norm R (Z.coordinateUnit : Z.coordinateRing) := rfl

example : cycleNorm f (denominatorCycle f p) = Additive.ofMul (spanNorm f p.val p.property.2) :=
  cycleNorm_denominator f p

example (v : Rˣ) (hR : (genericPoints (Spec (.of R))).Finite) :
    cycleNorm f (unitGraphCycle f v hR) = Additive.ofMul v := cycleNorm_unitGraph f v hR

example (hR : (genericPoints (Spec (.of R))).Finite) :
    cycleNorm f c = 0 ↔ ∃ (m : Additive (group R)) (d : ℤ),
      c = boundaryDivisor f m + d • unitGraphCycle f 1 hR := cycleNorm_eq_zero_iff f hR c

example (hR : (genericPoints (Spec (.of R))).Finite) (m : Additive (group R)) (d : ℤ)
    (h : boundaryDivisor f m = d • unitGraphCycle f 1 hR) : m = 0 ∧ d = 0 :=
  boundaryDivisor_identityGraph_intersection f hR m d h

example : cycleRationalFunction g (ambientChangeHom f g c) = cycleRationalFunction f c :=
  cycleRationalFunction_ambientChangeHom f g c

example : cycleNorm g (ambientChangeHom f g c) = cycleNorm f c :=
  cycleNorm_ambientChangeHom f g c

end NativeGeometry

section IntegralCoefficients

example : Function.Injective
    (rationalDivisorHom (𝟙 (Spec (.of ℤ)))) := rationalDivisorHom_injective _

example : Function.Surjective
    (cycleNorm (𝟙 (Spec (.of ℤ)))) := cycleNorm_surjective _

example (v : ℤˣ) : cycleRationalFunction (𝟙 (Spec (.of ℤ)))
    (denominatorCycle (𝟙 (Spec (.of ℤ))) ((unitDenominator v) ^ 7)) =
      Additive.ofMul (admissibleFraction ((unitDenominator v) ^ 7) 1) :=
  cycleRationalFunction_denominator _ _

end IntegralCoefficients

section OriginalSmoothIntegralScope

variable {k : Type v} {R : Type u} [Field k] [CommRing R] [Algebra k R]
  [Algebra.Smooth k R] [IsDomain R] {S : Scheme.{u}} (f : Spec (.of R) ⟶ S)

example : IsIntegrallyClosed R := Algebra.Smooth.isIntegrallyClosed_of_field k R

example : Additive (admissibleGroup R) ≃+
    finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) := by
  letI := Algebra.Smooth.isIntegrallyClosed_of_field k R
  letI := Algebra.FiniteType.isNoetherianRing k R
  exact rationalDivisorEquiv f

example : ∃ n : finiteCorrespondences f (multiplicativeGroupBaseChange S ↘ S) →+ Additive Rˣ,
    Function.Surjective n := by
  have := Algebra.Smooth.isIntegrallyClosed_of_field k R
  have := Algebra.FiniteType.isNoetherianRing k R
  exact ⟨cycleNorm f, cycleNorm_surjective f⟩

end OriginalSmoothIntegralScope
