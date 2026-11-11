/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.AffineExact
import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.SmoothReducedExact
import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.NormNaturality

/-! # Consumers of the actual canonical reduced-torus affine sequence -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Stacks.Chow Polynomial
open AlgebraicGeometry.NativeTorusPolynomial
open Polynomial.BoundaryOneRationalFunctions
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers

universe u

section CanonicalQuotient

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k))) [IsIntegral X.left]

example (z : sections (torusRepresentable k 1) (Cor.mk X)) :
    z ∈ torusIdentityRelations k 1 (Cor.mk X) ↔
      ∃ n : ℤ, z = ULift.up (n • torusIdentityGraph k X) :=
  mem_torusIdentityRelations_one_iff X z

example (z : sections (torusRepresentable k 1) (Cor.mk X)) :
    (toReducedTorus k 1).hom.app (op (Cor.mk X)) z = 0 ↔
      ∃ n : ℤ, z = ULift.up (n • torusIdentityGraph k X) :=
  toReducedTorus_eq_zero_iff_identityGraph X z

example (z : Cor.mk X ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) :
    (toReducedTorus k 1).hom.app (op (Cor.mk X))
        (ULift.up (z + (-3 : ℤ) • torusIdentityGraph k X)) =
      (toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up z) :=
  toReducedTorus_add_identityGraph X z (-3)

end CanonicalQuotient

section AffineSpec

variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R] [IsNoetherianRing R]
variable (f : Spec (.of R) ⟶ Spec (.of k)) [Smooth f] [IsSeparated f] [QuasiCompact f]

example : powerOneCycleEquiv f (torusIdentityGraph k (mk f)) =
    unitGraphCycle f 1 (Cor.finite_genericPoints k (Cor.mk (mk f))) :=
  powerOneCycleEquiv_identityGraph f

example : Function.Injective (reducedBoundaryDivisor f) := reducedBoundaryDivisor_injective f

example : Function.Surjective (reducedNormApp f) := reducedNormApp_surjective f

example (z : sections (reducedTorus k 1) (Cor.mk (mk f))) :
    reducedNormApp f z = 0 ↔ ∃ m, reducedBoundaryDivisor f m = z :=
  reducedNormApp_eq_zero_iff f z

example : (reducedDivisorShortComplex f).ShortExact := reducedDivisorShortComplex_shortExact f

example : (specSectionsReducedDivisorShortComplex f).ShortExact :=
  specSectionsReducedDivisorShortComplex_shortExact f

example (z : Cor.mk (mk f) ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) :
    specSectionsReducedNorm f
        ((toReducedTorus k 1).hom.app (op (Cor.mk (mk f))) (ULift.up z)) =
      ULift.up (Additive.ofMul (specGlobalUnit (powerOneNorm f z).toMul)) :=
  specSectionsReducedNorm_toReduced f z

end AffineSpec

section OriginalSmoothAffineObjects

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  [IsAffine X.left] [IsIntegral X.left]

example : IsIntegrallyClosed Γ(X.left, ⊤) :=
  AffineSectionCoordinates.sections_isIntegrallyClosed X

example : IsNoetherianRing Γ(X.left, ⊤) :=
  AffineSectionCoordinates.sections_isNoetherianRing X

example : (affineReducedDivisorShortComplex X).X₁ =
    (largeBoundaryOnePresheaf k).obj (op X) := rfl

example : (affineReducedDivisorShortComplex X).X₂ =
    ((toPresheaf k).obj (reducedTorus k 1)).obj (op X) := rfl

example : (affineReducedDivisorShortComplex X).X₃ =
    (largeUnitsPresheaf (Spec (.of k))).obj (op X) := rfl

example : (affineReducedDivisorShortComplex X).ShortExact :=
  affineReducedDivisorShortComplex_shortExact X

example : Function.Injective (affineReducedBoundaryDivisor X) :=
  affineReducedBoundaryDivisor_injective X

example : Function.Surjective (affineReducedNorm X) := affineReducedNorm_surjective X

example (z : ((toPresheaf k).obj (reducedTorus k 1)).obj (op X)) :
    affineReducedNorm X z = 0 ↔ ∃ m, affineReducedBoundaryDivisor X m = z :=
  affineReducedNorm_eq_zero_iff X z

end OriginalSmoothAffineObjects

section OriginalSmoothAlgebras

variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R] [IsDomain R]

example : (smoothAffineReducedDivisorShortComplex k R).ShortExact :=
  smoothAffineReducedDivisorShortComplex_shortExact k R

end OriginalSmoothAlgebras

section WholeCoefficientFibers

variable {S : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]
  [IsDomain R] [IsIntegrallyClosed R] [IsDomain A] [IsIntegrallyClosed A]
  [IsNoetherianRing A] {f : Spec (.of R) ⟶ S} (Z : PrimePoint f) (a : R →+* A)

example : Flat Z.projection := inferInstance

example : (Z.coefficientFiberCycle a).val =
    finiteCyclePushforward (Z.coefficientFiberMap a)
      (AlgebraicCycle.fundamentalCycle (Z.coefficientFiber a)) :=
  Z.coefficientFiberCycle_val a

example : Z.coefficientFiberCycle a =
    polynomialCycle (Spec.map (CommRingCat.ofHom a) ≫ f)
      (Z.coordinatePolynomial.map a) (Z.coordinatePolynomial_monic.map a)
      (map_constant_isUnit a Z.coordinatePolynomial Z.coordinatePolynomial_constant_isUnit) :=
  Z.coefficientFiberCycle_eq_polynomialCycle a

example : cycleRationalFunction (Spec.map (CommRingCat.ofHom a) ≫ f)
    (Z.coefficientFiberCycle a) = Additive.ofMul (admissibleMap a Z.rationalFunction) :=
  Z.cycleRationalFunction_coefficientFiberCycle a

example : cycleNorm (Spec.map (CommRingCat.ofHom a) ≫ f) (Z.coefficientFiberCycle a) =
    Additive.ofMul (Units.map a.toMonoidHom Z.coordinateNorm) :=
  Z.cycleNorm_coefficientFiberCycle a

example : cycleNorm (Spec.map (CommRingCat.ofHom a) ≫ f)
    ((-3 : ℤ) • Z.coefficientFiberCycle a) =
      Additive.ofMul ((Units.map a.toMonoidHom Z.coordinateNorm) ^ (-3 : ℤ)) :=
  Z.cycleNorm_zsmul_coefficientFiberCycle a (-3)

end WholeCoefficientFibers

section NonreducedCoefficientFibers

variable {S : Scheme.{u}} {R A : Type u} [CommRing R] [CommRing A]
  [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing A]
  {f : Spec (.of R) ⟶ S} (Z : PrimePoint f) (a : R →+* A)

example : (Z.coefficientFiberCycle a).val =
    finiteCyclePushforward (Z.coefficientFiberMap a)
      (AlgebraicCycle.fundamentalCycle (Z.coefficientFiber a)) :=
  Z.coefficientFiberCycle_val a

end NonreducedCoefficientFibers

section ArbitraryCoefficientSquare

variable {R A : Type u} [CommRing R] [CommRing A] (a : R →+* A) (p : R[X])

example : IsPullback (projection (p.map a)) (specialization a p)
    (Spec.map (CommRingCat.ofHom a)) (projection p) :=
  specialization_isPullback a p

end ArbitraryCoefficientSquare
