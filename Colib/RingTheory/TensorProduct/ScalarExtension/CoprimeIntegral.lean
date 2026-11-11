/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.TensorProduct.ScalarExtension.ResidueFiber
public import Colib.AlgebraicGeometry.Morphisms.FiniteEtale.SingletonFiber
public import Colib.RingTheory.Bertini.ClosedPointMovingCoefficients
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Integral scalar extensions from coprime residue degree

The entire scalar scheme remains integral. This uses native smooth regularity,
normality and the finite-open singleton-fiber criterion, not the old external
smooth-normal/domain-stalk packages. No component or residue branch is selected.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Algebra.TensorProduct

universe u

/-- The original smooth affine domain stays a domain, and its entire original
closed marked fiber consists of one point, under a coprime finite separable
scalar extension. Closedness supplies finiteness of the residue degree. -/
theorem isDomain_and_unique_prime_over_of_coprime_closedPoint
    (k R L : Type u) [Field k] [CommRing R] [IsDomain R] [Field L]
    [Algebra k R] [Algebra.Smooth k R] [Algebra k L]
    [Module.Finite k L] [Algebra.IsSeparable k L]
    (x : PrimeSpectrum R) [x.asIdeal.IsMaximal]
    (h : (Module.finrank k x.asIdeal.ResidueField).Coprime (Module.finrank k L)) :
    IsDomain (R ⊗[k] L) ∧
      ∃! y : PrimeSpectrum (R ⊗[k] L),
        PrimeSpectrum.comap (algebraMap R (R ⊗[k] L)) y = x := by
  let := QuadraticIncidence.ClosedPoint.residueField_finite k R x
  have hu := existsUnique_prime_over_of_coprime_residueDegree k R L x h
  obtain ⟨y, hy, hyunique⟩ := hu
  let S := R ⊗[k] L
  let : Algebra.FormallyEtale k L := Algebra.FormallyEtale.of_isSeparable k L
  let : Algebra.FinitePresentation k L :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale k L := {}
  let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  let f : Spec (.of S) ⟶ Spec (.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  have : IsFinite f := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  have : AlgebraicGeometry.Etale f := HasRingHomProperty.Spec_iff.mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  let b : Spec (.of S) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k S))
  have : AlgebraicGeometry.Smooth b := HasRingHomProperty.Spec_iff.mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)
  let : IsNormal (Spec (.of S)) :=
    isNormal_of_isRegular _ (isRegular_of_smooth_over_field b)
  have hI : IsIntegral (Spec (.of S)) :=
    Scheme.isIntegral_of_finite_etale_singletonFiber_of_isNormal f y
      (fun t ht => hyunique t (ht.trans hy))
  exact ⟨(affine_isIntegral_iff (.of S)).mp hI, ⟨y, hy, hyunique⟩⟩

end Algebra.TensorProduct

