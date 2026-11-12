/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # The zero-coordinate case over a finite separable coefficient field

Every actual étale chart over the zero-variable polynomial ring has an étale
structure map to the original ground field, not just the polynomial ring itself.
-/
@[expose] public noncomputable section
open AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Étale coordinates of dimension zero give an étale map to the original base. -/
theorem finiteSeparable_zeroCoordinate_structure_etale
    (K E B : Type u) [Field K] [Field E] [CommRing B]
    [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E]
    [Algebra E B] [Algebra K B] [IsScalarTower K E B]
    (q : MvPolynomial (Fin 0) E →ₐ[E] B) (hq : q.toRingHom.Etale) :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap K B))) := by
  let : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  let : Algebra.FinitePresentation K E :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale K E := {}
  let : Algebra.Etale E (MvPolynomial (Fin 0) E) :=
    Algebra.Etale.of_equiv (MvPolynomial.isEmptyAlgEquiv E (Fin 0)).symm
  have hEB : (algebraMap E B).Etale := by
    have h := RingHom.Etale.stableUnderComposition (algebraMap E (MvPolynomial (Fin 0) E))
      q.toRingHom (RingHom.etale_algebraMap.mpr inferInstance) hq
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap] using h
  have hKB : (algebraMap K B).Etale := by
    have h := RingHom.Etale.stableUnderComposition (algebraMap K E)
      (algebraMap E B) (RingHom.etale_algebraMap.mpr inferInstance) hEB
    simpa only [← IsScalarTower.algebraMap_eq K E B] using h
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hKB

end AlgebraicGeometry.Scheme
