/-
Copyright (c) 2026 Colib, Motivic Cohomology and AxiomMath/Stacks contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.FieldToResidue
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.FieldTheory.Separable

/-!
# Original residue fields of closed and separable field-valued points

All scalar actions below are induced by the original structure map using native
`fieldToResidue`. The closed-point finiteness proof is extracted from pinned Stacks
`Variety/Curve/RamificationAlgebraicClosure.lean:234-255`, without its curve or ramification
hypotheses and dependencies. A point valued in a finite separable extension has closed
image and separable residue field, retaining its actual image point and structure map.

The structural residue-point formulas adapt the lower helpers in
`Colib/AlgebraicGeometry/MotivicCohomology/Diagonal/ResiduePointEvaluation.lean:39-66`
at Colib revision `443a52f87210e38c18984c0effd1dd5d8e8dd1d8`, without importing that application.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The native structural scalar map is precisely evaluation of the original global sections. -/
theorem fieldToResidue_eq_evaluation {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    fieldToResidue f x = (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x := rfl

/-- Pullback to the original residue point is the native global evaluation map. -/
theorem Scheme.fromSpecResidueField_appTop (X : Scheme.{u}) (x : X) :
    (X.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso (X.residueField x)).hom =
      X.Γevaluation x := by
  rw [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.fromSpecStalk_appTop]
  simp only [homOfLE_refl, op_id, Category.assoc]
  rw [show (Spec (X.presheaf.stalk x)).presheaf.map (𝟙 (Opposite.op ⊤)) = 𝟙 _ from
    (Spec (X.presheaf.stalk x)).presheaf.map_id _]
  simp only [Category.id_comp, Iso.inv_hom_id_assoc]
  exact X.germ_residue (U := ⊤) x trivial

/-- The actual residue point lies over the spectrum of the original structural scalar map. -/
theorem Scheme.fromSpecResidueField_comp_eq_spec_fieldToResidue
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    X.fromSpecResidueField x ≫ f = Spec.map (fieldToResidue f x) := by
  apply ext_of_isAffine
  apply (cancel_mono (Scheme.ΓSpecIso (X.residueField x)).hom).mp
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.fromSpecResidueField_appTop,
    Scheme.ΓSpecIso_naturality, fieldToResidue_eq_evaluation]
  simp only [Iso.hom_inv_id_assoc]

/-- A closed point's actual residue field is finite over the original base field. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Variety/Curve/RamificationAlgebraicClosure.lean:234-255"
  "adaptation" "lower extraction of closed-point residue finiteness with the native scalar map"]
theorem finite_residueField_overField_of_isClosed {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    letI := (fieldToResidue f x).hom.toAlgebra
    Module.Finite k (X.residueField x) := by
  let := (fieldToResidue f x).hom.toAlgebra
  have : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  have h : LocallyOfFiniteType (Spec.map (fieldToResidue f x)) := by
    rw [← Scheme.fromSpecResidueField_comp_eq_spec_fieldToResidue]
    infer_instance
  have : Algebra.FiniteType k (X.residueField x) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h
  exact finite_of_finite_type_of_isJacobsonRing _ _

/-- A finite field-valued point of a separated scheme has closed actual image. -/
theorem isClosed_image_of_finite_fieldPoint {k K : Type u} [Field k] [Field K]
    [Algebra k K] [Module.Finite k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsSeparated f] (a : Spec (.of K) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    IsClosed ({a (IsLocalRing.closedPoint K)} : Set X) := by
  have : IsFinite (a ≫ f) := by
    rw [ha]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : IsFinite a := IsFinite.of_comp a f
  have h := a.isClosedMap.isClosed_range
  convert h using 1
  ext x
  simp only [Set.mem_singleton_iff, Set.mem_range]
  exact ⟨fun h => ⟨_, h.symm⟩, fun ⟨t, ht⟩ => ht.symm.trans
    (congrArg a (Subsingleton.elim t (IsLocalRing.closedPoint K)))⟩

/-- A separable field-valued point has separable residue field for its actual scalar action. -/
theorem isSeparable_residueField_of_fieldPoint {k K : Type u} [Field k] [Field K]
    [Algebra k K] [Algebra.IsSeparable k K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (a : Spec (.of K) ⟶ X)
    (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))) :
    letI := (fieldToResidue f (a (IsLocalRing.closedPoint K))).hom.toAlgebra
    Algebra.IsSeparable k (X.residueField (a (IsLocalRing.closedPoint K))) := by
  let := (fieldToResidue f (a (IsLocalRing.closedPoint K))).hom.toAlgebra
  let φ := X.descResidueField (Scheme.stalkClosedPointTo a)
  have hφ : Spec.map φ ≫ X.fromSpecResidueField (a (IsLocalRing.closedPoint K)) = a :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X a
  have hh : fieldToResidue f (a (IsLocalRing.closedPoint K)) ≫ φ =
      CommRingCat.ofHom (algebraMap k K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← Scheme.fromSpecResidueField_comp_eq_spec_fieldToResidue,
      ← Category.assoc, hφ, ha]
  let ψ : X.residueField (a (IsLocalRing.closedPoint K)) →ₐ[k] K :=
    { φ.hom with
      commutes' := fun z => congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of K => h z) hh }
  exact Algebra.IsSeparable.of_algHom k K ψ

/-- In characteristic zero the actual closed residue extension is already finite separable. -/
theorem finite_separable_residueField_of_isClosed_of_charZero
    {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    letI := (fieldToResidue f x).hom.toAlgebra
    Module.Finite k (X.residueField x) ∧ Algebra.IsSeparable k (X.residueField x) := by
  let := (fieldToResidue f x).hom.toAlgebra
  have := finite_residueField_overField_of_isClosed f x hx
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
