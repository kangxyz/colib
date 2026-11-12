/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Limits.SeparableRationalMarkedChart
public import Colib.AlgebraicGeometry.ResidueField.EtaleSeparable

/-! # Recover the actual polynomial coordinates of an affine étale neighborhood -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- Recover coordinates from the actual étale scheme map, not a newly selected chart. -/
theorem exists_etale_polynomial_coordinate
    (E B : Type u) [Field E] [CommRing B] (d : ℕ)
    (f : Spec (.of B) ⟶ Spec (.of (MvPolynomial (Fin d) E))) [Etale f] :
    ∃ (_a : Algebra E B),
      ∃ q : MvPolynomial (Fin d) E →ₐ[E] B,
        Algebra.Smooth E B ∧ q.toRingHom.Etale ∧ Spec.map (CommRingCat.ofHom q.toRingHom) = f ∧
        f ≫ Spec.map (CommRingCat.ofHom (algebraMap E (MvPolynomial (Fin d) E))) =
          Spec.map (CommRingCat.ofHom (algebraMap E B)) := by
  let q := (Scheme.Spec.preimage f).unop.hom
  have hq : Spec.map (CommRingCat.ofHom q) = f := Scheme.Spec.map_preimage f
  let a : Algebra E B := (q.comp (algebraMap E (MvPolynomial (Fin d) E))).toAlgebra
  let p : MvPolynomial (Fin d) E →ₐ[E] B :=
    { q with commutes' := fun _ => rfl }
  have he : q.Etale := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    change Etale (Spec.map (CommRingCat.ofHom q))
    rw [hq]
    infer_instance
  let : Algebra (MvPolynomial (Fin d) E) B := q.toAlgebra
  let : IsScalarTower E (MvPolynomial (Fin d) E) B :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.Etale (MvPolynomial (Fin d) E) B :=
    RingHom.etale_algebraMap.mp he
  refine ⟨a, p, Algebra.Smooth.comp E (MvPolynomial (Fin d) E) B, ?_, hq, ?_⟩
  · apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    change Etale (Spec.map (CommRingCat.ofHom q))
    rw [hq]
    infer_instance
  · rw [← hq, ← Spec.map_comp]
    rfl

/-- Native residue separability follows along the actual marked étale map. -/
theorem isSeparable_residueField_of_etale_mark
    {E Ω : Type u} [Field E] [Field Ω] {A X : Scheme.{u}}
    (f : X ⟶ Spec (.of E)) (g : A ⟶ X) [Etale g]
    (η : Spec (.of Ω) ⟶ A) (ξ : Spec (.of Ω) ⟶ X)
    (hmark : η ≫ g = ξ)
    (hs : letI := (fieldToResidue f (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable E (X.residueField (ξ (IsLocalRing.closedPoint Ω)))) :
    letI := (fieldToResidue (g ≫ f) (η (IsLocalRing.closedPoint Ω))).hom.toAlgebra
    Algebra.IsSeparable E (A.residueField (η (IsLocalRing.closedPoint Ω))) := by
  apply isSeparable_residueField_of_etale_over_field f g
  have hpoint : g (η (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω) :=
    congrArg (fun h : Spec (.of Ω) ⟶ X => h (IsLocalRing.closedPoint Ω)) hmark
  exact (congrArg (fun x : X =>
    letI := (fieldToResidue f x).hom.toAlgebra
    Algebra.IsSeparable E (X.residueField x)) hpoint).mpr hs

/-- All inputs for the integral rational chart producer come from this same
actual marked neighborhood, with its native coefficient residue action. -/
theorem exists_etale_polynomial_coordinate_separable_mark
    (E B Ω : Type u) [Field E] [CommRing B] [Field Ω] (d : ℕ)
    (f : Spec (.of B) ⟶ Spec (.of (MvPolynomial (Fin d) E))) [Etale f]
    (η : Spec (.of Ω) ⟶ Spec (.of B))
    (ξ : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin d) E))) (hmark : η ≫ f = ξ)
    (hs : letI := (fieldToResidue
      (Spec.map (CommRingCat.ofHom (algebraMap E (MvPolynomial (Fin d) E))))
      (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable E
        ((Spec (.of (MvPolynomial (Fin d) E))).residueField
          (ξ (IsLocalRing.closedPoint Ω)))) :
    ∃ (_a : Algebra E B),
      ∃ q : MvPolynomial (Fin d) E →ₐ[E] B,
        Algebra.Smooth E B ∧ q.toRingHom.Etale ∧
        Spec.map (CommRingCat.ofHom q.toRingHom) = f ∧
        (letI := (fieldToResidue (Spec.map (CommRingCat.ofHom (algebraMap E B)))
          (η (IsLocalRing.closedPoint Ω))).hom.toAlgebra
        Algebra.IsSeparable E ((Spec (.of B)).residueField
          (η (IsLocalRing.closedPoint Ω)))) := by
  obtain ⟨a, q, hsm, hq, hspec, hbase⟩ := exists_etale_polynomial_coordinate E B d f
  let := a
  refine ⟨a, q, hsm, hq, hspec, ?_⟩
  have hsep := isSeparable_residueField_of_etale_mark
    (Spec.map (CommRingCat.ofHom (algebraMap E (MvPolynomial (Fin d) E))))
    f η ξ hmark hs
  exact (congrArg (fun h : Spec (.of B) ⟶ Spec (.of E) =>
    letI := (fieldToResidue h (η (IsLocalRing.closedPoint Ω))).hom.toAlgebra
    Algebra.IsSeparable E ((Spec (.of B)).residueField
      (η (IsLocalRing.closedPoint Ω)))) hbase).mp hsep
end AlgebraicGeometry.Scheme
