/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ResidueField.FieldPoint
public import Mathlib.FieldTheory.IsSepClosed

/-!
# A separable intermediate field retaining the original scheme marking

For a marking in an arbitrary separably closed field Omega, take the separable closure of
its actual residue field inside Omega. The inclusion and the original residue-point map
factor the original scheme morphism. Separability over the original base follows from
separability of its actual residue scalar map. Omega need not be algebraic over the base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme

/-- An original marking with separable residue factors through a separably closed separable
extension of the original base, without assuming the marking field algebraic over it. -/
theorem exists_separable_residue_marking
    {k Ω : Type u} [Field k] [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (ξ : Spec (.of Ω) ⟶ X)
    (hs : letI := (fieldToResidue f (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable k (X.residueField (ξ (IsLocalRing.closedPoint Ω)))) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
      IsSepClosed L ∧ Infinite L ∧ Algebra.IsSeparable k L ∧
      ∃ (e : L →+* Ω) (x : Spec (.of L) ⟶ X),
        x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) ∧
        Spec.map (CommRingCat.ofHom e) ≫ x = ξ := by
  let κ := X.residueField (ξ (IsLocalRing.closedPoint Ω))
  let ρ : κ →+* Ω := (descResidueField (stalkClosedPointTo ξ)).hom
  let : Algebra κ Ω := ρ.toAlgebra
  let L := separableClosure κ Ω
  let : Algebra k κ := (fieldToResidue f (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
  let : Algebra k L :=
    ((algebraMap κ L).comp (fieldToResidue f (ξ (IsLocalRing.closedPoint Ω))).hom).toAlgebra
  let : IsScalarTower k κ L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsSeparable k κ := hs
  have hL : IsSepClosed L := (inferInstance : IsSepClosure κ L).sep_closed
  have hInf : Infinite L := by
    let : IsSepClosed L := hL
    apply Infinite.of_not_fintype
    intro hfinite
    let : Fintype L := hfinite
    let : IsAlgClosed L := inferInstance
    exact Finite.false (inferInstance : Finite L)
  have hsep : Algebra.IsSeparable k L := Algebra.IsSeparable.trans k κ L
  let e : L →+* Ω := (separableClosure κ Ω).val.toRingHom
  let x : Spec (.of L) ⟶ X := Spec.map (CommRingCat.ofHom (algebraMap κ L)) ≫
    X.fromSpecResidueField (ξ (IsLocalRing.closedPoint Ω))
  refine ⟨L, inferInstance, inferInstance, hL, hInf, hsep, e, x, ?_, ?_⟩
  · change (Spec.map (CommRingCat.ofHom (algebraMap κ L)) ≫ _) ≫ f = _
    rw [Category.assoc, fromSpecResidueField_comp_eq_spec_fieldToResidue, ← Spec.map_comp]
    rfl
  · change Spec.map (CommRingCat.ofHom e) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap κ L)) ≫ _) = ξ
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have he : e.comp (algebraMap κ L) = ρ :=
      (separableClosure κ Ω).val.comp_algebraMap
    rw [he]
    exact descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X ξ

end AlgebraicGeometry.Scheme
