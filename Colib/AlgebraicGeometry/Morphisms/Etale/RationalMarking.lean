/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Rational descent of actual étale markings

Over a separably closed field, an étale residue extension is separable and the actual residue
map is bijective. Its inverse gives a rational section preserving an arbitrary field-valued
marking. Applying this to the actual fiber over a rational point descends the original marking
through any étale morphism. Algebraic and separable closures are never identified.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The actual residue map over a field is separable for an étale scheme. -/
theorem Hom.residueFieldMapFromField_isSeparable
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Etale f] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Spec.residueFieldIsoOfField (f x)).inv ≫ f.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable k (X.residueField x) := by
  let : Algebra k (X.residueField x) :=
    ((Spec.residueFieldIsoOfField (f x)).inv ≫ f.residueFieldMap x).hom.toAlgebra
  let : Algebra ((AlgebraicGeometry.Spec (.of k)).residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let e := (Spec.residueFieldIsoOfField (f x)).commRingCatIsoToRingEquiv
  exact Algebra.IsSeparable.of_equiv_equiv e (RingEquiv.refl _) (by
      ext a
      change (f.residueFieldMap x).hom ((Spec.residueFieldIsoOfField (f x)).inv.hom
        ((Spec.residueFieldIsoOfField (f x)).hom.hom a)) = (f.residueFieldMap x).hom a
      congr 1
      exact ConcreteCategory.congr_hom (Spec.residueFieldIsoOfField (f x)).hom_inv_id a)

/-- Over a separably closed base field, the actual étale residue map is bijective. -/
theorem Hom.residueFieldMapFromField_bijective
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Etale f] (x : X) :
    Function.Bijective (((Spec.residueFieldIsoOfField (f x)).inv ≫
      f.residueFieldMap x).hom) := by
  let : Algebra k (X.residueField x) :=
    ((Spec.residueFieldIsoOfField (f x)).inv ≫ f.residueFieldMap x).hom.toAlgebra
  have := f.residueFieldMapFromField_isSeparable x
  exact IsSepClosed.algebraMap_bijective k (X.residueField x)

/-- The same actual residue extension is finite, with no algebraic-closure identification. -/
theorem Hom.residueFieldMapFromField_finite
    {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Etale f] (x : X) :
    letI : Algebra k (X.residueField x) :=
      ((Spec.residueFieldIsoOfField (f x)).inv ≫ f.residueFieldMap x).hom.toAlgebra
    Module.Finite k (X.residueField x) := by
  let : Algebra k (X.residueField x) :=
    ((Spec.residueFieldIsoOfField (f x)).inv ≫ f.residueFieldMap x).hom.toAlgebra
  exact Module.Finite.of_surjective (Algebra.linearMap k (X.residueField x))
    (f.residueFieldMapFromField_bijective x).surjective

/-- The native field residue isomorphism gives the actual canonical residue-point map. -/
@[reassoc]
theorem Spec.map_residueFieldIsoOfField_inv {k : Type u} [Field k] (x : Spec (.of k)) :
    Spec.map (Scheme.Spec.residueFieldIsoOfField x).inv =
      (Spec (.of k)).fromSpecResidueField x := by
  rw [Scheme.Spec.residueFieldIsoOfField_inv, Scheme.Spec.Γevaluation_eq_of_field,
    Iso.inv_hom_id_assoc, Spec.map_comp]
  exact Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField _ _

/-- The spectrum of the actual residue map is the original point's structure morphism. -/
@[reassoc]
theorem Hom.SpecMap_residueFieldMapFromField {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    Spec.map ((Scheme.Spec.residueFieldIsoOfField (f x)).inv ≫ f.residueFieldMap x) =
      X.fromSpecResidueField x ≫ f := by
  rw [Spec.map_comp, Spec.map_residueFieldIsoOfField_inv]
  exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x

/-- A field-valued marking of an étale scheme over a separably closed field descends to an
actual rational section, with its original marking as a scheme-morphism equality. -/
theorem exists_rational_section_of_etale_marking
    {k Ω : Type u} [Field k] [IsSepClosed k] [Field Ω] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [Etale f] (ξ : Spec (.of Ω) ⟶ X) :
    ∃ l : Spec (.of k) ⟶ X, l ≫ f = 𝟙 _ ∧ (ξ ≫ f) ≫ l = ξ := by
  let x := ξ (IsLocalRing.closedPoint Ω)
  let m := (Scheme.Spec.residueFieldIsoOfField (f x)).inv ≫ f.residueFieldMap x
  have : IsIso m :=
    (ConcreteCategory.isIso_iff_bijective m).mpr (Hom.residueFieldMapFromField_bijective f x)
  let i := asIso m
  let l := Spec.map i.inv ≫ X.fromSpecResidueField x
  have hl : l ≫ f = 𝟙 _ := by
    change (Spec.map i.inv ≫ X.fromSpecResidueField x) ≫ f = 𝟙 _
    rw [Category.assoc, ← Hom.SpecMap_residueFieldMapFromField f x]
    change Spec.map i.inv ≫ Spec.map i.hom = 𝟙 _
    rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
  refine ⟨l, hl, ?_⟩
  let a := X.descResidueField (Scheme.stalkClosedPointTo ξ)
  have ha : Spec.map a ≫ X.fromSpecResidueField x = ξ :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X ξ
  calc
    (ξ ≫ f) ≫ l = ((Spec.map a ≫ X.fromSpecResidueField x) ≫ f) ≫ l :=
      congrArg (fun q ↦ (q ≫ f) ≫ l) ha.symm
    _ = (Spec.map a ≫ (X.fromSpecResidueField x ≫ f)) ≫ l := by
      simp only [Category.assoc]
    _ = (Spec.map a ≫ Spec.map i.hom) ≫ l :=
      congrArg (fun q ↦ (Spec.map a ≫ q) ≫ l) (Hom.SpecMap_residueFieldMapFromField f x).symm
    _ = Spec.map a ≫ X.fromSpecResidueField x := by
      change (Spec.map a ≫ Spec.map i.hom) ≫
        (Spec.map i.inv ≫ X.fromSpecResidueField x) = _
      rw [Category.assoc, ← Category.assoc (Spec.map i.hom),
        ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]
    _ = ξ := ha

open CategoryTheory.Limits in
/-- A marked lift through an étale map above a rational point descends to that same rational
point, preserving the entire field-valued scheme morphism rather than only its image point. -/
theorem exists_rational_lift_of_etale_marking
    {k Ω : Type u} [Field k] [IsSepClosed k] [Field Ω]
    {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
    (x : Spec (.of k) ⟶ X) (c : Spec (.of Ω) ⟶ Spec (.of k))
    (ξ : Spec (.of Ω) ⟶ U) (hξ : ξ ≫ f = c ≫ x) :
    ∃ l : Spec (.of k) ⟶ U, l ≫ f = x ∧ c ≫ l = ξ := by
  let z : Spec (.of Ω) ⟶ pullback f x := pullback.lift ξ c hξ
  obtain ⟨r, hr, hm⟩ := exists_rational_section_of_etale_marking (pullback.snd f x) z
  refine ⟨r ≫ pullback.fst f x, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hr, Category.id_comp]
  · calc
      c ≫ (r ≫ pullback.fst f x) =
          (z ≫ pullback.snd f x) ≫ (r ≫ pullback.fst f x) := by
        rw [show z ≫ pullback.snd f x = c from pullback.lift_snd ξ c hξ]
      _ = ((z ≫ pullback.snd f x) ≫ r) ≫ pullback.fst f x := (Category.assoc _ _ _).symm
      _ = z ≫ pullback.fst f x := congrArg (fun q ↦ q ≫ pullback.fst f x) hm
      _ = ξ := pullback.lift_fst ξ c hξ

end AlgebraicGeometry.Scheme
