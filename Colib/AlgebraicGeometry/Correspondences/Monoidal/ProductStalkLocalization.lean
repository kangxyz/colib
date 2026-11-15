/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CartesianSquareStalkLocalization
public import Mathlib.RingTheory.Flat.Localization

/-!
# The localization map of a product stalk over a field

The Stacks presentation of a product stalk as a localization uses the
stalk of the base. Over a field that stalk is canonically the field, and
the localization map retains both original projection maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CommRingCat
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.BaseChangeStalk

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The field acts on a stalk through the actual structure map to its spectrum. -/
abbrev stalkAlgebraOfField (f : X ⟶ Spec (.of k)) (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  ((f.stalkMap x).hom.comp (StructureSheaf.toStalk k (f x)).hom).toAlgebra

private theorem stalkCongr_comp_toStalk_field {x y : (Spec (.of k) : Scheme.{u})}
    (h : x = y) :
    StructureSheaf.toStalk k y ≫
        eqToHom (congrArg (Spec (.of k)).presheaf.stalk h.symm) =
      StructureSheaf.toStalk k x := by
  subst y
  simp only [eqToHom_refl, Category.comp_id]

/-- A product stalk admits its actual tensor-to-stalk map over the field, which is a localization.
Both restrictions are the actual stalk maps of the product projections. -/
theorem pullback_stalk_isLocalization_overField {Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (t : pullback (C := Scheme) f g) :
    let x := pullback.fst f g t
    let y := pullback.snd f g t
    letI := stalkAlgebraOfField f x
    letI := stalkAlgebraOfField g y
    ∃ φ : (X.presheaf.stalk x) ⊗[k] (Y.presheaf.stalk y) →+*
        (pullback f g).presheaf.stalk t,
      φ.comp Algebra.TensorProduct.includeLeftRingHom = ((pullback.fst f g).stalkMap t).hom ∧
      φ.comp Algebra.TensorProduct.includeRight.toRingHom = ((pullback.snd f g).stalkMap t).hom ∧
      letI := φ.toAlgebra
      ∃ M : Submonoid ((X.presheaf.stalk x) ⊗[k] (Y.presheaf.stalk y)),
        IsLocalization M ((pullback f g).presheaf.stalk t) := by
  intro x y
  let S := Spec (.of k)
  let h : (pullback.fst f g ≫ f).base t = (pullback.snd f g ≫ g).base t :=
    congrArg (fun m : pullback f g ⟶ S => m.base t) pullback.condition
  let R := S.presheaf.stalk (f x)
  let A := X.presheaf.stalk x
  let B := Y.presheaf.stalk y
  let C := (pullback f g).presheaf.stalk t
  let : Algebra k A := stalkAlgebraOfField f x
  let : Algebra k B := stalkAlgebraOfField g y
  let : Algebra k R := StructureSheaf.stalkAlgebra k (f x)
  let : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let : Algebra R B := ((eqToHom (congrArg S.presheaf.stalk h)) ≫ g.stalkMap y).hom.toAlgebra
  let : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq' (by
    have heq : StructureSheaf.toStalk k (f x) ≫
        eqToHom (congrArg S.presheaf.stalk h) = StructureSheaf.toStalk k (g y) :=
      stalkCongr_comp_toStalk_field h.symm
    exact congrArg CommRingCat.Hom.hom (by
      change StructureSheaf.toStalk k (g y) ≫ g.stalkMap y =
        StructureSheaf.toStalk k (f x) ≫ eqToHom (congrArg S.presheaf.stalk h) ≫ g.stalkMap y
      rw [← Category.assoc, heq]))
  have hsurj : Function.Surjective (algebraMap k R) := by
    let p : PrimeSpectrum k := f x
    have : IsLocalization.AtPrime R p.asIdeal :=
      inferInstanceAs (IsLocalization.AtPrime ((Spec.structureSheaf k).presheaf.stalk p) p.asIdeal)
    exact (Field.localization_map_bijective (Kₘ := R) (M := p.asIdeal.primeCompl)
      (by simp)).surjective
  let : TensorProduct.CompatibleSMul k R A B :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective A B hsurj
  let e : A ⊗[k] B ≃+* A ⊗[R] B :=
    (Algebra.TensorProduct.equivOfCompatibleSMul k R R A B).symm.toRingEquiv
  have he₁ : e.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) :=
    RingHom.ext fun _ => rfl
  have he₂ : e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom =
      (Algebra.TensorProduct.includeRight.toRingHom : B →+* A ⊗[R] B) :=
    RingHom.ext fun _ => rfl
  obtain ⟨φ, hφ₁, hφ₂, M, hM⟩ := pullback_stalk_isLocalization f g t
  change (A ⊗[R] B) →+* C at φ
  change Submonoid (A ⊗[R] B) at M
  refine ⟨φ.comp e.toRingHom, ?_, ?_, exists_isLocalization_of_source_ringEquiv e φ M hM⟩
  · rw [RingHom.comp_assoc, he₁]
    exact hφ₁
  · rw [RingHom.comp_assoc, he₂]
    exact hφ₂

end AlgebraicGeometry.BaseChangeStalk
