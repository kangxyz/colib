/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Polynomial.ValueSection

/-! # The original rational chart mark satisfies the actual EtaleChart section equation

The construction reuses Polynomial.ValueSection unchanged. Neither the coordinates nor
finite covers are translated. An actual rational point must be produced first; an arbitrary
geometric point is not silently treated as rational over the stage field.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
variable {E R B : Type u} [CommRing E] [CommRing R] [CommRing B]
  [Algebra E R] [Algebra E B]
  (f : Polynomial R →ₐ[E] B) (ε : B →ₐ[E] E)

/-- The original rational coordinate mark has the required section equation. -/
theorem polynomialChart_rationalMark_section :
    Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
      Spec.map (CommRingCat.ofHom ((ε.comp f).toRingHom.comp Polynomial.C)) ≫
        polynomialValueSection R (algebraMap E R ((ε.comp f) Polynomial.X)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact polynomialPoint_factors_valueSection E R (ε.comp f)

/-- An unchanged geometric extension of that rational mark has the same section equation. -/
theorem polynomialChart_geometricMark_section
    {W : Scheme.{u}} (η : W ⟶ Spec (.of E)) :
    (η ≫ Spec.map (CommRingCat.ofHom ε.toRingHom)) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom) =
      (η ≫ Spec.map (CommRingCat.ofHom ((ε.comp f).toRingHom.comp Polynomial.C))) ≫
        polynomialValueSection R (algebraMap E R ((ε.comp f) Polynomial.X)) := by
  simp only [Category.assoc]
  rw [polynomialChart_rationalMark_section f ε]
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
open CategoryTheory
/-- A genuine rational scheme point is represented by a coefficient-linear ring map. -/
theorem exists_algHom_of_rational_schemePoint
    {E B : Type u} [CommRing E] [CommRing B] [Algebra E B]
    (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _) :
    ∃ ε : B →ₐ[E] E, Spec.map (CommRingCat.ofHom ε.toRingHom) = x := by
  obtain ⟨ε, rfl⟩ := Spec.map_surjective x
  have hε : CommRingCat.ofHom (algebraMap E B) ≫ ε = 𝟙 (CommRingCat.of E) := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, Spec.map_id] using hx
  let e : B →ₐ[E] E :=
    { ε.hom with
      commutes' := fun a => by
        have h := ConcreteCategory.congr_hom hε a
        simpa using h }
  exact ⟨e, rfl⟩

/-- The exact section data required by EtaleChart is constructed from the original
rational stage mark, without changing the original coordinate morphism. -/
theorem exists_polynomial_section_through_rational_schemePoint
    {E R B : Type u} [CommRing E] [CommRing R] [CommRing B]
    [Algebra E R] [Algebra E B]
    (f : Polynomial R →ₐ[E] B) (x : Spec (.of E) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) = 𝟙 _) :
    ∃ (s : Spec (.of R) ⟶ Spec (.of (Polynomial R)))
      (η : Spec (.of E) ⟶ Spec (.of R)),
      s ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) = 𝟙 _ ∧
      x ≫ Spec.map (CommRingCat.ofHom f.toRingHom) = η ≫ s := by
  obtain ⟨ε, hε⟩ := exists_algHom_of_rational_schemePoint x hx
  refine ⟨polynomialValueSection R (algebraMap E R ((ε.comp f) Polynomial.X)),
    Spec.map (CommRingCat.ofHom ((ε.comp f).toRingHom.comp Polynomial.C)),
    polynomialValueSection_projection _ _, ?_⟩
  rw [← hε]
  exact polynomialChart_rationalMark_section f ε
end AlgebraicGeometry.Scheme
